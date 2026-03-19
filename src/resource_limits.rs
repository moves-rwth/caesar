//! Execute something, but with a timeout and a memory limit.

use std::{
    future::{pending, Future},
    sync::{Arc, Mutex},
    thread,
    time::{Duration, Instant},
};

use crossbeam_channel::{bounded, Receiver, Sender};
use crossbeam_utils::atomic::AtomicCell;
use memory_stats::memory_stats;
use thiserror::Error;
use tokio::time::{error::Elapsed, interval, timeout, MissedTickBehavior};
use tracing::error;

/// A memory size in bytes, with constructors to handle units.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct MemorySize(usize);

impl MemorySize {
    pub fn bytes(bytes: usize) -> Self {
        MemorySize(bytes)
    }

    pub fn megabytes(mb: usize) -> Self {
        MemorySize(mb * 1024 * 1024)
    }

    pub fn as_megabytes(&self) -> usize {
        self.0 / 1024 / 1024
    }
}

const CHECK_MEM_USAGE_INTERVAL: Duration = Duration::from_millis(20);
pub const HARD_TIMEOUT_SLACK: Duration = Duration::from_millis(500);

/// A timeout or an out-of-memory condition.
#[derive(Debug, Clone, Copy, Error, PartialEq, Eq)]
#[repr(u8)]
pub enum LimitError {
    #[error("timeout")]
    Timeout,
    #[error("out of memory")]
    Oom,
    #[error("interrupted")]
    Interrupted,
}

/// Run `fut` with timeout and memory monitoring.
///
/// `fut` gets a [`LimitsRef`] and is expected to check it periodically.
/// If it does not stop in time, the outer hard timeout returns
/// [`LimitError::Timeout`].
pub async fn await_with_resource_limits<T, F>(
    limits_ref: LimitsRef,
    fut: impl FnOnce(LimitsRef) -> F,
) -> Result<T, LimitError>
where
    T: Unpin,
    F: Future<Output = T>,
{
    limits_ref.check_limits()?;
    let fut = fut(limits_ref.clone());
    let res = match limits_ref.time_left() {
        Some(duration) => {
            let hard_duration = duration + HARD_TIMEOUT_SLACK;
            with_memory_limit(limits_ref.memory_limit(), async {
                timeout(hard_duration, fut)
                    .await
                    .map_err(|_: Elapsed| LimitError::Timeout)
            })
            .await
        }
        None => with_memory_limit(limits_ref.memory_limit(), async { Ok(fut.await) }).await,
    };
    if let Err(err) = res {
        limits_ref.set_error(err);
    }
    res
}

async fn with_memory_limit<T>(
    mem_limit: Option<MemorySize>,
    fut: impl Future<Output = Result<T, LimitError>>,
) -> Result<T, LimitError> {
    match mem_limit {
        Some(mem_limit) => {
            tokio::select! {
                _ = wait_for_oom(mem_limit) => Err(LimitError::Oom),
                res = fut => res,
            }
        }
        None => fut.await,
    }
}

async fn wait_for_oom(mem_limit: MemorySize) {
    let mut interval = interval(CHECK_MEM_USAGE_INTERVAL);
    interval.set_missed_tick_behavior(MissedTickBehavior::Skip);
    loop {
        interval.tick().await;
        let memory_stats_res = memory_stats();
        match memory_stats_res {
            Some(memory_stats) => {
                let current_usage = MemorySize::bytes(memory_stats.physical_mem);
                if current_usage > mem_limit {
                    return;
                }
            }
            None => {
                // We have observed that the call `ProcessStats::get()` fails on
                // x86 Linux-based Docker images running virtualized in an ARM
                // environment on Apple M1 chips. This seems to be due to
                // `procfs` failing to parse `/proc/self/stat` for some reason.
                // Since we have not been able to track down this bug after
                // several hours, we just disable memory limit checking in such
                // cases. This seems acceptable since it's a very specific set
                // of circumstances and likely a bug in QEMU that is going to be
                // fixed.
                error!("Could not fetch process stats to check memory limit. Memory limit checking is disabled. This error may occur in virtual machines. For memory limit checking, please consider using a native environment.");
                pending().await // do not terminate this function
            }
        }
    }
}

/// Shared view of the current resource limits.
#[derive(Debug, Clone)]
pub struct LimitsRef(Arc<LimitsRefData>);

#[derive(Debug)]
struct LimitsRefData {
    state: AtomicCell<Result<(), LimitError>>,
    subscribers: Mutex<Vec<Sender<LimitError>>>,
    timeout: Option<Instant>,
    memory: Option<MemorySize>,
}

const _: () = assert!(AtomicCell::<Result<(), LimitError>>::is_lock_free());

impl LimitsRefData {
    fn error(&self) -> Option<LimitError> {
        self.state.load().err()
    }

    fn subscribe(&self) -> (Sender<LimitError>, Receiver<LimitError>) {
        let (sender, receiver) = bounded(1);
        let mut subscribers = self.subscribers.lock().unwrap();
        if let Some(err) = self.error() {
            let _ = sender.send(err);
        } else {
            subscribers.push(sender.clone());
        }
        (sender, receiver)
    }

    fn unsubscribe(&self, sender: &Sender<LimitError>) {
        let mut subscribers = self.subscribers.lock().unwrap();
        subscribers.retain(|entry| !entry.same_channel(sender));
    }

    fn set_error(&self, err: LimitError) -> LimitError {
        let prev = self.state.compare_exchange(Ok(()), Err(err));
        if prev.is_ok() {
            let mut subscribers = self.subscribers.lock().unwrap();
            // sending and cleanup
            subscribers.retain(|sender| sender.send(err).is_ok());
            err
        } else {
            self.error().unwrap()
        }
    }

    #[cfg(test)]
    fn subscriber_count(&self) -> usize {
        self.subscribers.lock().unwrap().len()
    }
}

impl LimitsRef {
    pub fn new(timeout: Option<Instant>, memory: Option<MemorySize>) -> Self {
        LimitsRef(Arc::new(LimitsRefData {
            state: AtomicCell::new(Ok(())),
            subscribers: Mutex::new(Vec::new()),
            timeout,
            memory,
        }))
    }

    /// Check whether work should stop.
    pub fn check_limits(&self) -> Result<(), LimitError> {
        // The hard-timeout path records `Timeout` in the stop token.
        if let Some(err) = self.0.error() {
            return Err(err);
        }
        if let Some(timeout) = self.0.timeout {
            if Instant::now() >= timeout {
                return Err(self.0.set_error(LimitError::Timeout));
            }
        }
        Ok(())
    }

    /// Return the stop reason, defaulting to `Interrupted`.
    pub fn interrupted_error(&self) -> LimitError {
        self.check_limits().err().unwrap_or(LimitError::Interrupted)
    }

    /// Cancel the current work explicitly.
    pub fn cancel(&self) {
        self.set_error(LimitError::Interrupted);
    }

    /// Subscribe to published stop events.
    #[cfg(test)]
    pub fn subscribe_to_stop(&self) -> Receiver<LimitError> {
        let (_, receiver) = self.0.subscribe();
        receiver
    }

    /// Spawn a scoped watcher that runs `on_stop` unless the returned sender
    /// is notified first.
    pub fn spawn_until_stopped_or_done<'scope, 'env>(
        &'scope self,
        scope: &'scope thread::Scope<'scope, 'env>,
        on_stop: impl FnOnce() + Send + 'scope,
    ) -> Sender<()> {
        let (done_sender, done_receiver) = bounded(1);
        let (stop_sender, stop_receiver) = self.0.subscribe();
        scope.spawn(move || {
            if self.check_limits().is_err() {
                self.0.unsubscribe(&stop_sender);
                on_stop();
                return;
            }

            crossbeam_channel::select! {
                recv(done_receiver) -> _ => {
                    self.0.unsubscribe(&stop_sender);
                }
                recv(stop_receiver) -> _ => {
                    self.0.unsubscribe(&stop_sender);
                    if self.check_limits().is_err() {
                        on_stop();
                    }
                }
            }
        });
        done_sender
    }

    /// Return the remaining timeout, or `None` if there is none.
    pub fn time_left(&self) -> Option<Duration> {
        let timeout = self.0.timeout?;
        Some(
            timeout
                .checked_duration_since(Instant::now())
                .unwrap_or_default(),
        )
    }

    /// Return the configured memory limit.
    pub fn memory_limit(&self) -> Option<MemorySize> {
        self.0.memory
    }

    /// Sets an error. Will only store the first error, any subsequent errors
    /// are discarded.
    fn set_error(&self, err: LimitError) {
        let _ = self.0.set_error(err);
    }
}

#[cfg(test)]
mod tests {
    use std::{
        sync::{Arc, Barrier, Mutex},
        thread,
    };

    use super::{LimitError, LimitsRef};

    #[test]
    fn cancel_notifies_subscribers() {
        let limits_ref = LimitsRef::new(None, None);
        let barrier = Arc::new(Barrier::new(2));
        let stop_receiver = limits_ref.subscribe_to_stop();

        thread::scope(|scope| {
            let spawned_barrier = barrier.clone();
            scope.spawn(move || {
                spawned_barrier.wait();
                stop_receiver.recv().unwrap()
            });

            barrier.wait();
            limits_ref.cancel();
        });

        assert_eq!(limits_ref.check_limits(), Err(LimitError::Interrupted));
    }

    #[test]
    fn done_does_not_trigger_stop_handler() {
        let limits_ref = LimitsRef::new(None, None);
        let stopped = Arc::new(Mutex::new(false));

        thread::scope(|scope| {
            let stopped = stopped.clone();
            let done_sender = limits_ref.spawn_until_stopped_or_done(scope, move || {
                *stopped.lock().unwrap() = true;
            });
            let _ = done_sender.send(());
        });

        assert!(!*stopped.lock().unwrap());
        assert_eq!(limits_ref.0.subscriber_count(), 0);
    }
}

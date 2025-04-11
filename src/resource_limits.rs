//! Execute something, but with a timeout and a memory limit.

use std::{
    future::{pending, Future},
    sync::{
        atomic::{AtomicU8, Ordering},
        Arc,
    },
    time::{Duration, Instant},
};

use simple_process_stats::ProcessStats;
use thiserror::Error;
use tokio::{
    select,
    time::{error::Elapsed, interval, timeout, MissedTickBehavior},
};
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

    pub fn as_bytes(&self) -> usize {
        self.0
    }

    pub fn as_megabytes(&self) -> usize {
        self.0 / 1024 / 1024
    }
}

const CHECK_MEM_USAGE_INTERVAL: Duration = Duration::from_millis(20);
pub const HARD_TIMEOUT_SLACK: Duration = Duration::from_millis(500);

/// A timeout or an out-of-memory condition.
#[derive(Debug, Clone, Copy, Error)]
pub enum LimitError {
    #[error("timeout")]
    Timeout,
    #[error("out of memory")]
    Oom,
}

/// Wait for the future  returned by `fut`. Returns [`LimitError::Timeout`] if
/// the future took too long to complete. If the memory limit was exceeded,
/// return [`LimitError::Oom`]. Otherwise, return the result wrapped in
/// [`Result::Ok`].
///
/// The `fut` is given a [`LimitsRef`] which it is supposed to check
/// periodically. After the given duration plus [`HARD_TIMEOUT_SLACK`], the
/// future will return a [`LimitError::Timeout`] in case `fut` did not catch the
/// timeout itself.
///
/// Note that the memory limit is checked for the whole process by a background
/// thread. Therefore, the memory limit is not specific to the given future.
pub async fn await_with_resource_limits<T, F>(
    duration: Option<Duration>,
    mem_limit: Option<MemorySize>,
    fut: impl FnOnce(LimitsRef) -> F,
) -> Result<T, LimitError>
where
    T: Unpin,
    F: Future<Output = T>,
{
    if let Some(duration) = duration {
        let limits_ref = LimitsRef::new(Some(Instant::now() + duration), mem_limit);

        let hard_duration = duration + HARD_TIMEOUT_SLACK;
        let fut = timeout(hard_duration, fut(limits_ref.clone()));
        let res = if let Some(mem_mbs) = mem_limit {
            select! {
                _ = wait_for_oom(mem_mbs) => {
                    Err(LimitError::Oom)
                }
                res = fut => {
                    res.map_err(|_: Elapsed| LimitError::Timeout)
                }
            }
        } else {
            fut.await.map_err(|_: Elapsed| LimitError::Timeout)
        };
        if let Err(err) = res {
            limits_ref.set_error(err);
        }
        res
    } else if let Some(mem_mbs) = mem_limit {
        let limits_ref = LimitsRef::new(None, mem_limit);
        select! {
            _ = wait_for_oom(mem_mbs) => {
                limits_ref.set_error(LimitError::Oom);
                Err(LimitError::Oom)
            }
            res = fut(limits_ref.clone()) => {
                Ok(res)
            }
        }
    } else {
        let limits_ref = LimitsRef::new(None, mem_limit);
        Ok(fut(limits_ref).await)
    }
}

async fn wait_for_oom(mem_limit: MemorySize) {
    let mut interval = interval(CHECK_MEM_USAGE_INTERVAL);
    interval.set_missed_tick_behavior(MissedTickBehavior::Skip);
    loop {
        interval.tick().await;
        let process_stats_res = ProcessStats::get().await;
        match process_stats_res {
            Ok(process_stats) => {
                let current_usage = MemorySize::bytes(process_stats.memory_usage_bytes as usize);
                if current_usage > mem_limit {
                    return;
                }
            }
            Err(err) => {
                // We have observed that the call `ProcessStats::get()` fails on
                // x86 Linux-based Docker images running virtualized in an ARM
                // environment on Apple M1 chips. This seems to be due to
                // `procfs` failing to parse `/proc/self/stat` for some reason.
                // Since we have not been able to track down this bug after
                // several hours, we just disable memory limit checking in such
                // cases. This seems acceptable since it's a very specific set
                // of circumstances and likely a bug in QEMU that is going to be
                // fixed.
                error!(err=%err, "Could not fetch process stats to check memory limit. Memory limit checking is disabled. This error may occur in virtual machines. For memory limit checking, please consider using a native environment.");
                pending().await // do not terminate this function
            }
        }
    }
}

/// An object to pass around that allows to check whether the resource limits
/// were exceeded and the task needs to be stopped as a consequence.
#[derive(Debug, Clone)]
pub struct LimitsRef(Arc<LimitsRefData>);

#[derive(Debug)]
struct LimitsRefData {
    done: AtomicU8,
    timeout: Option<Instant>,
    memory: Option<MemorySize>,
}

impl LimitsRef {
    pub fn new(timeout: Option<Instant>, memory: Option<MemorySize>) -> Self {
        LimitsRef(Arc::new(LimitsRefData {
            done: AtomicU8::new(0),
            timeout,
            memory,
        }))
    }

    /// Check whether the monitoring thread has indicated a timeout or an OOM.
    pub fn check_limits(&self) -> Result<(), LimitError> {
        // Timeout flag is set to 1 by `await_with_resource_limits`, only if the hard timeout is reached.
        match self.0.done.load(Ordering::Relaxed) {
            0 => {
                // Normal timeout might be reached even though the hard timeout is not reached yet.
                // Check for timeout by checking the remaining time
                if let Some(timeout) = self.0.timeout {
                    if Instant::now() >= timeout {
                        self.set_error(LimitError::Timeout);
                        return Err(LimitError::Timeout);
                    }
                }
                Ok(())
            }
            1 => Err(LimitError::Timeout),
            2 => Err(LimitError::Oom),
            _ => unreachable!(),
        }
    }

    /// Returns the time left or `None` if there was no timeout. Will return
    /// zero if the timeout has elapsed.
    pub fn time_left(&self) -> Option<Duration> {
        Some(self.0.timeout?.duration_since(Instant::now()))
    }

    /// Returns the stored memory limit.
    pub fn memory_limit(&self) -> Option<MemorySize> {
        self.0.memory
    }

    /// Sets an error. Will only store the first error, any subsequent errors
    /// are discarded.
    fn set_error(&self, err: LimitError) {
        let new = match err {
            LimitError::Timeout => 1,
            LimitError::Oom => 2,
        };
        let _ = self
            .0
            .done
            .compare_exchange(0, new, Ordering::Acquire, Ordering::Relaxed);
    }
}

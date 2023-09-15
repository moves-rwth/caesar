//! Execute something, but with a timeout and a memory limit.

use std::{
    future::{pending, Future},
    time::Duration,
};

use simple_process_stats::ProcessStats;
use thiserror::Error;
use tokio::{
    select,
    time::{interval, timeout, MissedTickBehavior},
};
use tracing::error;

const CHECK_MEM_USAGE_INTERVAL: Duration = Duration::from_millis(20);

/// A timeout or an out-of-memory condition.
#[derive(Debug, Clone, Copy, Error)]
pub enum LimitError {
    #[error("timeout")]
    Timeout,
    #[error("out of memory")]
    Oom,
}

/// Wait for the given future `fut`. Returns [`LimitError::Timeout`] if the
/// future took too long to complete. If the memory limit was exceeded, return
/// [`LimitError::Oom`]. Otherwise, return the result wrapped in [`Result::Ok`].
///
/// Note that the memory limit is checked for the whole process by a background
/// thread. Therefore, the memory limit is not specific to the given future.
pub async fn await_with_resource_limits<T: Unpin>(
    timeout_secs: Option<u64>,
    mem_limit_mb: Option<u64>,
    fut: impl Future<Output = T>,
) -> Result<T, LimitError> {
    if let Some(timeout_secs) = timeout_secs {
        let fut = timeout(Duration::from_secs(timeout_secs), fut);
        if let Some(mem_mbs) = mem_limit_mb {
            select! {
                _ = wait_for_oom(mem_mbs) => {
                    Err(LimitError::Oom)
                }
                res = fut => {
                    res.map_err(|_| LimitError::Timeout)
                }
            }
        } else {
            fut.await.map_err(|_| LimitError::Timeout)
        }
    } else if let Some(mem_mbs) = mem_limit_mb {
        select! {
            _ = wait_for_oom(mem_mbs) => {
                Err(LimitError::Oom)
            }
            res = fut => {
                Ok(res)
            }
        }
    } else {
        Ok(fut.await)
    }
}

async fn wait_for_oom(mem_limit_mb: u64) {
    let mut interval = interval(CHECK_MEM_USAGE_INTERVAL);
    interval.set_missed_tick_behavior(MissedTickBehavior::Skip);
    loop {
        interval.tick().await;
        let process_stats_res = ProcessStats::get().await;
        match process_stats_res {
            Ok(process_stats) => {
                let current_usage_mb = process_stats.memory_usage_bytes / 1024 / 1024;
                if current_usage_mb > mem_limit_mb {
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

//! Tracing-based timing with the usual usual tracing output.
//!
//! [`DispatchBuilder`] is used to construct a stack of tracing `Layer`s. At the
//! top is an [`EnvFilter`] layer that filters events using the `RUST_LOG`
//! environment variable. For example, `RUST_LOG="trace,z3=error" cargo test`
//! will run tests with events and spans on trace level, but filtering spam from
//! the `z3` crate. More information can be found in the [`EnvFilter`] documentation.
//!
//! A logging layer is supported in tests and to standard output.
//!
//! Finally, the [`TimingLayer`] can be enabled in the [`DispatchBuilder`]. The
//! [`TimingLayer`] measures active times of spans emitted by [`tracing`] and
//! tracks data from spans by name in histograms. Measurements can be retrieved
//! via [`TimingLayer::view_active()`].
//!
//! The default tracing setup for glacier and its tests is done by [`init_tracing`].
//!
//! [`tracing`]: https://github.com/tokio-rs/tracing
//! [`TimingLayer`]: struct.TimingLayer.html
//! [`DispatchBuilder`]: struct.DispatchBuilder.html
//! [`EnvFilter`]: https://docs.rs/tracing-subscriber/0.2.12/tracing_subscriber/filter/struct.EnvFilter.html
//! [`TimingLayer::view_active()`]: struct.TimingLayer.html#method.view_active
//! [`init_tracing`]: fn.init_tracing.html

use dashmap::DashMap;
use std::collections::HashMap;
use std::convert::TryInto;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Once;
use std::time::{Duration, Instant};
use tracing::Dispatch;
use tracing::Subscriber;
use tracing_subscriber::layer::{Context, Layer};
use tracing_subscriber::registry::LookupSpan;
use tracing_subscriber::EnvFilter;

static INIT: Once = Once::new();

/// Initialize the global tracing dispatcher with the one built by the provided builder.
pub fn init_tracing(builder: DispatchBuilder) {
    INIT.call_once(|| {
        tracing::dispatcher::set_global_default(builder.finish()).unwrap();
    });
}

/// A builder to construct the stack of layers we use to process tracing events
/// and spans.
#[derive(Default)]
pub struct DispatchBuilder {
    timing: bool,
    json: bool,
}

impl DispatchBuilder {
    /// Enable or disable timing.
    pub fn timing(mut self, timing: bool) -> Self {
        self.timing = timing;
        self
    }

    /// Enable or disable json output.
    pub fn json(mut self, json: bool) -> Self {
        self.json = json;
        self
    }

    /// Create a new `Dispatch`.
    pub fn finish(self) -> Dispatch {
        // Since the layer combinations are statically typed, we need to cover every
        // combination of options to avoid any `dyn` objects. Additionally, we
        // need to distinguish between testing and non-testing configurations so
        // that `with_test_writer()` is called appropriately.

        macro_rules! build_logging_layer {
            () => {{
                let logging_layer;
                cfg_if::cfg_if! {
                    if #[cfg(not(test))] {
                    logging_layer = tracing_subscriber::fmt::layer()
                        .with_span_events(tracing_subscriber::fmt::format::FmtSpan::CLOSE)
                        .with_writer(std::io::stderr);
                    } else {
                        use tracing_subscriber::fmt::format::*;
                        logging_layer = tracing_subscriber::fmt::layer()
                            .with_span_events(FmtSpan::CLOSE)
                            .with_test_writer();
                    }
                }
                let logging_layer2;
                cfg_if::cfg_if! {
                    if #[cfg(not(feature = "log-print-timeless"))] {
                        logging_layer2 = logging_layer;
                    } else {
                        logging_layer2 = logging_layer.without_time();
                    }
                }
                logging_layer2
            }};
        }

        match (self.timing, self.json) {
            (true, true) => Dispatch::new(EnvFilter::from_default_env().with_subscriber(
                build_logging_layer!().json().with_subscriber(
                    TimingLayer::new().with_subscriber(tracing_subscriber::registry()),
                ),
            )),
            (true, false) => Dispatch::new(EnvFilter::from_default_env().with_subscriber(
                build_logging_layer!().with_subscriber(
                    TimingLayer::new().with_subscriber(tracing_subscriber::registry()),
                ),
            )),
            (false, true) => Dispatch::new(
                EnvFilter::from_default_env().with_subscriber(
                    build_logging_layer!()
                        .json()
                        .with_subscriber(tracing_subscriber::registry()),
                ),
            ),
            (false, false) => Dispatch::new(EnvFilter::from_default_env().with_subscriber(
                build_logging_layer!().with_subscriber(tracing_subscriber::registry()),
            )),
        }
    }
}

/// A tracing `Layer` to track timing information on spans.
pub struct TimingLayer {
    span_times: DashMap<tracing::span::Id, (Duration, Option<Instant>)>,
    durations: DashMap<&'static str, AtomicDuration>,
}

impl TimingLayer {
    fn new() -> Self {
        TimingLayer {
            span_times: DashMap::new(),
            durations: DashMap::new(),
        }
    }

    pub fn read_active() -> Option<HashMap<&'static str, Duration>> {
        tracing::dispatcher::get_default(|dispatch: &Dispatch| {
            let timing_layer: &TimingLayer = dispatch.downcast_ref()?;
            Some(
                timing_layer
                    .durations
                    .iter()
                    .map(|entry| (*entry.key(), entry.value().total()))
                    .collect(),
            )
        })
    }
}

impl<S: Subscriber> Layer<S> for TimingLayer
where
    S: for<'lookup> LookupSpan<'lookup>,
{
    fn on_enter(&self, id: &tracing::span::Id, _ctx: Context<'_, S>) {
        let mut entry = self
            .span_times
            .entry(id.clone())
            .or_insert_with(|| (Duration::new(0, 0), None));
        assert_eq!(entry.1, None);
        entry.1 = Some(Instant::now());
    }

    fn on_exit(&self, id: &tracing::span::Id, _ctx: Context<'_, S>) {
        let end = Instant::now();
        let mut span_time = self.span_times.get_mut(id).unwrap();
        let start = span_time.1.take().unwrap();
        span_time.0 += end.duration_since(start);
    }

    fn on_close(&self, id: tracing::span::Id, ctx: Context<'_, S>) {
        let (_, (span_duration, span_start)) = self.span_times.remove(&id).unwrap();
        assert_eq!(span_start, None);

        let name = ctx.metadata(&id).unwrap().name();
        if let Some(histogram) = self.durations.get(name) {
            histogram.record(span_duration);
        } else {
            self.durations
                .entry(name)
                .or_insert_with(AtomicDuration::new)
                .record(span_duration);
        }
    }
}

struct AtomicDuration {
    total: AtomicU64,
}

impl AtomicDuration {
    fn new() -> Self {
        AtomicDuration {
            total: AtomicU64::new(0),
        }
    }

    /// Record a single duration.
    fn record(&self, duration: Duration) {
        assert!(duration > Duration::from_nanos(0));
        let nanos: u64 = duration.as_nanos().try_into().unwrap();
        self.total.fetch_add(nanos, Ordering::Relaxed);
    }

    /// Retrieve the total duration.
    fn total(&self) -> Duration {
        Duration::from_nanos(self.total.load(Ordering::Relaxed))
    }
}

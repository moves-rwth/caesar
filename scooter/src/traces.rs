//! Parsing output from the Rust `tracing` crate.

use std::{str::FromStr, time::Duration};

use serde::Deserialize;
use serde_json::{Map, Value};

enum TimeUnit {
    Nanos,
    Micros,
    Millis,
    Secs,
}

impl TimeUnit {
    fn parse_with_suffix(s: &str) -> Option<(&str, Self)> {
        #[allow(clippy::manual_map)]
        if let Some(stripped) = s.strip_suffix("ns") {
            Some((stripped, Self::Nanos))
        } else if let Some(stripped) = s.strip_suffix("µs") {
            Some((stripped, Self::Micros))
        } else if let Some(stripped) = s.strip_suffix("ms") {
            Some((stripped, Self::Millis))
        } else if let Some(stripped) = s.strip_suffix("s") {
            Some((stripped, Self::Secs))
        } else {
            None
        }
    }

    fn next_smaller(&self) -> Option<Self> {
        match self {
            Self::Nanos => None,
            Self::Micros => Some(Self::Nanos),
            Self::Millis => Some(Self::Micros),
            Self::Secs => Some(Self::Millis),
        }
    }

    fn to_duration(&self, value: u64) -> Duration {
        match self {
            Self::Nanos => Duration::from_nanos(value),
            Self::Micros => Duration::from_micros(value),
            Self::Millis => Duration::from_millis(value),
            Self::Secs => Duration::from_secs(value),
        }
    }
}

/// A `Duration` that can be parsed from tracing's output.
#[derive(Debug)]
pub struct TracingDuration(pub Duration);

impl FromStr for TracingDuration {
    type Err = TracingDurationParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (s, unit) = TimeUnit::parse_with_suffix(s).ok_or(TracingDurationParseError)?;
        let (value, unit) = if s.contains(".") {
            let mut parts = s.split('.');
            let decimal_part = parts.next().unwrap();
            let decimal_part =
                u64::from_str(decimal_part).map_err(|_| TracingDurationParseError)?;

            if let Some(next_unit) = unit.next_smaller() {
                let fractional_part = parts.next().unwrap();
                let fractional_length = fractional_part.len();
                let fractional_part =
                    u64::from_str(fractional_part).map_err(|_| TracingDurationParseError)?;

                let value =
                    decimal_part * 1000 + fractional_part * 10u64.pow(3 - fractional_length as u32);
                (value, next_unit)
            } else {
                (decimal_part, unit)
            }
        } else {
            let value = u64::from_str(s).map_err(|_| TracingDurationParseError)?;
            (value, unit)
        };

        Ok(TracingDuration(unit.to_duration(value)))
    }
}

#[derive(Debug)]
pub struct TracingDurationParseError;

impl std::fmt::Display for TracingDurationParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "invalid tracing duration format")
    }
}

impl std::error::Error for TracingDurationParseError {}

impl<'de> Deserialize<'de> for TracingDuration {
    fn deserialize<D>(deserializer: D) -> Result<TracingDuration, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        TracingDuration::from_str(&s).map_err(serde::de::Error::custom)
    }
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "lowercase", tag = "message")]
pub enum TracingEventFields {
    Close {
        #[serde(rename = "time.busy")]
        time_busy: TracingDuration,
        #[serde(rename = "time.idle")]
        time_idle: TracingDuration,
    },
}

/// A tracing event.
#[derive(Debug, Deserialize)]
pub struct TracingEvent {
    pub timestamp: String,
    pub level: String,
    pub fields: Map<String, Value>,
    pub span: Option<TracingSpan>,
    pub spans: Option<Vec<TracingSpan>>,
}

#[derive(Debug)]
pub struct TracingSpan {
    pub name: String,
}

/// We have our own Deserialize impl because this one allows duplicate fields.
/// The tracing library has some weird bugs where some messages are invalid json.
impl<'de> Deserialize<'de> for TracingSpan {
    fn deserialize<D>(deserializer: D) -> Result<TracingSpan, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct TracingSpanVisitor;

        impl<'de> serde::de::Visitor<'de> for TracingSpanVisitor {
            type Value = TracingSpan;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("struct TracingSpan")
            }

            fn visit_map<V>(self, mut map: V) -> Result<TracingSpan, V::Error>
            where
                V: serde::de::MapAccess<'de>,
            {
                let mut name = None;

                while let Some(key) = map.next_key::<String>()? {
                    match key.as_str() {
                        "name" => {
                            let next_value = map.next_value()?;
                            if name.is_none() {
                                name = Some(next_value);
                            }
                        }
                        _ => {
                            let _ = map.next_value::<serde::de::IgnoredAny>()?;
                        }
                    }
                }

                let name = name.ok_or_else(|| serde::de::Error::missing_field("name"))?;
                Ok(TracingSpan { name })
            }
        }

        deserializer.deserialize_map(TracingSpanVisitor)
    }
}

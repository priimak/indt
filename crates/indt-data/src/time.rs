use regex::Regex;
use std::cmp::{min, Ordering};
use std::fmt;
use std::fmt::Formatter;
use std::ops::{Add, Div, Mul, Sub};
use std::sync::LazyLock;

#[repr(u64)]
#[derive(PartialEq, Eq, Ord, PartialOrd, Debug, Clone, Copy)]
pub enum TimeUnit {
    NS = 1, // nanoseconds
    US = 1000, // microseconds
    MS = 1000000, // milliseconds
    S = 1000000000,  // seconds
    M = 60000000000,  // minutes
    H = 3600000000000,   // hours
}

impl TimeUnit {
    #[allow(dead_code)]
    pub fn value_of(s: &str) -> Result<TimeUnit, String> {
        match &*s.to_lowercase() {
            "ns" => Ok(TimeUnit::NS),
            "us" => Ok(TimeUnit::US),
            "ms" => Ok(TimeUnit::MS),
            "s" => Ok(TimeUnit::S),
            "m" => Ok(TimeUnit::M),
            "h" => Ok(TimeUnit::H),
            _ => Err(format!("Unable to parse time unit {}", 7))
        }
    }
}

impl fmt::Display for TimeUnit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TimeUnit::NS => write!(f, "ns"),
            TimeUnit::US => write!(f, "us"),
            TimeUnit::MS => write!(f, "ms"),
            TimeUnit::S => write!(f, "s"),
            TimeUnit::M => write!(f, "m"),
            TimeUnit::H => write!(f, "h"),
        }
    }
}

#[repr(u64)]
#[derive(PartialEq, Eq, Ord, PartialOrd, Debug, Clone, Copy)]
pub enum FrequencyUnit {
    Hz = 1,
    KHz = 1000,
    MHz = 1000000,
    GHz = 1000000000,
    THz = 1000000000000,
}

impl FrequencyUnit {
    #[allow(dead_code)]
    pub fn value_of(s: &str) -> Result<FrequencyUnit, String> {
        match &*s.to_lowercase() {
            "hz" => Ok(FrequencyUnit::Hz),
            "khz" => Ok(FrequencyUnit::KHz),
            "mhz" => Ok(FrequencyUnit::MHz),
            "ghz" => Ok(FrequencyUnit::GHz),
            "thz" => Ok(FrequencyUnit::THz),
            _ => Err(format!("Unable to parse frequency unit [{}]", s))
        }
    }
}

impl fmt::Display for FrequencyUnit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            FrequencyUnit::Hz => write!(f, "Hz"),
            FrequencyUnit::KHz => write!(f, "KHz"),
            FrequencyUnit::MHz => write!(f, "MHz"),
            FrequencyUnit::GHz => write!(f, "GHz"),
            FrequencyUnit::THz => write!(f, "THz"),
        }
    }
}


/// Object that represents duration interval.
#[derive(Debug, Clone)]
pub struct Duration {
    value: f64,
    unit: TimeUnit,
}

static DURATION_MATCHER: LazyLock<Regex> = LazyLock::new(|| Regex::new(
    r"^\s*(?<value>\d+(\.\d+)?)\s*(?<unit>ns|us|ms|s|m|h)\s*$"
).unwrap());

static FREQUENCY_MATCHER: LazyLock<Regex> = LazyLock::new(|| Regex::new(
    r"^\s*(?<value>\d+(\.\d+)?)\s*(?<unit>(|k|K|m|M|g|G|t|T)[hH][zZ])\s*$"
).unwrap());

impl Duration {
    /// Returns this duration in different time unit.
    #[allow(dead_code)]
    pub fn in_unit(self: &Duration, unit: TimeUnit) -> Duration {
        let scale: f64 = (self.unit as u64 as f64) / (unit as u64 as f64);
        Duration { value: self.value * scale, unit: unit }
    }

    /// Returns [`Result`] containing either instance of [`Duration`] or an error message.
    #[allow(dead_code)]
    pub fn value_of(s: &str) -> Result<Duration, String> {
        match DURATION_MATCHER.captures(&*s) {
            None => Err(format!("Failed to parse input string [{}] as duration", s)),
            Some(m) => Ok(Duration {
                value: m["value"].parse::<f64>().unwrap(),
                unit: TimeUnit::value_of(&m["unit"]).unwrap(),
            })
        }
    }

    /// Returns instance of Duration or panics.
    #[allow(dead_code)]
    #[inline(always)]
    pub fn new(s: &str) -> Duration { Duration::value_of(s).unwrap() }
}

impl PartialOrd<Self> for Duration {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.value.partial_cmp(&other.in_unit(self.unit).value)
    }

    fn lt(&self, other: &Self) -> bool {
        self.value < other.in_unit(self.unit).value
    }

    fn le(&self, other: &Self) -> bool {
        self.value <= other.in_unit(self.unit).value
    }

    fn gt(&self, other: &Self) -> bool {
        self.value > other.in_unit(self.unit).value
    }

    fn ge(&self, other: &Self) -> bool {
        self.value >= other.in_unit(self.unit).value
    }
}


impl PartialEq<Self> for Duration {
    fn eq(&self, other: &Self) -> bool {
        other.in_unit(self.unit).value == self.value
    }
}

impl Mul<f64> for Duration {
    type Output = Duration;

    fn mul(self, scale: f64) -> Self::Output {
        Duration { value: self.value * scale, unit: self.unit }
    }
}

impl Mul<Duration> for i64 {
    type Output = Duration;

    fn mul(self, a: Duration) -> Self::Output {
        Duration { value: (self as f64) * a.value, unit: a.unit }
    }
}

impl Mul<&Duration> for i64 {
    type Output = Duration;

    fn mul(self, a: &Duration) -> Self::Output {
        Duration { value: (self as f64) * a.value, unit: a.unit }
    }
}

impl Mul<Duration> for f64 {
    type Output = Duration;

    fn mul(self, a: Duration) -> Self::Output {
        Duration { value: self * a.value, unit: a.unit }
    }
}

impl Mul<&Duration> for f64 {
    type Output = Duration;

    fn mul(self, a: &Duration) -> Self::Output {
        Duration { value: self * a.value, unit: a.unit }
    }
}

impl Mul<i64> for &Duration {
    type Output = Duration;

    fn mul(self, scale: i64) -> Self::Output {
        Duration { value: self.value * (scale as f64), unit: self.unit }
    }
}

impl Mul<f64> for &Duration {
    type Output = Duration;

    fn mul(self, scale: f64) -> Self::Output {
        Duration { value: self.value * scale, unit: self.unit }
    }
}


impl Mul<i64> for Duration {
    type Output = Duration;

    fn mul(self, scale: i64) -> Self::Output {
        Duration { value: self.value * (scale as f64), unit: self.unit }
    }
}

impl Add for Duration {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        let target_unit: TimeUnit = min(self.unit, other.unit);
        Duration {
            value: self.in_unit(target_unit).value + other.in_unit(target_unit).value,
            unit: target_unit,
        }
    }
}

impl Add for &Duration {
    type Output = Duration;

    fn add(self, other: Self) -> Self::Output {
        let target_unit: TimeUnit = min(self.unit, other.unit);
        Duration {
            value: self.in_unit(target_unit).value + other.in_unit(target_unit).value,
            unit: target_unit,
        }
    }
}

impl Sub for Duration {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        let target_unit: TimeUnit = min(self.unit, other.unit);
        Duration {
            value: self.in_unit(target_unit).value - other.in_unit(target_unit).value,
            unit: target_unit,
        }
    }
}

impl Sub for &Duration {
    type Output = Duration;

    fn sub(self, other: Self) -> Self::Output {
        let target_unit: TimeUnit = min(self.unit, other.unit);
        Duration {
            value: self.in_unit(target_unit).value - other.in_unit(target_unit).value,
            unit: target_unit,
        }
    }
}

impl Div<i64> for Duration {
    type Output = Duration;

    fn div(self, scale: i64) -> Self::Output {
        Duration { value: self.value / (scale as f64), unit: self.unit }
    }
}

impl Div<f64> for Duration {
    type Output = Duration;

    fn div(self, scale: f64) -> Self::Output {
        Duration { value: self.value / (scale as f64), unit: self.unit }
    }
}

impl Div<i64> for &Duration {
    type Output = Duration;

    fn div(self, scale: i64) -> Self::Output {
        Duration { value: self.value / (scale as f64), unit: self.unit }
    }
}

impl Div<f64> for &Duration {
    type Output = Duration;

    fn div(self, scale: f64) -> Self::Output {
        Duration { value: self.value / (scale as f64), unit: self.unit }
    }
}

impl fmt::Display for Duration {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.value, self.unit)
    }
}

////////////////////////// Frequency

#[derive(Debug, Clone)]
pub struct Frequency {
    value: f64,
    unit: FrequencyUnit,
}

impl Frequency {
    /// Returns this frequency in different unit.
    #[allow(dead_code)]
    pub fn in_unit(self: &Frequency, unit: FrequencyUnit) -> Frequency {
        let scale: f64 = (self.unit as u64 as f64) / (unit as u64 as f64);
        Frequency { value: self.value * scale, unit: unit }
    }

    /// Returns [`Result`] containing either instance of [`Frequency`] or an error message.
    #[allow(dead_code)]
    pub fn value_of(s: &str) -> Result<Frequency, String> {
        match FREQUENCY_MATCHER.captures(&*s) {
            None => Err(format!("Failed to parse input string [{}] as frequency", s)),
            Some(m) => Ok(Frequency {
                value: m["value"].parse::<f64>().unwrap(),
                unit: FrequencyUnit::value_of(&m["unit"]).unwrap(),
            })
        }
    }


    /// Returns instance of [`Frequency`] or panics.
    #[allow(dead_code)]
    #[inline(always)]
    pub fn new(s: &str) -> Frequency { Frequency::value_of(s).unwrap() }
}

impl fmt::Display for Frequency {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.value, self.unit)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_time_unit() {
        let mut tu = TimeUnit::value_of("NS").unwrap();
        assert_eq!(tu as u64, 1);
        assert_eq!(format!("{}", tu), "ns");

        tu = TimeUnit::value_of("ns").unwrap();
        assert_eq!(tu as u64, 1);
        assert_eq!(format!("{}", tu), "ns");

        tu = TimeUnit::value_of("us").unwrap();
        assert_eq!(tu as u64, 1000);
        assert_eq!(format!("{}", tu), "us");

        tu = TimeUnit::value_of("Ms").unwrap();
        assert_eq!(tu as u64, 1000000);
        assert_eq!(format!("{}", tu), "ms");

        tu = TimeUnit::value_of("S").unwrap();
        assert_eq!(tu as u64, 1000000000);
        assert_eq!(format!("{}", tu), "s");

        tu = TimeUnit::value_of("m").unwrap();
        assert_eq!(tu as u64, 60000000000);
        assert_eq!(format!("{}", tu), "m");

        tu = TimeUnit::value_of("h").unwrap();
        assert_eq!(tu as u64, 3600000000000);
        assert_eq!(format!("{}", tu), "h");
    }

    #[test]
    fn test_duration_parsing_fail() {
        assert!(Duration::value_of("").is_err());
        assert!(Duration::value_of("7 kjahskd").is_err());
        assert!(Duration::value_of("7 mss").is_err());
        assert!(Duration::value_of("7 MS").is_err());
    }


    #[test]
    fn test_duration_parsing_success() {
        let mut a = Duration::value_of("7ms");
        assert!(a.is_ok());
        assert!(a.as_ref().map_or(false, |duration| duration.unit == TimeUnit::MS));
        assert!(a.as_ref().map_or(false, |duration| duration.value == 7.0));

        a = Duration::value_of("7     ms ");
        assert!(a.is_ok());
        assert!(a.as_ref().map_or(false, |duration| duration.unit == TimeUnit::MS));
        assert!(a.as_ref().map_or(false, |duration| duration.value == 7.0));
    }

    #[test]
    fn test_duration_ord() {
        assert!(Duration::new("7ms") == Duration::new("7000 us"));
        assert!(Duration::new("7ms") <= Duration::new("7000 us"));
        assert!(Duration::new("7ms") < Duration::new("7001 us"));
        assert!(Duration::new("7ms") <= Duration::new("7001 us"));
        assert!(Duration::new("7ms") == Duration::new("0.007 s"));
        assert!(Duration::new("7ms") >= Duration::new("0.007 s"));
        assert!(Duration::new("7ms") > Duration::new("0.0068 s"));
        assert_eq!(false, Duration::new("7ms") == Duration::new("7001 us"));
        assert!(Duration::value_of("0.014 s") != Duration::value_of("0.014 sz"));
    }

    #[test]
    fn test_duration_ops() {
        let a = Duration::new("7     ms");

        // multiplication by a number
        assert_eq!(&a * 2, Duration::new("14 ms"));
        assert_eq!(&a * 2.0, Duration::new("0.014 s"));
        assert_eq!(3.0 * &a, Duration::new("0.021 s"));
        assert_eq!(4 * &a, Duration::new("0.028 s"));

        assert_eq!(Duration::new("7ms") * 2, Duration::new("14 ms"));
        assert_eq!(Duration::new("7ms") * 2.0, Duration::new("0.014 s"));
        assert_eq!(3.0 * Duration::new("7ms"), Duration::new("0.021 s"));
        assert_eq!(4 * Duration::new("7ms"), Duration::new("0.028 s"));

        // division by a number
        assert_eq!(&a / 2, Duration::new("0.0035 s"));
        assert_eq!(&a / 2.0, Duration::new("0.0035 s"));
        assert_eq!(Duration::new("7ms") / 2, Duration::new("0.0035 s"));
        assert_eq!(Duration::new("7ms") / 2.0, Duration::new("0.0035 s"));

        // add two durations
        let x = Duration::new("5 ms");
        let y = Duration::new("3 ms");
        assert_eq!(&x + &y, Duration::new("8 ms"));
        assert_eq!(x + y, Duration::new("0.008 s"));

        // subtract two durations
        let a = Duration::new("3s");
        let b = Duration::new("5 ms");
        assert_eq!(&a - &b, Duration::new("2.995 s"));
        assert_eq!(a - b, Duration::new("2.995 s"));
    }

    #[test]
    fn test_duration_transform() {
        assert_eq!(Duration::new("3s").in_unit(TimeUnit::MS).unit, TimeUnit::MS);
        assert_eq!(Duration::new("3s").in_unit(TimeUnit::MS).value, 3000.0);
        assert_eq!(Duration::new("3s").in_unit(TimeUnit::US).value, 3000000.0);
    }

    #[test]
    fn test_frequency_unit() {
        let f = |s| FrequencyUnit::value_of(s).unwrap();

        assert_eq!(f("hz") as u64, 1);
        assert_eq!(format!("{}", f("hz")), "Hz");
        assert_eq!(format!("{}", f("Hz")), "Hz");
        assert_eq!(format!("{}", f("hZ")), "Hz");
        assert_eq!(format!("{}", f("HZ")), "Hz");

        assert_eq!(f("khz") as u64, 1000);
        assert_eq!(format!("{}", f("khz")), "KHz");
        assert_eq!(format!("{}", f("KHz")), "KHz");
        assert_eq!(format!("{}", f("khZ")), "KHz");
        assert_eq!(format!("{}", f("KHZ")), "KHz");

        assert_eq!(f("mhz") as u64, 1_000_000);
        assert_eq!(format!("{}", f("mhz")), "MHz");
        assert_eq!(format!("{}", f("MHz")), "MHz");
        assert_eq!(format!("{}", f("MhZ")), "MHz");
        assert_eq!(format!("{}", f("mHZ")), "MHz");

        assert_eq!(f("ghz") as u64, 1_000_000_000);
        assert_eq!(format!("{}", f("ghz")), "GHz");
        assert_eq!(format!("{}", f("GHz")), "GHz");
        assert_eq!(format!("{}", f("GhZ")), "GHz");
        assert_eq!(format!("{}", f("GHZ")), "GHz");

        assert_eq!(f("thz") as u64, 1_000_000_000_000);
        assert_eq!(format!("{}", f("thz")), "THz");
        assert_eq!(format!("{}", f("THz")), "THz");
        assert_eq!(format!("{}", f("ThZ")), "THz");
        assert_eq!(format!("{}", f("THZ")), "THz");
    }

    #[test]
    fn test_frequency_parsing_fail() {
        assert!(Frequency::value_of("").is_err());
        assert!(Frequency::value_of("7 kjahskd").is_err());
        assert!(Frequency::value_of("7 khzz").is_err());
        assert!(Frequency::value_of("7 AHz").is_err());
    }

    #[test]
    fn test_frequency_parsing_success() {
        let mut a = Frequency::value_of("7KHz");
        assert!(a.is_ok());
        assert!(a.as_ref().map_or(false, |freq| freq.unit == FrequencyUnit::KHz));
        assert!(a.as_ref().map_or(false, |freq| freq.value == 7.0));

        a = Frequency::value_of("7     mhz ");
        assert!(a.is_ok());
        assert!(a.as_ref().map_or(false, |freq| freq.unit == FrequencyUnit::MHz));
        assert!(a.as_ref().map_or(false, |freq| freq.value == 7.0));
    }
}
//! Module containing bindings to rust's `std::time` module.

use crate::real_std::{convert::TryInto, time};

use crate::vm::{
    self,
    api::{RuntimeResult, IO},
    thread::Thread,
    types::VmInt,
    ExternModule,
};

const NANOS_PER_SEC: u64 = 1_000_000_000;

macro_rules! try_convert {
    ($val: expr, $msg: expr) => {{
        $val.try_into().map_err(|_| $msg.to_string()).into()
    }};
}

macro_rules! convert_or_abort {
    ($val: expr, $msg: expr) => {{
        match try_convert!($val, $msg) {
            RuntimeResult::Return(x) => x,
            RuntimeResult::Panic(e) => return RuntimeResult::Panic(e),
        }
    }};
}

mod duration {
    use super::*;

    #[derive(Clone, Debug, Userdata, Trace, VmType)]
    #[gluon_userdata(clone)]
    #[gluon(vm_type = "std.time.types.Duration")]
    #[gluon(crate_name = "::vm")]
    #[gluon_trace(skip)]
    pub(crate) struct Duration(pub(crate) time::Duration);

    pub(crate) fn new(secs: VmInt, nanos: VmInt) -> RuntimeResult<Duration, String> {
        let secs: u64 = convert_or_abort!(secs, "seconds must be non-negative");
        let nanos: u64 = convert_or_abort!(nanos, "nanoseconds must be non-negative");
        let secs = secs.checked_add(nanos / NANOS_PER_SEC);
        let nanos = (nanos % NANOS_PER_SEC) as u32;

        match secs {
            Some(secs) => RuntimeResult::Return(Duration(time::Duration::new(secs, nanos))),
            // should never occur because i64.max_value() + i64.max_value() / 1e9 < u64.max_value()
            None => {
                RuntimeResult::Panic("seconds overflowed when creating a new Duration".to_string())
            }
        }
    }

    pub(crate) fn from_secs(secs: VmInt) -> RuntimeResult<Duration, String> {
        new(secs, 0)
    }

    pub(crate) fn from_millis(millis: VmInt) -> RuntimeResult<Duration, String> {
        let millis: u64 = convert_or_abort!(millis, "milliseconds must be non-negative");
        RuntimeResult::Return(Duration(time::Duration::from_millis(millis)))
    }

    pub(crate) fn from_micros(micros: VmInt) -> RuntimeResult<Duration, String> {
        let micros: u64 = convert_or_abort!(micros, "microseconds must be non-negative");
        RuntimeResult::Return(Duration(time::Duration::from_micros(micros)))
    }

    pub(crate) fn from_nanos(nanos: VmInt) -> RuntimeResult<Duration, String> {
        new(0, nanos)
    }

    pub(crate) fn as_secs(dur: &Duration) -> RuntimeResult<VmInt, String> {
        try_convert!(
            dur.0.as_secs(),
            "Overflow when trying to convert Duration into seconds"
        )
    }

    pub(crate) fn subsec_millis(dur: &Duration) -> VmInt {
        dur.0.subsec_millis() as VmInt
    }

    pub(crate) fn subsec_micros(dur: &Duration) -> VmInt {
        dur.0.subsec_micros() as VmInt
    }

    pub(crate) fn subsec_nanos(dur: &Duration) -> VmInt {
        dur.0.subsec_nanos() as VmInt
    }

    pub(crate) fn as_millis(dur: &Duration) -> RuntimeResult<VmInt, String> {
        try_convert!(
            dur.0.as_millis(),
            "Overflow when trying to convert Duration into milliseconds"
        )
    }

    pub(crate) fn as_micros(dur: &Duration) -> RuntimeResult<VmInt, String> {
        try_convert!(
            dur.0.as_micros(),
            "Overflow when trying to convert Duration into microseconds"
        )
    }

    pub(crate) fn as_nanos(dur: &Duration) -> RuntimeResult<VmInt, String> {
        try_convert!(
            dur.0.as_nanos(),
            "Overflow when trying to convert Duration into nanoseconds"
        )
    }

    pub(crate) fn checked_add(dur1: &Duration, dur2: &Duration) -> Option<Duration> {
        dur1.0.checked_add(dur2.0).map(Duration)
    }

    pub(crate) fn checked_sub(dur1: &Duration, dur2: &Duration) -> Option<Duration> {
        dur1.0.checked_sub(dur2.0).map(Duration)
    }

    // should this be Option because it better matches Rust's API or Result because it could fail
    // in two different ways?
    pub(crate) fn checked_mul(dur: &Duration, multiplier: VmInt) -> Option<Duration> {
        match multiplier.try_into() {
            Ok(n) => dur.0.checked_mul(n).map(Duration),
            Err(_) => None,
        }
    }

    pub(crate) fn checked_div(dur: &Duration, divisor: VmInt) -> Option<Duration> {
        match divisor.try_into() {
            Ok(n) => dur.0.checked_div(n).map(Duration),
            Err(_) => None,
        }
    }

    pub(crate) fn eq(dur1: &Duration, dur2: &Duration) -> bool {
        dur1.0 == dur2.0
    }

    pub(crate) fn lt(dur1: &Duration, dur2: &Duration) -> bool {
        dur1.0 < dur2.0
    }
}

mod instant {
    use super::{duration::Duration, *};

    #[derive(Clone, Debug, Userdata, Trace, VmType)]
    #[gluon_userdata(clone)]
    #[gluon(vm_type = "std.time.types.Instant")]
    #[gluon(crate_name = "::vm")]
    #[gluon_trace(skip)]
    pub(crate) struct Instant(pub(crate) time::Instant);

    pub(crate) fn now() -> IO<Instant> {
        IO::Value(Instant(time::Instant::now()))
    }

    // Note: The parameters are reversed relative to the underlying standard library function
    pub(crate) fn duration_since(earlier: &Instant, later: &Instant) -> Result<Duration, Duration> {
        // Should never panic because either earlier <= later or later > earlier
        later.0
            .checked_duration_since(earlier.0)
            .map(Duration)
            .ok_or_else( ||
                earlier.0
                    .checked_duration_since(later.0)
                    .map(Duration)
                    .unwrap(),
            )
    }

    // Note: The parameters are reversed relative to the underlying standard library function
    pub(crate) fn saturating_duration_since(earlier: &Instant, later: &Instant) -> Duration {
        Duration(later.0.saturating_duration_since(earlier.0))
    }

    pub(crate) fn elapsed(earlier: &Instant) -> IO<Result<Duration, Duration>> {
        IO::Value(duration_since(earlier, &Instant(time::Instant::now())))
    }

    pub(crate) fn checked_add(moment: &Instant, dur: &Duration) -> Option<Instant> {
        moment.0.checked_add(dur.0).map(Instant)
    }

    pub(crate) fn checked_sub(moment: &Instant, dur: &Duration) -> Option<Instant> {
        moment.0.checked_sub(dur.0).map(Instant)
    }

    pub(crate) fn eq(moment1: &Instant, moment2: &Instant) -> bool {
        moment1.0 == moment2.0
    }

    pub(crate) fn lt(moment1: &Instant, moment2: &Instant) -> bool {
        moment1.0 < moment2.0
    }
}

mod system_time {
    use super::{duration::Duration, *};

    #[derive(Clone, Debug, Userdata, Trace, VmType)]
    #[gluon_userdata(clone)]
    #[gluon(vm_type = "std.time.types.SystemTime")]
    #[gluon(crate_name = "::vm")]
    #[gluon_trace(skip)]
    pub(crate) struct SystemTime(pub(crate) time::SystemTime);

    pub(crate) fn now() -> IO<SystemTime> {
        IO::Value(SystemTime(time::SystemTime::now()))
    }

    // Note: The parameters are reversed relative to the underlying standard library function
    /// Returns `Ok(later - earlier)` if `later` is the same as or later than `earlier`.
    /// Returns `Err(earlier - later)` if `later` is earlier than `earlier`.
    pub(crate) fn duration_since(
        earlier: &SystemTime,
        later: &SystemTime,
    ) -> Result<Duration, Duration> {
        later.0
            .duration_since(earlier.0)
            .map(|x| Duration(x))
            .map_err(|e| Duration(e.duration()))
    }

    // Note: The parameters are reversed relative to the underlying standard library function
    /// Returns `later - earlier` if `later` is the same as or later than `earlier`.
    /// Returns `0` if `later` is earlier than `earlier`.
    pub(crate) fn saturating_duration_since(
        earlier: &SystemTime,
        later: &SystemTime
    ) -> Duration {
        Duration(
            later.0
                .duration_since(earlier.0)
                .unwrap_or(time::Duration::new(0, 0)),
        )
    }

    pub(crate) fn elapsed(earlier: &SystemTime) -> IO<Result<Duration, Duration>> {
        IO::Value(
            earlier.0
                .elapsed()
                .map(|x| Duration(x))
                .map_err(|e| Duration(e.duration())),
        )
    }

    pub(crate) fn checked_add(moment: &SystemTime, dur: &Duration) -> Option<SystemTime> {
        moment.0.checked_add(dur.0).map(SystemTime)
    }

    pub(crate) fn checked_sub(moment: &SystemTime, dur: &Duration) -> Option<SystemTime> {
        moment.0.checked_sub(dur.0).map(SystemTime)
    }

    pub(crate) fn eq(moment1: &SystemTime, moment2: &SystemTime) -> bool {
        moment1.0 == moment2.0
    }

    pub(crate) fn lt(moment1: &SystemTime, moment2: &SystemTime) -> bool {
        moment1.0 < moment2.0
    }
}

mod std {
    pub mod time {
        pub use crate::std_lib::time as prim;
    }
}

pub fn load(vm: &Thread) -> vm::Result<ExternModule> {
    vm.register_type::<duration::Duration>("std.time.types.Duration", &[])?;
    vm.register_type::<instant::Instant>("std.time.types.Instant", &[])?;
    vm.register_type::<system_time::SystemTime>("std.time.types.SystemTime", &[])?;

    ExternModule::new(
        vm,
        record! {
            duration => record! {
                type std::time::Duration => duration::Duration,

                new => primitive!(2, std::time::prim::duration::new),
                from_secs => primitive!(1, std::time::prim::duration::from_secs),
                from_millis => primitive!(1, std::time::prim::duration::from_millis),
                from_micros => primitive!(1, std::time::prim::duration::from_micros),
                from_nanos => primitive!(1, std::time::prim::duration::from_nanos),

                as_secs => primitive!(1, std::time::prim::duration::as_secs),
                subsec_millis => primitive!(1, std::time::prim::duration::subsec_millis),
                subsec_micros => primitive!(1, std::time::prim::duration::subsec_micros),
                subsec_nanos => primitive!(1, std::time::prim::duration::subsec_nanos),
                as_millis => primitive!(1, std::time::prim::duration::as_millis),
                as_micros => primitive!(1, std::time::prim::duration::as_micros),
                as_nanos => primitive!(1, std::time::prim::duration::as_nanos),

                checked_add => primitive!(2, std::time::prim::duration::checked_add),
                checked_sub => primitive!(2, std::time::prim::duration::checked_sub),
                checked_mul => primitive!(2, std::time::prim::duration::checked_mul),
                checked_div => primitive!(2, std::time::prim::duration::checked_div),

                eq => primitive!(2, std::time::prim::duration::eq),
                lt => primitive!(2, std::time::prim::duration::lt),
            },
            instant => record! {
                type std::time::Instant => instant::Instant,

                now => primitive!(0, std::time::prim::instant::now),
                duration_since => primitive!(2, std::time::prim::instant::duration_since),
                saturating_duration_since => primitive!(2, std::time::prim::instant::saturating_duration_since),
                elapsed => primitive!(1, std::time::prim::instant::elapsed),

                checked_add => primitive!(2, std::time::prim::instant::checked_add),
                checked_sub => primitive!(2, std::time::prim::instant::checked_sub),

                eq => primitive!(2, std::time::prim::instant::eq),
                lt => primitive!(2, std::time::prim::instant::lt),
            },
            system_time => record! {
                type std::time::SystemTime => system_time::SystemTime,

                unix_epoch => system_time::SystemTime(time::UNIX_EPOCH),

                now => primitive!(0, std::time::prim::system_time::now),
                duration_since => primitive!(2, std::time::prim::system_time::duration_since),
                saturating_duration_since => primitive!(2, std::time::prim::system_time::saturating_duration_since),
                elapsed => primitive!(1, std::time::prim::system_time::elapsed),

                checked_add => primitive!(2, std::time::prim::system_time::checked_add),
                checked_sub => primitive!(2, std::time::prim::system_time::checked_sub),

                eq => primitive!(2, std::time::prim::system_time::eq),
                lt => primitive!(2, std::time::prim::system_time::lt),
            },
        },
    )
}

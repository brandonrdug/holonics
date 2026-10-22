//! Exterior Linux monotonic clock boundary for the example supervisor contract.
//!
//! The only unsafe code in this module is the OS FFI call; no HNN law or library code depends on it.

use std::io;

#[cfg(all(target_os = "linux", target_pointer_width = "64"))]
use std::os::raw::{c_int, c_long};

#[cfg(all(target_os = "linux", target_pointer_width = "64"))]
#[repr(C)]
struct Timespec {
    tv_sec: c_long,
    tv_nsec: c_long,
}

#[cfg(all(target_os = "linux", target_pointer_width = "64"))]
unsafe extern "C" {
    fn clock_gettime(clock_id: c_int, time: *mut Timespec) -> c_int;
}

/// Read `CLOCK_MONOTONIC` as checked nanoseconds from the same clock used by Python
/// `time.monotonic_ns()`. Other platforms fail closed rather than substituting UTC or `Instant`.
pub(super) fn monotonic_ns() -> io::Result<u128> {
    #[cfg(all(target_os = "linux", target_pointer_width = "64"))]
    {
        let mut time = Timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        // SAFETY: `time` points to a live, writable C-layout timespec for the duration of the
        // call; CLOCK_MONOTONIC is Linux clock id 1 and requires no additional resource handle.
        let status = unsafe { clock_gettime(1, &mut time) };
        if status != 0 {
            return Err(io::Error::last_os_error());
        }
        if time.tv_sec < 0 || !(0..1_000_000_000).contains(&time.tv_nsec) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "CLOCK_MONOTONIC returned an invalid timespec",
            ));
        }
        let seconds = u128::try_from(time.tv_sec).map_err(|_| {
            io::Error::new(io::ErrorKind::InvalidData, "negative monotonic seconds")
        })?;
        let nanos = u128::try_from(time.tv_nsec).map_err(|_| {
            io::Error::new(io::ErrorKind::InvalidData, "negative monotonic nanoseconds")
        })?;
        return seconds
            .checked_mul(1_000_000_000)
            .and_then(|whole| whole.checked_add(nanos))
            .ok_or_else(|| {
                io::Error::new(io::ErrorKind::InvalidData, "monotonic nanoseconds overflow")
            });
    }
    #[cfg(not(all(target_os = "linux", target_pointer_width = "64")))]
    {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "REQ-063 external monotonic deadline contract requires 64-bit Linux CLOCK_MONOTONIC",
        ))
    }
}

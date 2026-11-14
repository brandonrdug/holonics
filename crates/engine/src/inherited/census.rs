//! **The measured need of a declared width** (the width census's §5, theory November 8): while a census read runs,
//! each instrumented site records the largest bit length its values reached and how often it was met, so a carrier
//! is read beside its need (a value's top place against `i64`'s 63 or `i128`'s 127), and a count site records how
//! often an event happened (a saturation, a release to zero). Off, a site costs one relaxed load and records nothing,
//! and no site changes a value: a census read and an uninstrumented run give the same bits.
//!
//! A site is named by its refusal message (sites sharing a message are read together) or by its caller's place in
//! the source (`#[track_caller]`).

use std::panic::Location;
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicUsize, Ordering};
use std::sync::Mutex;

static ON: AtomicBool = AtomicBool::new(false);
const SLOTS: usize = 2048;
static KEYS: [AtomicUsize; SLOTS] = [const { AtomicUsize::new(0) }; SLOTS];
static MOST: [AtomicU32; SLOTS] = [const { AtomicU32::new(0) }; SLOTS];
static MET: [AtomicU64; SLOTS] = [const { AtomicU64::new(0) }; SLOTS];
static NAMES: Mutex<Vec<(usize, Site)>> = Mutex::new(Vec::new());

/// A site's name.
#[derive(Clone, Copy, Debug)]
pub enum Site {
    Named(&'static str),
    At(&'static Location<'static>),
}

impl std::fmt::Display for Site {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Site::Named(s) => write!(f, "{s}"),
            Site::At(l) => write!(f, "{}:{}", l.file(), l.line()),
        }
    }
}

/// One site's reading.
#[derive(Clone, Debug)]
pub struct Reading {
    pub site: Site,
    /// The largest bit length of a magnitude met (zero at a count site).
    pub most_bits: u32,
    /// How often the site was met.
    pub met: u64,
}

/// The magnitude a site measures: its bit length (`|x|`'s, so a signed value's sign place is not counted).
pub trait Magnitude {
    fn bits(&self) -> u32;
}

macro_rules! magnitude {
    ($($t:ty),*) => {$(
        impl Magnitude for $t {
            fn bits(&self) -> u32 {
                <$t>::BITS - self.unsigned_abs().leading_zeros()
            }
        }
    )*};
}
magnitude!(i128, i64, i32);

macro_rules! unsigned_magnitude {
    ($($t:ty),*) => {$(
        impl Magnitude for $t {
            fn bits(&self) -> u32 {
                <$t>::BITS - self.leading_zeros()
            }
        }
    )*};
}
unsigned_magnitude!(u128, u64, u32);

/// Start recording (an exterior read turns this on; nothing inside a law does).
pub fn enable() {
    ON.store(true, Ordering::Relaxed);
}

pub fn enabled() -> bool {
    ON.load(Ordering::Relaxed)
}

fn slot(key: usize, site: Site) -> usize {
    let mut i = (key.wrapping_mul(0x9E37_79B9_7F4A_7C15_usize)) % SLOTS;
    for _ in 0..SLOTS {
        let k = KEYS[i].load(Ordering::Acquire);
        if k == key {
            return i;
        }
        if k == 0 {
            match KEYS[i].compare_exchange(0, key, Ordering::AcqRel, Ordering::Acquire) {
                Ok(_) => {
                    if let Ok(mut names) = NAMES.lock() {
                        names.push((i, site));
                    }
                    return i;
                }
                Err(k) if k == key => return i,
                Err(_) => {}
            }
        }
        i = (i + 1) % SLOTS;
    }
    // Every slot taken: the census reads the first slot's site as an overflow; it never refuses the law.
    0
}

fn record(key: usize, site: Site, bits: u32) {
    let i = slot(key, site);
    MOST[i].fetch_max(bits, Ordering::Relaxed);
    MET[i].fetch_add(1, Ordering::Relaxed);
}

/// A value met at a named site (its refusal message): its bit length kept if it is the largest yet.
pub fn reach<T: Magnitude>(site: &'static str, v: &T) {
    if enabled() {
        record(site.as_ptr() as usize ^ site.len().rotate_left(48), Site::Named(site), v.bits());
    }
}

/// A value met at the caller's place in the source.
#[track_caller]
pub fn reach_here<T: Magnitude>(v: &T) {
    if enabled() {
        let at = Location::caller();
        record(at as *const Location<'static> as usize, Site::At(at), v.bits());
    }
}

/// An event at a named site (a saturation, a release to zero), counted.
pub fn tally(site: &'static str, n: u64) {
    if enabled() && n > 0 {
        let i = slot(site.as_ptr() as usize ^ site.len().rotate_left(48), Site::Named(site));
        MET[i].fetch_add(n, Ordering::Relaxed);
    }
}

/// Every site met so far, in the order first met.
pub fn report() -> Vec<Reading> {
    let names = NAMES.lock().map(|n| n.clone()).unwrap_or_default();
    names.into_iter().map(|(i, site)| Reading { site, most_bits: MOST[i].load(Ordering::Relaxed), met: MET[i].load(Ordering::Relaxed) }).collect()
}

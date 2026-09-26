//! **The notebook's exterior boundary**, shared by the `hnn_design` examples (each includes it by
//! `#[path = "exterior.rs"] mod exterior;`): the cut file and its manifest, and the exact
//! presentation of readings for a person.
//!
//! [definition] **Every reading is exact; no decimal is printed** (a decimal is a collapse, CLAUDE.md's
//! exact-arithmetic law). Integers print as integers and rationals as `n/d` (`n/2^e` or
//! `n/(2^e·m)` on a wide denominator with a power-of-two factor); bits are enclosures with exact
//! endpoints, each also read at the receiver's grain `L_R` through `GrainCell::of`:
//! `n + k/L_R + ε`, the carry `n`, the phase class `k` and the exact fibre `0 ≤ ε < 1/L_R`; a
//! comparison is the exact ordering of two enclosures with their exact difference.

// Each example reads only the part of the boundary it needs.
#![allow(dead_code)]

use std::ops::Range;

use holonics::hnn::Field;
use holonics::hnn::receiving::GrainCell;
use holonics::ratio::Rat;
use holonics::ratio::algebraic::ExactInterval;
use num_bigint::BigInt;
use num_traits::One;

/// **A cut file and its manifest** (the standing real cut in `.local/cuts/`, written by
/// `standing_cut.py`), read whole at the notebook's exterior boundary: the file's bytes, the
/// manifest's population and its held-out range, read by the numbers after their keys (the manifest
/// is exterior JSON; no parser enters the crate). The file's length must be the manifest's
/// population, and the held-out range must close the cut. Only its scope and counts are printed.
#[allow(clippy::disallowed_types, clippy::disallowed_methods)]
pub fn read_cut(path: &str) -> (Vec<u8>, usize, Range<usize>) {
    let bytes =
        std::fs::read(path).unwrap_or_else(|error| panic!("read the cut file {path}: {error}"));
    let manifest_path = path
        .strip_suffix(".bin")
        .map_or_else(|| format!("{path}.json"), |stem| format!("{stem}.json"));
    let manifest = std::fs::read_to_string(&manifest_path)
        .unwrap_or_else(|error| panic!("read the cut manifest {manifest_path}: {error}"));
    let numbers_after = |key: &str| -> Vec<usize> {
        let start = manifest
            .find(key)
            .unwrap_or_else(|| panic!("the manifest names {key}"))
            + key.len();
        let rest = manifest[start..].trim_start();
        let value = if rest.starts_with('[') {
            &rest[..rest.find(']').expect("a closed list")]
        } else {
            &rest[..rest.find([',', '\n', '}']).unwrap_or(rest.len())]
        };
        value
            .split(|c: char| !c.is_ascii_digit())
            .filter(|piece| !piece.is_empty())
            .map(|piece| piece.parse().expect("a count"))
            .collect()
    };
    let population = numbers_after("\"population\":")[0];
    let range = numbers_after("\"held_out_range\":");
    assert_eq!(
        bytes.len(),
        population,
        "the cut file's length is the manifest's population"
    );
    assert_eq!(range[1], population, "the held-out range closes the cut");
    (bytes, population, range[0]..range[1])
}

// -------------------------------------------------------------------------------------------
// presentation (for a person; every reading exact, never a decimal)

/// **The receiver's grain** `L_R = ⌈1/ε_bits⌉` of the field's first receiver (campaign 1: 16), the
/// declared grain every bit count is read at.
pub fn receiver_grain(field: &Field) -> u64 {
    field.receivers()[0]
        .tolerance
        .recip()
        .ceil()
        .to_integer()
        .try_into()
        .expect("a grain fits a machine word")
}

/// An exact rational: an integer, `n/2^e` on a wide dyadic denominator, `n/(2^e·m)` on a wide
/// denominator with a power-of-two factor, or `n/d`.
pub fn exact(value: &Rat) -> String {
    let denominator = value.denom().magnitude();
    if denominator.is_one() {
        return value.numer().to_string();
    }
    let twos = denominator.trailing_zeros().unwrap_or(0);
    let odd = denominator >> twos;
    if denominator.bits() <= 16 {
        format!("{}/{}", value.numer(), denominator)
    } else if odd.is_one() {
        format!("{}/2^{twos}", value.numer())
    } else if twos > 0 {
        format!("{}/(2^{twos}·{odd})", value.numer())
    } else {
        format!("{}/{}", value.numer(), denominator)
    }
}

/// **A reading at the grain** `L` (`GrainCell::of`): `value = n + k/L + ε`, the carry `n`, the
/// phase class `k ∈ ℤ/L` and the unresolved fibre `0 ≤ ε < 1/L`, each exact.
pub fn reading(value: &Rat, grain: u64) -> String {
    let cell = GrainCell::of(value, grain);
    format!(
        "{} + {}/{grain} + ε, ε = {} < 1/{grain}",
        cell.carry,
        cell.phase,
        exact(&cell.fibre)
    )
}

/// **An enclosure read at the grain**: both endpoints' cells; when they share their carry and
/// phase class, that cell once with the enclosure of its fibre.
pub fn reading_of(interval: &ExactInterval, grain: u64) -> String {
    let (lower, upper) = (
        GrainCell::of(&interval.lower, grain),
        GrainCell::of(&interval.upper, grain),
    );
    if lower.carry == upper.carry && lower.phase == upper.phase {
        format!(
            "{} + {}/{grain} + ε, ε ∈ [{}, {}] ⊂ [0, 1/{grain})",
            lower.carry,
            lower.phase,
            exact(&lower.fibre),
            exact(&upper.fibre)
        )
    } else {
        format!(
            "[{} + {}/{grain} + {}, {} + {}/{grain} + {}] (each fibre < 1/{grain})",
            lower.carry,
            lower.phase,
            exact(&lower.fibre),
            upper.carry,
            upper.phase,
            exact(&upper.fibre)
        )
    }
}

/// An exact ratio, reduced, with its integer quotient and remainder: `n/d (q rem r over d)`.
pub fn ratio(value: &Rat) -> String {
    if value.is_integer() {
        return value.numer().to_string();
    }
    let (numerator, denominator) = (value.numer(), value.denom());
    let quotient = value.floor().to_integer();
    let remainder = numerator - &quotient * denominator;
    format!(
        "{} ({quotient} rem {remainder} over {denominator})",
        exact(value)
    )
}

/// An enclosure of bits: its exact endpoints, then its reading at the grain.
pub fn enclosure(interval: &ExactInterval, grain: u64) -> String {
    format!(
        "exact [{}, {}] bits; at L_R = {grain}: {}",
        exact(&interval.lower),
        exact(&interval.upper),
        reading_of(interval, grain)
    )
}

/// An enclosure divided by a count (bits a cell): the exact ratios read at the grain.
pub fn per(interval: &ExactInterval, count: u64, grain: u64) -> String {
    if count == 0 {
        return "-".to_string();
    }
    let count = Rat::from_integer(BigInt::from(count));
    reading_of(
        &ExactInterval {
            lower: &interval.lower / &count,
            upper: &interval.upper / &count,
        },
        grain,
    )
}

/// Where enclosure `a` lies against `b`, exactly.
pub fn against(a: &ExactInterval, b: &ExactInterval) -> &'static str {
    if a.upper < b.lower {
        "below"
    } else if a.lower > b.upper {
        "above"
    } else {
        "undecided (the enclosures overlap)"
    }
}

/// **The exact difference** of two enclosures, `a − b ∈ [a.lower − b.upper, a.upper − b.lower]`,
/// with its exact endpoints and its reading at the grain.
pub fn difference(a: &ExactInterval, b: &ExactInterval, grain: u64) -> String {
    enclosure(
        &ExactInterval {
            lower: &a.lower - &b.upper,
            upper: &a.upper - &b.lower,
        },
        grain,
    )
}

//! **Exact machine words: the rings the section layout computes in, without the device.**
//!
//! [definition] `ExactRing`, `CheckedIntegers` and `ModularWords` are the exact arithmetic of
//! `crates/holonics-cuda`'s section layout, extracted so a host-only owner (the certified
//! prime-image reading in `holonic-core`) computes in the same ring without linking CUDA. The
//! The CUDA package re-exports every item here (`holonics_cuda::ModularWords`,
//! `holonics_cuda::section_layout::ExactRing`, …), so device code is unchanged.
//!
//! [definition] **One mouth, kept.** At the device modulus `2^61 − 1`, `ModularWords::add`, `mul`,
//! `canonical` and `is_canonical` call `holonics_portable::section_layout_cuda` — the same code
//! `accelerators/cuda-kernel` compiles for nvptx — so "`ModularWords::DEVICE` is literally the
//! device's add/mul" remains a property of one piece of code. The tests below assert it.
//!
//! The refusal vocabulary (`SectionClause`, `SectionRefusal`, `Sectioned`) travels with the ring
//! because `ModularWords::new` and `verify_canonical` refuse in it; the section layout keeps
//! raising the same values.

use std::fmt;

use holonics_portable::section_layout_cuda as section_cuda;

/// The result of a construction that either generates the layout or names the clause it refused.
pub type Sectioned<T> = core::result::Result<T, SectionRefusal>;

// ---------------------------------------------------------------------------------------------
// Clauses and refusals
// ---------------------------------------------------------------------------------------------

/// One named clause of the section-layout law.  A refusal names exactly one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SectionClause {
    /// The global field carries one positive address extent.
    PositiveGlobalExtent,
    /// The global address extent is representable in the `u32` index wire the device reads.
    GlobalExtentWire,
    /// The declaration carries one or more regions.
    PositiveRegions,
    /// The slot population is positive and representable in the `u32` index wire.
    SlotWire,
    /// The offsets table carries one boundary per region plus its end, and starts at zero.
    OffsetsLength,
    /// The offsets table is monotone and every region carries at least one slot.
    RegionWidth,
    /// The offsets table ends exactly at the address table's own length.
    OffsetsEnd,
    /// Every declared global address is below the declared global extent.
    AddressWithinExtent,
    /// A declared extent product does not fit its wire.
    ExtentProduct,
    /// The declared scatter receipt is not the one the incidence supports.
    ScatterReceipt,
    /// The declared accumulation is not an exact ring.
    AccumulationLaw,
    /// The declared accumulation has no device realization.
    AccumulationOnDevice,
    /// The local operator's width is not the declared tile width.
    LocalOperatorWidth,
    /// A presented field or tile does not carry the declared extent.
    SpanExtent,
    /// The exact arithmetic refused: a checked integer sum or product left its wire.
    ExactArithmetic,
    /// A word presented for the device is not the canonical residue of its class in the declared
    /// ring, i.e. it does not lie in `[0, modulus)`.
    CanonicalWord,
    /// A bounded derivation was asked for more work than the caller's declared ceiling admits.
    WorkCeiling,
    /// The generated launch shape could not be derived from the caller's device evidence.
    LaunchDerivation,
    /// A named colour class does not exist in this colouring.
    ColourClass,
    /// The colouring is not proper for this incidence.
    ColouringProper,
    /// The host descriptors used to stage the device tables do not match the descriptors supplied
    /// for enactment.
    TableProvenance,
}

impl SectionClause {
    /// The clause's own name.
    pub const fn name(self) -> &'static str {
        match self {
            SectionClause::PositiveGlobalExtent => "positive-global-extent",
            SectionClause::GlobalExtentWire => "global-extent-wire",
            SectionClause::PositiveRegions => "positive-regions",
            SectionClause::SlotWire => "slot-wire",
            SectionClause::OffsetsLength => "offsets-length",
            SectionClause::RegionWidth => "region-width",
            SectionClause::OffsetsEnd => "offsets-end",
            SectionClause::AddressWithinExtent => "address-within-extent",
            SectionClause::ExtentProduct => "extent-product",
            SectionClause::ScatterReceipt => "scatter-receipt",
            SectionClause::AccumulationLaw => "accumulation-law",
            SectionClause::AccumulationOnDevice => "accumulation-on-device",
            SectionClause::LocalOperatorWidth => "local-operator-width",
            SectionClause::SpanExtent => "span-extent",
            SectionClause::ExactArithmetic => "exact-arithmetic",
            SectionClause::CanonicalWord => "canonical-word",
            SectionClause::WorkCeiling => "work-ceiling",
            SectionClause::LaunchDerivation => "launch-derivation",
            SectionClause::ColourClass => "colour-class",
            SectionClause::ColouringProper => "colouring-proper",
            SectionClause::TableProvenance => "table-provenance",
        }
    }
}

/// A typed construction refusal of the section-layout law, raised before any allocation sized by
/// the refused declaration and before any driver call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SectionRefusal {
    /// The single clause that failed.
    pub clause: SectionClause,
    /// The exact quantities that failed it.
    pub detail: String,
}

impl SectionRefusal {
    /// Name a violated clause.
    pub fn new(clause: SectionClause, detail: impl Into<String>) -> Self {
        Self {
            clause,
            detail: detail.into(),
        }
    }
}

impl fmt::Display for SectionRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "section layout clause `{}` refused: {}",
            self.clause.name(),
            self.detail
        )
    }
}

impl std::error::Error for SectionRefusal {}
fn refuse<T>(clause: SectionClause, detail: impl Into<String>) -> Sectioned<T> {
    Err(SectionRefusal::new(clause, detail))
}

/// **A named exact associative-commutative accumulation.**
///
/// There is deliberately **no floating variant and no room for one**: the Lean owner states every
/// law over a `CommSemiring`, floating addition is not associative, and an accumulating scatter
/// whose addition is not associative is order-dependent again through the back door.  A float
/// accumulation is therefore refused by *type*, not by a check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccumulationLaw {
    /// Exact addition in `ℤ`, carried in `i64`.  A sum or product that leaves the 64-bit wire is a
    /// [`SectionClause::ExactArithmetic`] refusal, never a wrap.  **Host only**: a device kernel has
    /// no way to raise that refusal mid-launch, so `SectionKernels::enact` refuses this law with
    /// [`SectionClause::AccumulationOnDevice`] rather than silently wrapping.
    IntegerAdd,
    /// Exact addition in `Z/modulus`.  Total — every sum and product is exact and in range — which
    /// is why this is the law the device arm realizes.
    ModularAdd {
        /// The modulus.  The device realizes exactly `holonics_portable::section_layout_cuda::MODULUS`.
        modulus: u64,
    },
}

impl AccumulationLaw {
    /// The law's own name, for a receipt line.
    pub fn name(self) -> String {
        match self {
            AccumulationLaw::IntegerAdd => String::from("exact-integer-add"),
            AccumulationLaw::ModularAdd { modulus } => format!("exact-modular-add-{modulus}"),
        }
    }
}

/// **An exact commutative semiring.**  The Lean owner states every law over a `CommSemiring`; this
/// is the executable equivalent, and `Option` is how a *partial* exact ring (checked integers)
/// refuses rather than wraps.  There is no implementor whose addition is inexact.
pub trait ExactRing {
    /// The ring's value type.
    type Value: Copy + PartialEq + Eq + fmt::Debug;

    /// The additive identity.
    fn zero(&self) -> Self::Value;
    /// Exact addition, or `None` when the exact sum leaves the representation.
    fn add(&self, left: Self::Value, right: Self::Value) -> Option<Self::Value>;
    /// Exact multiplication, or `None` when the exact product leaves the representation.
    fn mul(&self, left: Self::Value, right: Self::Value) -> Option<Self::Value>;
    /// The accumulation law this ring's addition realizes.
    fn law(&self) -> AccumulationLaw;
}

/// Exact integers carried in `i64`: total for addition and multiplication **until** the exact
/// result leaves the wire, at which point it refuses.  Host only.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CheckedIntegers;

impl ExactRing for CheckedIntegers {
    type Value = i64;

    fn zero(&self) -> i64 {
        0
    }

    fn add(&self, left: i64, right: i64) -> Option<i64> {
        left.checked_add(right)
    }

    fn mul(&self, left: i64, right: i64) -> Option<i64> {
        left.checked_mul(right)
    }

    fn law(&self) -> AccumulationLaw {
        AccumulationLaw::IntegerAdd
    }
}

/// Exact words of `Z/modulus`, total in both operations.
///
/// At the device's own modulus, `holonics_portable::section_layout_cuda::MODULUS = 2^61 - 1`, the operations
/// **are literally the device's**: [`ExactRing::add`] and [`ExactRing::mul`] call
/// `section_layout_cuda::add` / `::mul`, the same code `accelerators/cuda-kernel` compiles for
/// nvptx.  The bit-for-bit agreement the device tests assert is therefore a property of one piece
/// of code, not of two transcriptions.  At any other modulus the general 128-bit path is used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModularWords {
    modulus: u64,
}

impl ModularWords {
    /// The modulus the device realizes: the Mersenne prime `2^61 - 1`.
    pub const DEVICE: ModularWords = ModularWords {
        modulus: section_cuda::MODULUS,
    };

    /// Words of `Z/modulus`, for a modulus naming a ring with two distinct elements.
    pub fn new(modulus: u64) -> Sectioned<ModularWords> {
        if modulus < 2 {
            return refuse(
                SectionClause::AccumulationLaw,
                format!("a modulus of {modulus} does not name a ring with two distinct elements"),
            );
        }
        Ok(ModularWords { modulus })
    }

    /// The modulus.
    pub const fn modulus(&self) -> u64 {
        self.modulus
    }

    /// The canonical residue of an arbitrary word.
    pub fn canonical(&self, value: u64) -> u64 {
        if self.modulus == section_cuda::MODULUS {
            section_cuda::canonical(value)
        } else {
            value % self.modulus
        }
    }

    /// Whether a word is already the canonical residue of its class, i.e. lies in `[0, modulus)`.
    /// At the device's own modulus the predicate is
    /// [`section_cuda::is_canonical`](holonics_portable::section_layout_cuda::is_canonical) itself, the same
    /// code nvptx compiles, so the boundary and the kernel name one notion of canonical.
    pub fn is_canonical(&self, value: u64) -> bool {
        if self.modulus == section_cuda::MODULUS {
            section_cuda::is_canonical(value)
        } else {
            value < self.modulus
        }
    }

    /// **The canonicality boundary.**  Verify that every word of a table about to be presented to
    /// the device — or folded through this ring's arithmetic — is already the canonical residue of
    /// its class, naming the **first** offending index and the word that offended.
    ///
    /// **Refusal, not reduction, and the reason.**  The section-layout law's default for a
    /// malformed declaration is refusal, not repair: a descending offsets table is refused rather
    /// than sorted, an address past the declared extent is refused rather than clamped, and a
    /// non-canonical word is refused rather than folded.  Two reasons are specific to this
    /// boundary and decide it.
    ///
    /// 1. `SectionDeviceTables::stage` holds only a `&LocalOperator<u64>`.  Reducing would have
    ///    to reduce a *copy*, leaving the caller's own operator — the very operator
    ///    `SectionLayout::apply_reference` reads to produce the exact host comparison — as it
    ///    was.  The bit-for-bit device/host agreement would then be asserted between two different
    ///    declarations, which is precisely the property this owner exists to keep.
    /// 2. A non-canonical coefficient is a caller whose arithmetic already left the ring somewhere
    ///    upstream.  Folding it silently here erases the one place that is observable, which is the
    ///    same failure the narrowing 128-bit fold committed: a wrong answer inside `[0, modulus)`
    ///    that nothing downstream can notice.
    ///
    /// The arithmetic itself does **not** depend on this check.  `section_cuda::add` and
    /// `section_cuda::mul` are total over every pair of `u64` words, so a word that slips past a
    /// mouth this owner does not hold — a `DeviceBuffer` the caller filled itself, an accumulation
    /// target already resident on the card — still yields the exact residue rather than a wrap.
    /// This clause is the declaration's law; totality is the arithmetic's.
    pub fn verify_canonical(&self, values: &[u64], table: &str) -> Sectioned<()> {
        for (at, value) in values.iter().enumerate() {
            if !self.is_canonical(*value) {
                return refuse(
                    SectionClause::CanonicalWord,
                    format!(
                        "{table} entry {at} is {value}, which is not the canonical residue {} of                          its class in Z/{}; a word presented to the device is canonical or refused",
                        self.canonical(*value),
                        self.modulus
                    ),
                );
            }
        }
        Ok(())
    }
}

impl ExactRing for ModularWords {
    type Value = u64;

    fn zero(&self) -> u64 {
        0
    }

    fn add(&self, left: u64, right: u64) -> Option<u64> {
        if self.modulus == section_cuda::MODULUS {
            Some(section_cuda::add(left, right))
        } else {
            Some((((left as u128) + (right as u128)) % (self.modulus as u128)) as u64)
        }
    }

    fn mul(&self, left: u64, right: u64) -> Option<u64> {
        if self.modulus == section_cuda::MODULUS {
            Some(section_cuda::mul(left, right))
        } else {
            Some((((left as u128) * (right as u128)) % (self.modulus as u128)) as u64)
        }
    }

    fn law(&self) -> AccumulationLaw {
        AccumulationLaw::ModularAdd {
            modulus: self.modulus,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Words spanning the canonical range, its boundary and the non-canonical top of `u64`.
    fn words() -> Vec<u64> {
        let modulus = section_cuda::MODULUS;
        let mut words = vec![
            0,
            1,
            2,
            3,
            modulus - 2,
            modulus - 1,
            modulus,
            modulus + 1,
            u64::MAX,
        ];
        let mut state = 0x9e37_79b9_7f4a_7c15_u64;
        for _ in 0..512 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            words.push(state);
            words.push(state % modulus);
        }
        words
    }

    /// **The device ring is the device's code.** At `2^61 − 1` every operation of
    /// `ModularWords::DEVICE` returns exactly what `holonics_portable::section_layout_cuda` returns — the
    /// code nvptx compiles — and that is the exact residue of the integer operation.
    #[test]
    fn the_device_ring_is_literally_the_device_add_and_mul() {
        let ring = ModularWords::DEVICE;
        let modulus = section_cuda::MODULUS;
        assert_eq!(ring.modulus(), modulus);
        assert_eq!(
            ring.law(),
            AccumulationLaw::ModularAdd { modulus },
            "the device ring names the device accumulation"
        );
        let words = words();
        for &left in &words {
            assert_eq!(ring.canonical(left), section_cuda::canonical(left));
            assert_eq!(ring.is_canonical(left), section_cuda::is_canonical(left));
            assert_eq!(ring.canonical(left), left % modulus);
            for &right in words.iter().step_by(7) {
                let sum = ring.add(left, right).expect("total");
                let product = ring.mul(left, right).expect("total");
                assert_eq!(sum, section_cuda::add(left, right));
                assert_eq!(product, section_cuda::mul(left, right));
                let m = u128::from(modulus);
                assert_eq!(u128::from(sum), (u128::from(left) + u128::from(right)) % m);
                assert_eq!(
                    u128::from(product),
                    (u128::from(left) * u128::from(right)) % m
                );
            }
        }
    }

    /// Another modulus takes the general 128-bit path; a degenerate one and a non-canonical word
    /// are refused with their clause.
    #[test]
    fn a_general_modulus_is_exact_and_refusals_name_their_clause() {
        let ring = ModularWords::new(1_000_003).expect("a ring");
        assert_eq!(ring.add(1_000_002, 5), Some(4));
        assert_eq!(ring.mul(1_000_002, 1_000_002), Some(1));
        assert_eq!(
            ModularWords::new(1).unwrap_err().clause,
            SectionClause::AccumulationLaw
        );
        let refusal = ring
            .verify_canonical(&[0, 7, 1_000_003], "probe")
            .unwrap_err();
        assert_eq!(refusal.clause, SectionClause::CanonicalWord);
        assert_eq!(CheckedIntegers.add(i64::MAX, 1), None);
        assert_eq!(CheckedIntegers.mul(3, -4), Some(-12));
    }
}

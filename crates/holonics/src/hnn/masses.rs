//! **The receiving parametron's region class masses, read at the grain** (Decision 27).
//!
//! [definition; agent-inferred] For each admitted receiver region `r`, a certified finite quotient
//! of the receiver's address ([`Regions`]), the receiving parametron stores class masses over the
//! positive Krichevsky–Trofimov prior `α_(r,c) = 1/2` (one per two), deposited only by the
//! comparisons whose covectors reached the receiving locus ([`MassStep`]):
//!
//! ```text
//! storage    C_(r,c) = α + Σ_(i : r_i = r) w_i q_(i,c) ,   q_i = e_(t_i) ,  w_i ≥ 0 ,  α = 1/2
//! face       p_(r,c) = C_(r,c) / N_r ,   N_r = Σ_c C_(r,c)
//! grain      2^k ≤ p^L < 2^(k+1)   (integer comparisons),   k = L n + j ,  0 ≤ j < L
//! combined   Re f_c = k_c/L + Re(R P_R^(τ_R) v_R)_c ,   Im f_c = Im(R P_R^(τ_R) v_R)_c
//! ```
//!
//! **The storage** ([`ClassMasses`]) holds each mass exactly as an integer of half-units, `2C`,
//! and each region's total `2N`: the prior is one half-unit, and a reached comparison of weight `w`
//! adds `2w` half-units at its region and target class. [agent-inferred] Integers of half-units
//! and not Decision 22's carrier lattice: every mass lies on `½ℤ` (the prior is `1/2` and the
//! compose's reached weights are unit), a lattice `2^(−L)ℤ` with `L ≥ 1` would carry every update
//! with no remainder and release nothing (Lean `HNN/RegionCounts.{count_lattice_exact,
//! kt_lattice_exact}`), so the lattice's carry would be the identity on these values, and the
//! integers are its coordinates at `L = 1`. A weight off `½ℤ` or below zero is refused
//! ([`HnnError::MassWeight`]), never rounded. The masses retain no occurrence list: they are the
//! whole standing of the region receiver (`count_future_sufficient`), invariant under a permutation
//! of the past (`regionRun_perm`, `past_permutation_fixture`).
//!
//! **The face** is `p_(r,c) = C_(r,c)/N_r`, positive at every class (`count_face_positive_section`),
//! so a categorical comparison needs no finite logit for its one-hot target. It is read at the
//! receiver's grain `L_R` by exact integer comparison ([`grain_exponent`]): with `p = a/b`, the
//! unique `k` with `2^(k⁺) b^L ≤ 2^(k⁻) a^L` and `2^((k+1)⁻) a^L < 2^((k+1)⁺) b^L`. The count face's
//! grain logits are `k_c/L_R` on the real rows and zero on the imaginary rows ([`CountFace`]); the
//! scored face `θ^(k_c)/Σ_d θ^(k_d)` in `ℚ(θ)` differs from `log₂ p_c` by less than one grain per
//! class (`grain_code_residual`). The unresolved fibre `log₂ p_c − k_c/L_R ∈ [0, 1/L_R)` is not a
//! rational: the comparison pair certifies it, and it is not carried.
//!
//! **The prior decays exactly** (`count_prior_decay`): `p_r = A_r/(A_r+S_r)·α/A_r +
//! S_r/(A_r+S_r)·q̄_r` with `A_r = |A|/2`, `S_r` the weight that reached `r`; the context-free fixed
//! point is the online order-0 face (`context_free_fixed_face`, `count_face_eq_kt`), and at the
//! preceding-cell region it is order-1's.
//!
//! **The combined face** (`combined_face_pullback`, `combined_code_pullback`): the scored logits
//! are the count face's grain logits plus the wave's `R P_R^(τ_R) v_R`. The ratio's covector on the
//! combined face flows back through `R` as the wave-only face's did; the count part is a stored
//! face, carrying no parameter pulled back through `R`, so the rings, contacts and charts learn only
//! what the counts do not already say.
//!
//! | Lean `HNN/RegionCounts` | Rust |
//! |---|---|
//! | `count_step_mass`, `count_step_normalized`, `count_step_covector` | [`ClassMasses::deposit`] |
//! | `count_face_positive_section`, `count_face_eq_kt`, `kt_fixture`, `kt_half_units_normalized` | [`ClassMasses::probability`] |
//! | `count_prior_decay`, `context_free_fixed_face` | [`ClassMasses::prior`] |
//! | `regionRun_local`, `regionRun_perm`, `count_future_sufficient`, `past_permutation_fixture` | [`ClassMasses`] (the masses and nothing else) |
//! | `grainExponent_spec`, `grain_log_iff_pow_bounds`, `grain_face_residual`, `grain_code_residual`, `grain_fixture` | [`grain_exponent`], [`CountFace`] |
//! | `count_lattice_accounting`, `count_lattice_exact`, `kt_lattice_exact` | the half-unit integers (module header) |
//! | `combined_face_pullback`, `combined_code_pullback` | [`CountFace::logits`], read by `hnn::receiving::ReceivingRead::combined` |

use num_bigint::{BigInt, BigUint};
use num_traits::{Signed, ToPrimitive, Zero};

use crate::hnn::HnnError;
use crate::hnn::ratio::Face;
use crate::hnn::receiving::ReceivingRead;
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;

/// [definition] **The prior mass in half-units**: `2α = 1`, the Krichevsky–Trofimov mass `α = 1/2`.
pub const PRIOR_HALF_UNITS: u64 = 1;

/// [definition] **The prior mass** `α = 1/2` (Lean `HNN/RegionCounts.ktPrior`).
pub fn prior() -> Rat {
    Rat::new(BigInt::from(PRIOR_HALF_UNITS), BigInt::from(2))
}

// -------------------------------------------------------------------------------------------
// the region partition

/// [definition; agent-inferred] **An admitted receiver's region partition**: a certified finite
/// quotient of the receiver's address, which a receiving read computes from the pending ratio's
/// retained operands alone (no target of its own window enters it).
///
/// - `Whole`: one region, the context-free receiver; its count face is the online order-0 face.
/// - `PrecedingCell`: the retained window's preceding cell, `window[δ − 1]` at `δ = 1` in the
///   moment's convention (Lean `HNN/Moment.SourceDecl.ingest`, most recent first;
///   `SourceMoment::window`), the cell before the receiving window; region `1 + a` for the cell `a`,
///   and the declared **empty-window region** `0` when the window holds no cell (at the cut's
///   start). Every receiving phase of a window reads the region of the window's preceding cell,
///   and deposits there: at aperture `A = 1` the storage is the online order-1 table exactly; at
///   `A > 1` phase `j` reads and deposits at the cell `j + 1` back of its target (the cells between
///   are the window's own targets, which no read of the window retains), so the table pools the
///   lags `1 … A`. It needs a retained window: a field that declares it declares a positive offset
///   (`Field::declare` refuses it otherwise, [`HnnError::RegionWindow`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Regions {
    Whole,
    PrecedingCell,
}

impl Regions {
    /// The number of regions over `|A|` classes: `1`, or `|A| + 1`.
    pub fn count(&self, alphabet: usize) -> usize {
        match self {
            Regions::Whole => 1,
            Regions::PrecedingCell => alphabet + 1,
        }
    }

    /// **The region of a receiver's address**: the retained window (most recent first, as
    /// `SourceMoment::window` returns it) read through the partition. Refused when the window's
    /// cell lies outside the exterior chart.
    pub fn region(&self, window: &[Option<usize>], alphabet: usize) -> Result<usize, HnnError> {
        match self {
            Regions::Whole => Ok(0),
            Regions::PrecedingCell => match window.first().copied().flatten() {
                None => Ok(0),
                Some(code) if code < alphabet => Ok(1 + code),
                Some(code) => Err(HnnError::CellOutside { code, alphabet }),
            },
        }
    }

    /// The partition's code in the field's description: `0` for the whole, `1` for the preceding
    /// cell with the empty-window region.
    pub fn code(&self) -> u64 {
        match self {
            Regions::Whole => 0,
            Regions::PrecedingCell => 1,
        }
    }
}

// -------------------------------------------------------------------------------------------
// the storage

/// [definition] **One reached comparison's deposit at the receiving parametron**: its ring, its
/// region, its target class `t` (the class `q = p̃ + g = e_t` its reached covector reconstructs,
/// Lean `count_step_covector`) and its weight `w ≥ 0` on `½ℤ`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MassStep {
    pub ring: usize,
    pub region: usize,
    pub class: usize,
    pub weight: Rat,
}

/// [definition] **The receiving parametron's region class masses** (module header): each mass
/// `C_(r,c)` and each region's total `N_r` as integers of half-units. Only [`ClassMasses::deposit`]
/// changes them, and the constitution calls it only on a staged deposit's reached comparisons.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassMasses {
    regions: Regions,
    classes: usize,
    /// `2C_(r,c)`, row-major `region × class`.
    masses: Vec<u64>,
    /// `2N_r = Σ_c 2C_(r,c)`.
    totals: Vec<u64>,
}

impl ClassMasses {
    /// **The prior masses** over a partition and `|A|` classes: every `C_(r,c) = α = 1/2`, so every
    /// `N_r = |A|/2` and the face is uniform.
    pub fn prior(regions: Regions, classes: usize) -> Self {
        let count = regions.count(classes);
        Self {
            regions,
            classes,
            masses: vec![PRIOR_HALF_UNITS; count * classes],
            totals: vec![PRIOR_HALF_UNITS * classes as u64; count],
        }
    }

    /// The declared partition.
    pub fn regions(&self) -> Regions {
        self.regions
    }

    /// `|A|`.
    pub fn classes(&self) -> usize {
        self.classes
    }

    /// The number of regions.
    pub fn region_count(&self) -> usize {
        self.totals.len()
    }

    fn check(&self, region: usize, class: usize) -> Result<usize, HnnError> {
        if region >= self.totals.len() {
            return Err(HnnError::Shape {
                what: "a region of the receiving parametron's partition",
                expected: self.totals.len(),
                found: region,
            });
        }
        if class >= self.classes {
            return Err(HnnError::CellOutside {
                code: class,
                alphabet: self.classes,
            });
        }
        Ok(region * self.classes + class)
    }

    /// `2C_(r,c)`.
    pub fn half_units(&self, region: usize, class: usize) -> Result<u64, HnnError> {
        Ok(self.masses[self.check(region, class)?])
    }

    /// `2N_r`.
    pub fn total_half_units(&self, region: usize) -> Result<u64, HnnError> {
        self.check(region, 0)?;
        Ok(self.totals[region])
    }

    /// `C_(r,c)`, exact.
    pub fn mass(&self, region: usize, class: usize) -> Result<Rat, HnnError> {
        Ok(half(self.half_units(region, class)?))
    }

    /// `N_r`, exact.
    pub fn total(&self, region: usize) -> Result<Rat, HnnError> {
        Ok(half(self.total_half_units(region)?))
    }

    /// **The face** `p_(r,c) = C_(r,c)/N_r`, exact in lowest terms (the half-units cancel).
    pub fn probability(&self, region: usize, class: usize) -> Result<Rat, HnnError> {
        Ok(Rat::new(
            BigInt::from(self.half_units(region, class)?),
            BigInt::from(self.total_half_units(region)?),
        ))
    }

    /// **One reached comparison's deposit** (Lean `count_step_mass`): `C_(r,t) += w`, `N_r += w`, in
    /// half-units `+2w`. Refused before anything moves at a region or class outside the storage, a
    /// weight below zero or off `½ℤ` ([`HnnError::MassWeight`]), or a count past the machine word.
    /// A zero weight moves nothing.
    pub fn deposit(&mut self, step: &MassStep) -> Result<(), HnnError> {
        let entry = self.check(step.region, step.class)?;
        let doubled = &step.weight * Rat::from_integer(BigInt::from(2));
        if step.weight.is_negative() || !doubled.is_integer() {
            return Err(HnnError::MassWeight {
                weight: step.weight.clone(),
            });
        }
        let added = doubled
            .to_integer()
            .to_u64()
            .ok_or(HnnError::CountOverflow)?;
        if added == 0 {
            return Ok(());
        }
        let mass = self.masses[entry]
            .checked_add(added)
            .ok_or(HnnError::CountOverflow)?;
        let total = self.totals[step.region]
            .checked_add(added)
            .ok_or(HnnError::CountOverflow)?;
        self.masses[entry] = mass;
        self.totals[step.region] = total;
        Ok(())
    }

    /// **The count face's grain exponents** of one region at grain `L`: `k_c` with
    /// `2^(k_c) ≤ p_(r,c)^L < 2^(k_c+1)` ([`grain_exponent`] on the half-unit integers).
    pub fn grain_exponents(&self, region: usize, grain: u64) -> Result<Vec<BigInt>, HnnError> {
        let total = BigUint::from(self.total_half_units(region)?);
        (0..self.classes)
            .map(|class| {
                grain_exponent(
                    &BigUint::from(self.half_units(region, class)?),
                    &total,
                    grain,
                )
            })
            .collect()
    }

    /// **The masses' exact bits**: every `C_(r,c)` by its numerator's and denominator's bits (an
    /// odd count of half-units is `(2C)/2`, an even one the integer `C`). The totals are the
    /// masses' sums, a reading kept beside them, and are not counted.
    pub fn bits(&self) -> u64 {
        self.masses
            .iter()
            .map(|&units| {
                if units % 2 == 1 {
                    u64::from(u64::BITS - units.leading_zeros()) + 2
                } else {
                    u64::from(u64::BITS - (units / 2).leading_zeros()).max(1) + 1
                }
            })
            .sum()
    }

    /// **The mass deposited since the prior**: `Σ_r (N_r − |A|/2)`, exact (the reached weight).
    pub fn deposited_mass(&self) -> Rat {
        let prior = PRIOR_HALF_UNITS * self.classes as u64;
        let units: u64 = self.totals.iter().map(|total| total - prior).sum();
        half(units)
    }
}

fn half(units: u64) -> Rat {
    Rat::new(BigInt::from(units), BigInt::from(2))
}

// -------------------------------------------------------------------------------------------
// the grain

/// [definition] **The grain exponent of a positive ratio `a/b` at grain `L`** (Lean
/// `HNN/RegionCounts.{grainExponent_spec, grain_log_iff_pow_bounds}`): the unique integer `k` with
/// `2^k ≤ (a/b)^L < 2^(k+1)`, decided by the natural-number comparisons
/// `2^(k⁺) b^L ≤ 2^(k⁻) a^L` and `2^((k+1)⁻) a^L < 2^((k+1)⁺) b^L` (`k⁺ = max(k, 0)`,
/// `k⁻ = max(−k, 0)`). The bit lengths of `a^L` and `b^L` place `k` within one of its value, and one
/// comparison decides it. Refused at a zero numerator or denominator (no finite exponent).
pub fn grain_exponent(
    numerator: &BigUint,
    denominator: &BigUint,
    grain: u64,
) -> Result<BigInt, HnnError> {
    if numerator.is_zero() || denominator.is_zero() {
        return Err(HnnError::Shape {
            what: "a positive ratio read at the grain",
            expected: 1,
            found: 0,
        });
    }
    let power = u32::try_from(grain).map_err(|_| HnnError::Shape {
        what: "a receiver's grain within 32 bits",
        expected: u32::MAX as usize,
        found: usize::MAX,
    })?;
    let (a, b) = (numerator.pow(power), denominator.pow(power));
    // `2^(bits(a) − 1) ≤ a < 2^bits(a)`, likewise `b`: `a/b ∈ (2^(d−1), 2^(d+1))`, `d = bits(a) − bits(b)`.
    let d = BigInt::from(a.bits()) - BigInt::from(b.bits());
    let k = if at_least(&a, &b, &d) { d } else { d - 1 };
    debug_assert!(at_least(&a, &b, &k) && !at_least(&a, &b, &(&k + 1)));
    Ok(k)
}

/// `2^k ≤ a/b`, as `2^(k⁺) b ≤ 2^(k⁻) a`.
fn at_least(a: &BigUint, b: &BigUint, k: &BigInt) -> bool {
    let shift = k
        .magnitude()
        .to_usize()
        .expect("a grain exponent within the machine word");
    if k.is_negative() {
        b <= &(a << shift)
    } else {
        &(b << shift) <= a
    }
}

// -------------------------------------------------------------------------------------------
// the count face

/// [definition] **The count face of one region at the receiver's grain**: the region read, the
/// grain `L_R` and each class's grain exponent `k_c` ([`grain_exponent`]). Its grain logits are
/// `k_c/L_R` on the real rows and zero on the imaginary rows ([`CountFace::logits`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CountFace {
    region: usize,
    grain: u64,
    exponents: Vec<BigInt>,
}

impl CountFace {
    /// **Read one region's masses at a grain.**
    pub fn read(masses: &ClassMasses, region: usize, grain: u64) -> Result<Self, HnnError> {
        Ok(Self {
            region,
            grain,
            exponents: masses.grain_exponents(region, grain)?,
        })
    }

    /// The region read.
    pub fn region(&self) -> usize {
        self.region
    }

    /// `L_R`.
    pub fn grain(&self) -> u64 {
        self.grain
    }

    /// The grain exponents `k_c`.
    pub fn exponents(&self) -> &[BigInt] {
        &self.exponents
    }

    /// Each class's carry and phase class `(⌊k_c/L_R⌋, k_c mod L_R)` (Lean `carryPhase`).
    pub fn cells(&self) -> Vec<(BigInt, u64)> {
        let grain = BigInt::from(self.grain);
        self.exponents
            .iter()
            .map(|k| {
                let mut carry = k / &grain;
                let mut phase = k % &grain;
                if phase.is_negative() {
                    carry -= 1;
                    phase += &grain;
                }
                (
                    carry,
                    phase.to_u64().expect("a phase class lies in ℤ/grain"),
                )
            })
            .collect()
    }

    /// **The grain logits**, realified `[k_0/L_R, 0, k_1/L_R, 0, …]` (Lean `grainLogits`).
    pub fn logits(&self) -> Vec<Rat> {
        let grain = BigInt::from(self.grain);
        self.exponents
            .iter()
            .flat_map(|k| [Rat::new(k.clone(), grain.clone()), Rat::zero()])
            .collect()
    }

    /// **The count face alone's code length** `−log₂ p̂(c)` of one class, enclosed: the scored face
    /// of the grain logits alone, `θ^(k_c)/Σ_d θ^(k_d)` in `ℚ(θ)` (`hnn::ratio::Face`).
    pub fn code_length(&self, class: usize) -> Result<ExactInterval, HnnError> {
        let read = ReceivingRead::of_logits(self.logits(), self.grain);
        Face::of_read(&read, self.grain)?.code_length(class)
    }
}

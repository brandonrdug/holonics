//! **The Holon ratio at the receiver's face, and the carried power.**
//!
//! [definition] The loss is the logarithm of a ratio of Holons (design (a), `compare`; "Exact
//! charts"). At receiving phase `j` the produced Holon `|H⟩` is the logit vector
//! `f_j = R P_R^(τ_R) v_R(e_j)` and the target `|T⟩` is the byte `t_j` read in the same exterior
//! chart that `E` reads: the one-hot `q_j`, with the receiving ring's clock `τ_R(j)` advanced by
//! selective stepping over the targets. Both phases are read in the cut's frame: the target's is
//! `φ^T_j = (τ_R(j) − d_R w)/d_R` turns with `w = ⌊λ_R/d_R⌋` the cut's winding, which is the log's
//! branch ([`TargetPhases`]). The produced side reads only a phase class through `P_R^(τ_R)` and
//! represents no stream winding, so the winding is carried as the branch and never descended on,
//! and the gap stays at the scale of the magnitude part (review C1: the absolute `τ_R/d_R` reached
//! 521 turns over 40,000 cells). Their ratio at the target class is
//!
//! ```text
//! ℓ_j = log R_j ,   R_j = Ĝ_(T←H) ,   Re ℓ_j = −log₂ p̂_j(t_j)  (the KL part, bits)
//!                                    Im ℓ_j = w + Δ ,  Δ = φ^T − φ^H_t  (turns; w + ⌊Δ⌋ the branch)
//! p̂_c = 2^(n_c + k_c/L) / Σ_d 2^(n_d + k_d/L)       the face, exact in ℚ(θ), θ^L = 2
//! ```
//!
//! [definition] **The carried power** is its owner's ([`CarriedPower`] and [`PhaseField`] in
//! [`crate::ratio::exponentiated`], design addition 4, Lean `Objects/Ratio/CarriedPower`):
//! `2^(n + k/L) = 2^n θ^k`, a carry `n` (an exact shift) and a phase class `k ∈ ℤ/L`, whose phase
//! carry is multiplication by 2. `ℚ(θ)` is a field, so the face normalizes by exact division there
//! ([`Face::mass`]). The real chart `θ ↦ 2^(1/L)` is read only as an [`ExactInterval`] enclosure,
//! an exterior face: every code length and every bit total is a certified set, never a float.
//!
//! [definition; agent-inferred] **The covector's odometer chart** (design (a), "Exact charts"). The
//! word's return and the deposited constitution are rational (the forward reads `Θ` over ℚ).
//! `ℚ(θ)` has no ring map to ℚ (`X^L − 2` is irreducible), so a covector in `ℚ(θ)` cannot be pulled
//! back into a rational constitution without a declared chart. The learning face is therefore the
//! **odometer chart** of the carried power, `2^(n + k/L) ↦ 2^n (1 + k/L)`: exact at every carry,
//! continuous across it (`2^n · 2 = 2^(n+1) · 1`), monotone in the logit, and rational. Its
//! magnitude part is `p̃ − q` with `p̃_c ∝ 2^(n_c)(L + k_c)`; its phase part is `−½ q_c Δ_c` on
//! `Im f_c` (`−q_c Δ_c` on `φ^H_c = Im f_c / 2`). It is not the face's derivative (the face is
//! constant on each grain cell, so its own derivative vanishes almost everywhere). It is a strict
//! descent direction of the scored code length, whose logit gradient is `p̂ − q`:
//! `⟨p̂ − q, p̃ − q⟩ = Σ_(c≠t) p̂_c p̃_c + (1 − p̂_t)(1 − p̃_t) > 0` (Lean
//! `HNN/Ratio.odometer_covector_descends`). At an integer cell (`k = 0`) the chart is the face
//! (`odometer_eq_face_at_integer_cells`), and at `L = 1` the two agree everywhere; elsewhere its
//! weights lie within the factor `max_x (1 + x)/2^x ≈ 1.0615` of the face's, a reading. The face
//! `p̂` that is read, reported and scored stays exact in `ℚ(θ)`.
//!
//! | Lean `HNN/Ratio` | Rust |
//! |---|---|
//! | `Objects/Ratio/CarriedPower.{carriedPower_exact, theta_pow, irreducible_X_pow_sub_two, realChart}` (the owner's) | [`CarriedPower`], [`PhaseField`] |
//! | `face_constant_on_fibre`, `face_code_length_within_grain`, `codeLength_eq_face` | [`Face`], [`Face::code_length`] |
//! | `receivingPhase_ratio` (a common rechart leaves `ℓ`) | [`HolonRatio::compare`] |
//! | `alignCost_turns` (the windowed gap in turns; the cut's winding the branch) | [`target_phases`], [`PhaseRatio`] |
//! | `odometer_covector_descends`, `odometer_eq_face_at_integer_cells` (the magnitude part); `receivingPhase_phase_pullback` (the phase part) | [`RatioCovector`], [`Face::odometer_masses`] |
//! | `Objects/Ratio.logFibre` (the undivided pair with its winding) | [`HolonRatio::log_ratio`] |
//! | `HNN/TargetFace.{finite_chart_obstruction, MarginCodes, margin_rule_codeLength, marginLeast, margin_campaign_one, codeFace}` (Decision 26) | [`code_margin`], [`code_face`] |
//!
//! [definition; agent-inferred] **The target's code face** (Decision 26). A one-hot target `q_t` has
//! no finite logit: every finite logit vector gives every class positive mass. The receiver
//! therefore declares a finite, gauge-fixed chart of the target Holon at its grain,
//! `χ_R(T) = m·e_t` in the realified logits (`Re f_t = m`, every other entry `0`: the common shift
//! fixed by the classes the target does not name, the phase part zero), with the **margin** `m` the
//! least integer whose face codes the target within the receiver's tolerance of one grain per cell:
//!
//! ```text
//! p̂_t(χ) = 2^m / (2^m + |A| − 1),   −log₂ p̂_t(χ) ≤ 1/L_R   ⇔   (2^m + |A| − 1)^(L_R) ≤ 2^(m·L_R + 1)
//! ```
//!
//! read in exact integers ([`code_margin`]; `m = 13` at `|A| = 2^8`, `L_R = 2^4`). It is the
//! exogenous side of the receiving map's normal law (`hnn::constitution::NormalLaw::exogenous`),
//! whose loss is the squared additive-chart log ratio `½|χ_R(T) − f|²`, named as such: descent of
//! the cross-entropy face is not claimed by it (the exposure's receipt decides).

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::aeon::Reading;
use crate::hnn::HnnError;
use crate::hnn::field::{Field, phase_winding};
use crate::hnn::realization::indexed;
use crate::hnn::receiving::{GrainCell, ReceivingRead};
use crate::ratio::algebraic::{ExactInterval, natural_log_enclosure};
use crate::ratio::exponentiated::{CarriedPower, PhaseField, READING_BITS, power_of_two};
use crate::ratio::gaussian::GaussianRat;
use crate::ratio::{LogRatio, Rat, integer};

/// The series terms and dyadic octaves of a logarithm's enclosure.
const LOG_TERMS: u32 = 48;
const LOG_OCTAVES: u32 = 96;

// -------------------------------------------------------------------------------------------
// enclosures of the real chart

/// **`2^x` of a rational, enclosed**: `2^⌊x⌋ · 2^(a/b)` with `a/b` the fractional part, its root
/// bounded by an exact integer `b`-th root at [`READING_BITS`]. A reading, never a law's value.
pub fn power_of_two_enclosure(x: &Rat) -> Result<ExactInterval, HnnError> {
    let floor = x.floor().to_integer();
    let fraction = x - Rat::from_integer(floor.clone());
    let scale = power_of_two(&floor)?;
    if fraction.is_zero() {
        return Ok(ExactInterval::point(scale));
    }
    let (a, b) = (
        fraction
            .numer()
            .to_biguint()
            .expect("a fraction is nonnegative"),
        fraction.denom().to_u32().ok_or(HnnError::Shape {
            what: "a logit's denominator (the root's degree)",
            expected: u32::MAX as usize,
            found: usize::MAX,
        })?,
    );
    let bits = u64::from(READING_BITS);
    let exponent = a
        .to_u64()
        .expect("a fraction's numerator lies below its denominator")
        + bits * u64::from(b);
    let target = BigUint::one() << exponent as usize;
    let root = target.nth_root(b);
    let unit = Rat::new(BigInt::one(), BigInt::one() << READING_BITS as usize);
    let lower = Rat::from_integer(BigInt::from(root.clone())) * &unit;
    let upper = if root.pow(b) == target {
        lower.clone()
    } else {
        Rat::from_integer(BigInt::from(root + 1u32)) * &unit
    };
    interval(&scale * lower, &scale * upper)
}

fn interval(lower: Rat, upper: Rat) -> Result<ExactInterval, HnnError> {
    ExactInterval::new(lower, upper).map_err(|_| HnnError::Shape {
        what: "an ordered enclosure",
        expected: 0,
        found: 1,
    })
}

/// **`log₂` of a positive rational, enclosed** without factoring: `ln x / ln 2`, each enclosed by
/// the crate's series and divided outward. Exact (a point) on powers of two.
pub fn log2_enclosure(value: &Rat) -> Result<ExactInterval, HnnError> {
    if !value.is_positive() {
        return Err(HnnError::Shape {
            what: "a positive argument of log2",
            expected: 1,
            found: 0,
        });
    }
    if let (Some(n), Some(d)) = (
        value.numer().to_biguint().filter(|n| n.count_ones() == 1),
        value.denom().to_biguint().filter(|d| d.count_ones() == 1),
    ) {
        let exponent = BigInt::from(n.bits()) - BigInt::from(d.bits());
        return Ok(ExactInterval::point(Rat::from_integer(exponent)));
    }
    let natural =
        natural_log_enclosure(value, LOG_TERMS, LOG_OCTAVES).map_err(|_| HnnError::Shape {
            what: "a logarithm's enclosure",
            expected: 1,
            found: 0,
        })?;
    let two = ln_two()?;
    let candidates = [
        &natural.lower / &two.lower,
        &natural.lower / &two.upper,
        &natural.upper / &two.lower,
        &natural.upper / &two.upper,
    ];
    let lower = candidates.iter().min().expect("four candidates").clone();
    let upper = candidates.iter().max().expect("four candidates").clone();
    round_out(interval(lower, upper)?)
}

/// `ln 2`'s enclosure at the declared series terms and octaves: a constant of the reading, formed
/// once.
fn ln_two() -> Result<&'static ExactInterval, HnnError> {
    static LN_TWO: std::sync::OnceLock<Option<ExactInterval>> = std::sync::OnceLock::new();
    LN_TWO
        .get_or_init(|| natural_log_enclosure(&integer(2), LOG_TERMS, LOG_OCTAVES).ok())
        .as_ref()
        .ok_or(HnnError::Shape {
            what: "ln 2's enclosure",
            expected: 1,
            found: 0,
        })
}

/// `log₂` of an enclosed positive value: monotone, so the bounds' logarithms bound it.
pub fn log2_of_enclosure(value: &ExactInterval) -> Result<ExactInterval, HnnError> {
    let lower = log2_enclosure(&value.lower)?;
    let upper = log2_enclosure(&value.upper)?;
    interval(lower.lower, upper.upper)
}

/// The sum of two enclosures, held outward on the dyadic grid of the log octaves.
pub fn interval_sum(a: &ExactInterval, b: &ExactInterval) -> Result<ExactInterval, HnnError> {
    round_out(interval(&a.lower + &b.lower, &a.upper + &b.upper)?)
}

/// `a − b` of two enclosures.
pub fn interval_difference(
    a: &ExactInterval,
    b: &ExactInterval,
) -> Result<ExactInterval, HnnError> {
    round_out(interval(&a.lower - &b.upper, &a.upper - &b.lower)?)
}

fn round_out(value: ExactInterval) -> Result<ExactInterval, HnnError> {
    value.round_out(LOG_OCTAVES).map_err(|_| HnnError::Shape {
        what: "an ordered enclosure",
        expected: 0,
        found: 1,
    })
}

// -------------------------------------------------------------------------------------------
// the target's code face

/// **The receiver's declared margin** (module header): the least `m ≥ 0` with
/// `(2^m + |A| − 1)^(L_R) ≤ 2^(m·L_R + 1)`, decided in exact integers. The left side falls toward
/// `2^(m·L_R)` as `m` grows, so the least `m` exists for every alphabet and grain.
pub fn code_margin(alphabet: usize, grain: u64) -> u64 {
    let others = BigUint::from(alphabet.saturating_sub(1));
    let grain = u32::try_from(grain.max(1)).expect("a receiver's grain within 32 bits");
    let mut margin = 0u64;
    loop {
        let face = ((BigUint::one() << margin as usize) + &others).pow(grain);
        let bound = BigUint::one() << (margin * u64::from(grain) + 1) as usize;
        if face <= bound {
            return margin;
        }
        margin += 1;
    }
}

/// **The target's code face `χ_R(T) = m·e_t`** in the realified logits `[Re f_0, Im f_0, …]` over
/// `alphabet` classes (module header): `m` at `Re f_t`, zero elsewhere.
pub fn code_face(margin: u64, class: usize, alphabet: usize) -> Result<Vec<Rat>, HnnError> {
    if class >= alphabet {
        return Err(HnnError::CellOutside {
            code: class,
            alphabet,
        });
    }
    let mut face = vec![Rat::zero(); 2 * alphabet];
    face[2 * class] = Rat::from_integer(BigInt::from(margin));
    Ok(face)
}

// -------------------------------------------------------------------------------------------
// the face

/// [definition] **The face at one receiving phase**: each class's grain cell `(n_c, k_c)` with its
/// fibre `ε_c`, its produced phase `φ^H_c = Im f_c / 2` in turns, and the normalizer
/// `Z = Σ_c 2^(n_c − n_top) θ^(k_c)` in `ℚ(θ)` (`n_top` the largest carry, so `Z ≥ 1`). The exact face
/// is `p̂_c = 2^(n_c − n_top) θ^(k_c) / Z`; it reads only the cells (Lean
/// `HNN/Ratio.face_constant_on_fibre`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Face {
    grain: u64,
    cells: Vec<GrainCell>,
    phases: Vec<Rat>,
    top: BigInt,
    normalizer: PhaseField,
}

impl Face {
    /// The face of one receiving read at grain `L_R`.
    pub fn of_read(read: &ReceivingRead, grain: u64) -> Result<Self, HnnError> {
        if read.cells.is_empty() {
            return Err(HnnError::Shape {
                what: "a face over at least one class",
                expected: 1,
                found: 0,
            });
        }
        let top = read
            .cells
            .iter()
            .map(|cell| cell.carry.clone())
            .max()
            .expect("at least one class");
        let mut normalizer = PhaseField::zero(grain);
        for cell in &read.cells {
            normalizer = normalizer
                .plus(&CarriedPower::new(&cell.carry - &top, cell.phase, grain)?.value()?)?;
        }
        Ok(Self {
            grain,
            cells: read.cells.clone(),
            phases: read.phases.clone(),
            top,
            normalizer,
        })
    }

    /// `L_R`.
    pub fn grain(&self) -> u64 {
        self.grain
    }

    /// The classes' grain cells.
    pub fn cells(&self) -> &[GrainCell] {
        &self.cells
    }

    /// The receiver's fibre `ε_c` per class, returned and never consumed as a value.
    pub fn fibres(&self) -> Vec<Rat> {
        self.cells.iter().map(|cell| cell.fibre.clone()).collect()
    }

    /// `φ^H_c` in turns.
    pub fn phases(&self) -> &[Rat] {
        &self.phases
    }

    /// The normalizer `Z` in `ℚ(θ)`.
    pub fn normalizer(&self) -> &PhaseField {
        &self.normalizer
    }

    fn carried(&self, class: usize) -> Result<CarriedPower, HnnError> {
        let cell = self.cells.get(class).ok_or(HnnError::CellOutside {
            code: class,
            alphabet: self.cells.len(),
        })?;
        Ok(CarriedPower::new(
            &cell.carry - &self.top,
            cell.phase,
            self.grain,
        )?)
    }

    /// **The exact mass `p̂_c`** in `ℚ(θ)`.
    pub fn mass(&self, class: usize) -> Result<PhaseField, HnnError> {
        Ok(self
            .carried(class)?
            .value()?
            .times(&self.normalizer.inverse()?)?)
    }

    /// **The code length `−log₂ p̂_c`**, enclosed: `log₂ Z − (n_c − n_top) − k_c/L`.
    pub fn code_length(&self, class: usize) -> Result<ExactInterval, HnnError> {
        let carried = self.carried(class)?;
        let offset = Rat::from_integer(carried.carry().clone())
            + Rat::new(BigInt::from(carried.phase()), BigInt::from(self.grain));
        let log_normalizer = match self.normalizer.as_rational() {
            Some(value) => log2_enclosure(value)?,
            None => log2_of_enclosure(&self.normalizer.enclosure()?)?,
        };
        interval_difference(&log_normalizer, &ExactInterval::point(offset))
    }

    /// **The odometer masses** `p̃_c = 2^(n_c)(L + k_c) / Σ_d 2^(n_d)(L + k_d)`: the covector's
    /// rational chart of the face (module header). They sum to one exactly.
    pub fn odometer_masses(&self) -> Result<Vec<Rat>, HnnError> {
        let weights: Vec<Rat> = (0..self.cells.len())
            .map(|class| Ok(self.carried(class)?.odometer()?))
            .collect::<Result<_, HnnError>>()?;
        let total: Rat = weights.iter().sum();
        Ok(weights.iter().map(|weight| weight / &total).collect())
    }
}

/// [definition] **The faces `p̂_j` of one receiving window**, one per receiving phase, with their
/// fibres: what `refine` publishes (design (c), `Faces`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Faces {
    pub faces: Vec<Face>,
    /// The exact logits `f_j` behind each face (realified `[Re, Im, …]`), a reading of the word.
    pub logits: Vec<Vec<Rat>>,
}

impl Faces {
    /// The faces of the receiving reads at grain `L_R`.
    pub fn of_reads(reads: &[ReceivingRead], grain: u64) -> Result<Self, HnnError> {
        Ok(Self {
            faces: indexed(reads.len(), |j| Face::of_read(&reads[j], grain))?,
            logits: reads.iter().map(|read| read.logits.clone()).collect(),
        })
    }
}

// -------------------------------------------------------------------------------------------
// the target's phase

/// [definition] **The target phases of one window, read in the cut's frame** (Lean
/// `HNN/Ratio.alignCost_turns`): the receiving ring's winding at the anchor, `w = ⌊λ_R/d_R⌋`, which
/// is the log's branch, and `φ^T_j = (τ_R(j) − d_R w)/d_R` turns per receiving phase.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetPhases {
    pub branch: BigInt,
    pub phases: Vec<Rat>,
}

/// **The target phases** of a window: the receiving ring's lift from the anchor `λ`, advanced by
/// selective stepping over `t_0 … t_j` (with carries, as ingest would, without ingesting), read
/// relative to the cut's winding `w = ⌊λ_R/d_R⌋`, which is returned as the branch. Each phase lies
/// in `[0, 1 + 2(j+1)/d_R)`, the anchor's open phase plus at most two ticks a cell (a step and a
/// carry), however long the stream before the cut.
pub fn target_phases(
    field: &Field,
    anchor: &[BigInt],
    ring: usize,
    targets: &[usize],
) -> Result<TargetPhases, HnnError> {
    let period = field
        .rings()
        .get(ring)
        .ok_or(HnnError::RingOutside {
            ring,
            rings: field.rings().len(),
        })?
        .period();
    let at = anchor.get(ring).ok_or(HnnError::Shape {
        what: "lift point",
        expected: field.rings().len(),
        found: anchor.len(),
    })?;
    let (_, branch) = phase_winding(at, period);
    let floor = &branch * BigInt::from(period);
    let mut lift = anchor.to_vec();
    let phases = targets
        .iter()
        .map(|&code| {
            field.selective_step(&mut lift, code)?;
            Ok(Rat::new(&lift[ring] - &floor, BigInt::from(period)))
        })
        .collect::<Result<_, HnnError>>()?;
    Ok(TargetPhases { branch, phases })
}

// -------------------------------------------------------------------------------------------
// the Holon ratio

/// [definition] **The ratio at one receiving phase** at its target class `t`: the target's phase
/// `φ^T` in the cut's frame, the produced phase `φ^H_t`, the windowed gap `Δ = φ^T − φ^H_t` read as
/// its windings and open phase ([`Reading`]), the cut's winding `w` as the branch, never descended
/// on (Lean `HNN/Ratio.alignCost_turns`), the code length `−log₂ p̂(t)` (the KL part against the
/// one-hot target, enclosed), and the phase excess `½ Δ²` exactly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PhaseRatio {
    pub target: usize,
    pub target_phase: Rat,
    pub produced_phase: Rat,
    pub gap: Reading,
    pub branch: BigInt,
    pub code_length: ExactInterval,
    pub excess: Rat,
}

impl PhaseRatio {
    /// The log's whole winding `n` in `Im ℓ = n + open phase`: the cut's winding plus the windowed
    /// gap's own windings.
    pub fn winding(&self) -> BigInt {
        &self.branch + self.gap.windings()
    }
}

/// [definition] **The Holon ratio `R_j = Ĝ_(T←H)` over a receiving window**: the contemporary faces
/// and, per phase, the ratio at its target class. Only it constructs a [`RatioCovector`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HolonRatio {
    faces: Faces,
    phases: Vec<PhaseRatio>,
}

impl HolonRatio {
    /// **Compare the produced faces with the targets** `(t_j, φ^T_j)`, one per receiving phase,
    /// the target phases read in the cut's frame with its winding the branch.
    pub fn compare(
        faces: Faces,
        targets: &[usize],
        target_phases: &TargetPhases,
    ) -> Result<Self, HnnError> {
        let TargetPhases {
            branch,
            phases: target_phases,
        } = target_phases;
        if targets.len() != faces.faces.len() || target_phases.len() != targets.len() {
            return Err(HnnError::Shape {
                what: "targets per receiving phase",
                expected: faces.faces.len(),
                found: targets.len(),
            });
        }
        // Each receiving phase reads only its own face and target: the phases run together.
        let phases = indexed(targets.len(), |j| {
            let (face, target, target_phase) = (&faces.faces[j], targets[j], &target_phases[j]);
            let produced_phase = face
                .phases
                .get(target)
                .ok_or(HnnError::CellOutside {
                    code: target,
                    alphabet: face.phases.len(),
                })?
                .clone();
            let gap = target_phase - &produced_phase;
            Ok(PhaseRatio {
                target,
                target_phase: target_phase.clone(),
                produced_phase,
                code_length: face.code_length(target)?,
                excess: &gap * &gap / integer(2),
                gap: Reading::of_turns(&gap),
                branch: branch.clone(),
            })
        })?;
        Ok(Self { faces, phases })
    }

    /// The contemporary faces.
    pub fn faces(&self) -> &Faces {
        &self.faces
    }

    /// Each receiving phase's ratio.
    pub fn phases(&self) -> &[PhaseRatio] {
        &self.phases
    }

    /// The window's code length `Σ_j −log₂ p̂_j(t_j)`, enclosed.
    pub fn code_length(&self) -> Result<ExactInterval, HnnError> {
        let mut total = ExactInterval::point(Rat::zero());
        for phase in &self.phases {
            total = interval_sum(&total, &phase.code_length)?;
        }
        Ok(total)
    }

    /// The window's phase excess `Σ_j ½ Δ_j²`, exact.
    pub fn excess(&self) -> Rat {
        self.phases.iter().map(|phase| phase.excess.clone()).sum()
    }

    /// **The undivided pair of phase `j`** in the covector's rational chart, `(q_t : p̃_t)`, carried
    /// with the log's whole winding (the cut's plus the windowed gap's) as the branch of its
    /// logarithm (Lean `Objects/Ratio.logFibre`).
    pub fn log_ratio(&self, phase: usize) -> Result<LogRatio, HnnError> {
        let ratio = self.phases.get(phase).ok_or(HnnError::Shape {
            what: "receiving phase",
            expected: self.phases.len(),
            found: phase,
        })?;
        let mass = self.faces.faces[phase].odometer_masses()?[ratio.target].clone();
        let winding = ratio.winding().to_i64().ok_or(HnnError::CountOverflow)?;
        LogRatio::new(
            GaussianRat::real(Rat::one()),
            GaussianRat::real(mass),
            winding,
        )
        .map_err(|_| HnnError::Shape {
            what: "a nonzero comparand",
            expected: 1,
            found: 0,
        })
    }

    /// **`R⁻¹dR` at the face**: the magnitude part `p̃ − q` on `Re f` and the phase part
    /// `−½ q_c Δ_c` on `Im f`, per receiving phase (module header, the covector's chart).
    pub fn covector(&self) -> Result<RatioCovector, HnnError> {
        let logits = self
            .faces
            .faces
            .iter()
            .zip(&self.phases)
            .map(|(face, ratio)| {
                let masses = face.odometer_masses()?;
                let mut covector = vec![Rat::zero(); 2 * masses.len()];
                for (class, mass) in masses.into_iter().enumerate() {
                    covector[2 * class] = mass;
                }
                covector[2 * ratio.target] -= Rat::one();
                let gap = ratio.gap.turns();
                covector[2 * ratio.target + 1] = -gap / integer(2);
                Ok(covector)
            })
            .collect::<Result<_, HnnError>>()?;
        Ok(RatioCovector { logits })
    }
}

/// [definition] **`R⁻¹dR` at the face**: per receiving phase, the gradient of the ratio's log on
/// the realified logits `[Re f_0, Im f_0, …]`, magnitude in bits per unit of the base-2 exponent and
/// phase in turns (`ln 2` relates bits to nats: a declared factor, never evaluated). Only a
/// [`HolonRatio`] constructs one:
///
/// ```compile_fail,E0451
/// use holonics::hnn::ratio::RatioCovector;
/// // A scalar or a free vector is not a covector of the Holon ratio (guard 10).
/// fn forge(logits: Vec<Vec<holonics::ratio::Rat>>) -> RatioCovector {
///     RatioCovector { logits }
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RatioCovector {
    logits: Vec<Vec<Rat>>,
}

impl RatioCovector {
    /// The gradient on the logits at each receiving phase.
    pub fn logits(&self) -> &[Vec<Rat>] {
        &self.logits
    }

    /// The descent direction `−R⁻¹dR` at receiving phase `j`: the normal law's covector `g`.
    pub fn descent(&self, phase: usize) -> Vec<Rat> {
        self.logits[phase].iter().map(|x| -x).collect()
    }
}

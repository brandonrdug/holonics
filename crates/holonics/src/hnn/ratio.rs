//! **The Holon ratio at the receiver's face, and the carried power.**
//!
//! [definition] The loss is the logarithm of a ratio of Holons (design (a), `compare`; "Exact
//! charts"). At receiving phase `j` the produced Holon `|H⟩` is the logit vector
//! `f_j = k(a_j)/L_R + R P_R^(τ_R) v_R(e_j)`, the landmark tree's grain logits at phase `j`'s causal
//! address plus the wave (the landmark tree, `hnn::receiving::ReceivingRead::combined`; the covector below
//! is read on this combined face and flows back through `R` alone), and the target `|T⟩` is the byte
//! `t_j` read in the same exterior chart that `E` reads: the one-hot `q_j`, with the receiving
//! ring's clock `τ_R(j)` advanced by selective stepping over the targets. Both phases are read in
//! the cut's frame: the target's is
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
//! constant on each grain cell, so its own derivative vanishes almost everywhere). The pairing
//! `⟨p̂ − q, p̃ − q⟩ = Σ_(c≠t) p̂_c p̃_c + (1 − p̂_t)(1 − p̃_t) > 0` (Lean
//! `HNN/Ratio.odometer_covector_descends`) makes `−(p̃ − q)` a descent direction for the smooth
//! softmax score evaluated at the grain representative. It proves no strict decrease of the
//! quantized score: a step inside the same grain cells leaves that score unchanged. At an integer
//! cell (`k = 0`) the chart is the face (`odometer_eq_face_at_integer_cells`), and at `L = 1` the
//! two agree everywhere; elsewhere the weight ratio is at most `2/(e ln 2)`.
//! `p̂` that is read, reported and scored stays exact in `ℚ(θ)`.
//!
//! | Lean `HNN/Ratio` | Rust |
//! |---|---|
//! | `Objects/Ratio/CarriedPower.{carriedPower_exact, theta_pow, irreducible_X_pow_sub_two, realChart}` (the owner's) | [`CarriedPower`], [`PhaseField`] |
//! | `face_constant_on_fibre`, `face_code_length_within_grain`, `codeLength_eq_face` | [`Face`], [`Face::code_length`] |
//! | `receivingPhase_ratio` (a common rechart leaves `ℓ`) | [`HolonRatio::compare`] |
//! | `alignCost_turns` (the gap past the cut's winding, in turns; the cut's winding the branch) | [`target_phases`], [`PhaseRatio`] |
//! | `odometer_covector_descends`, `odometer_eq_face_at_integer_cells` (the magnitude part); `receivingPhase_phase_pullback` (the phase part) | [`RatioCovector`], [`Face::odometer_masses`] |
//! | `Objects/Ratio.logFibre` (the undivided pair with its winding) | [`HolonRatio::log_ratio`] |

use num_bigint::BigInt;
#[cfg(test)]
use num_bigint::BigUint;
use num_traits::{One, ToPrimitive, Zero};

use crate::aeon::Reading;
use crate::hnn::HnnError;
use crate::hnn::encoding::Encoded;
use crate::hnn::field::Field;
use crate::hnn::realization::indexed;
use crate::hnn::receiving::ReceivingRead;
use crate::ratio::algebraic::{
    ExactInterval, interval_difference, interval_sum, log2_enclosure, log2_of_enclosure,
};
use crate::ratio::exponentiated::{CarriedPower, PhaseField};
#[cfg(test)]
use crate::ratio::exponentiated::{READING_BITS, power_of_two};
use crate::ratio::gaussian::GaussianRat;
use crate::ratio::{LogRatio, Rat, integer};
use crate::receiver::face::GrainCell;

// -------------------------------------------------------------------------------------------
// enclosures of the real chart (the base-two logarithms and their sums are
// `crate::ratio::algebraic`'s, on its declared grid)

/// **`2^x` of a rational, enclosed**: `2^⌊x⌋ · 2^(a/b)` with `a/b` the fractional part, its root
/// bounded by an exact integer `b`-th root at [`READING_BITS`]. A reading, never a law's value.
#[cfg(test)]
pub(crate) fn power_of_two_enclosure(x: &Rat) -> Result<ExactInterval, HnnError> {
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
    Ok(ExactInterval::new(&scale * lower, &scale * upper)?)
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
        Ok(interval_difference(
            &log_normalizer,
            &ExactInterval::point(offset),
        )?)
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

/// [definition] **The faces `p̂_j` the receiver reads over one epoch**, one per receiving phase,
/// with their fibres: what `refine` publishes (design (c), `Faces`).
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

/// [definition] **The target phases of one epoch, read in the cut's frame** (Lean
/// `HNN/Ratio.alignCost_turns`): the receiving ring's winding at the anchor, `w = ⌊λ_R/d_R⌋`, which
/// is the log's branch, and `φ^T_j = (τ_R(j) − d_R w)/d_R` turns per receiving phase.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetPhases {
    pub branch: BigInt,
    pub phases: Vec<Rat>,
}

/// **The target phases** of an epoch: the receiving ring's lift from the anchor `λ`, advanced by
/// selective stepping over the encoded targets `t_0 … t_j` (with carries, as ingest would, without
/// ingesting; a located route's digits and its squares at the consumer), read relative to the cut's
/// winding `w = ⌊λ_R/d_R⌋`, which is returned as the branch. On an identity each phase lies in
/// `[0, 1 + 2(j+1)/d_R)`, the anchor's open phase plus at most two ticks a cell (a step and a
/// carry), however long the stream before the cut; a located step advances a ring by at most its
/// period. Refused unless the field admits the targets (`Field::admit`).
pub fn target_phases(
    field: &Field,
    anchor: &[BigInt],
    ring: usize,
    targets: &Encoded,
) -> Result<TargetPhases, HnnError> {
    field.admit(targets)?;
    let declared = field.rings().get(ring).ok_or(HnnError::RingOutside {
        ring,
        rings: field.rings().len(),
    })?;
    let period = declared.period();
    let at = anchor.get(ring).ok_or(HnnError::Shape {
        what: "lift point",
        expected: field.rings().len(),
        found: anchor.len(),
    })?;
    // The cut's winding is the receiving ring's clock's (`Ring::clock_at`).
    let branch = BigInt::from(declared.clock_at(at)?.winding().clone());
    let floor = &branch * BigInt::from(period);
    let mut lift = anchor.to_vec();
    let phases = (0..targets.len())
        .map(|at| {
            field.step_occurrence(&mut lift, targets, at)?;
            Ok(Rat::new(&lift[ring] - &floor, BigInt::from(period)))
        })
        .collect::<Result<_, HnnError>>()?;
    Ok(TargetPhases { branch, phases })
}

// -------------------------------------------------------------------------------------------
// the Holon ratio

/// [definition] **The ratio at one receiving phase** at its target class `t`: the target's phase
/// `φ^T` in the cut's frame, the produced phase `φ^H_t`, the gap past the cut's winding
/// `Δ = φ^T − φ^H_t` read as its windings and open phase ([`Reading`]), the cut's winding `w` as
/// the branch, never descended on (Lean `HNN/Ratio.alignCost_turns`), the code length `−log₂ p̂(t)`
/// (the KL part against the one-hot target, enclosed), and the phase excess `½ Δ²` exactly.
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
    /// The log's whole winding `n` in `Im ℓ = n + open phase`: the cut's winding plus the gap's own
    /// windings past it.
    pub fn winding(&self) -> BigInt {
        &self.branch + self.gap.windings()
    }
}

/// [definition] **The Holon ratio `R_j = Ĝ_(T←H)` over the epoch the receiver reads**: the
/// contemporary faces and, per phase, the ratio at its target class. Only it constructs a
/// [`RatioCovector`].
///
/// [definition; agent-inferred, U6's order repair] **A ratio over a partition of the phases**
/// ([`HolonRatio::compare_partition`]): a receipt is a field of readings over a partition, so a
/// comparison may cover only some phases (a refinement's unlocked stations, whose targets are not
/// placed); the others carry no ratio and a zero covector (no global scalar is formed over them).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HolonRatio {
    faces: Faces,
    phases: Vec<PhaseRatio>,
    /// The receiving phase of each compared ratio, in order.
    stations: Vec<usize>,
}

impl HolonRatio {
    /// **Compare the produced faces with the targets** `(t_j, φ^T_j)`, one per receiving phase,
    /// the target phases read in the cut's frame with its winding the branch.
    pub fn compare(
        faces: Faces,
        targets: &[usize],
        target_phases: &TargetPhases,
    ) -> Result<Self, HnnError> {
        let compared = vec![true; targets.len()];
        Self::compare_partition(faces, targets, target_phases, &compared)
    }

    /// **Compare the produced faces with the targets at the compared phases only** (the type's
    /// header): each compared phase's ratio as [`HolonRatio::compare`] reads it; the rest carry none.
    pub fn compare_partition(
        faces: Faces,
        targets: &[usize],
        target_phases: &TargetPhases,
        compared: &[bool],
    ) -> Result<Self, HnnError> {
        let TargetPhases {
            branch,
            phases: target_phases,
        } = target_phases;
        if targets.len() != faces.faces.len()
            || target_phases.len() != targets.len()
            || compared.len() != targets.len()
        {
            return Err(HnnError::Shape {
                what: "targets per receiving phase",
                expected: faces.faces.len(),
                found: targets.len(),
            });
        }
        let stations: Vec<usize> = (0..targets.len()).filter(|&j| compared[j]).collect();
        // Each receiving phase reads only its own face and target: the phases run together.
        let phases = indexed(stations.len(), |i| {
            let j = stations[i];
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
        Ok(Self {
            faces,
            phases,
            stations,
        })
    }

    /// The receiving phase of each compared ratio, in order.
    pub fn stations(&self) -> &[usize] {
        &self.stations
    }

    /// The contemporary faces.
    pub fn faces(&self) -> &Faces {
        &self.faces
    }

    /// Each receiving phase's ratio.
    pub fn phases(&self) -> &[PhaseRatio] {
        &self.phases
    }

    /// The epoch's code length `Σ_j −log₂ p̂_j(t_j)`, enclosed.
    pub fn code_length(&self) -> Result<ExactInterval, HnnError> {
        let mut total = ExactInterval::point(Rat::zero());
        for phase in &self.phases {
            total = interval_sum(&total, &phase.code_length)?;
        }
        Ok(total)
    }

    /// The epoch's phase excess `Σ_j ½ Δ_j²`, exact.
    pub fn excess(&self) -> Rat {
        self.phases.iter().map(|phase| phase.excess.clone()).sum()
    }

    /// **The undivided pair of phase `j`** in the covector's rational chart, `(q_t : p̃_t)`, carried
    /// with the log's whole winding (the cut's plus the gap's past it) as the branch of its
    /// logarithm (Lean `Objects/Ratio.logFibre`).
    pub fn log_ratio(&self, phase: usize) -> Result<LogRatio, HnnError> {
        let ratio = self.phases.get(phase).ok_or(HnnError::Shape {
            what: "receiving phase",
            expected: self.phases.len(),
            found: phase,
        })?;
        let mass = self.faces.faces[self.stations[phase]].odometer_masses()?[ratio.target].clone();
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
        let mut logits: Vec<Vec<Rat>> = self
            .faces
            .faces
            .iter()
            .map(|face| vec![Rat::zero(); 2 * face.cells().len()])
            .collect();
        for (ratio, &j) in self.phases.iter().zip(&self.stations) {
            let masses = self.faces.faces[j].odometer_masses()?;
            let covector = &mut logits[j];
            for (class, mass) in masses.into_iter().enumerate() {
                covector[2 * class] = mass;
            }
            covector[2 * ratio.target] -= Rat::one();
            let gap = ratio.gap.turns();
            covector[2 * ratio.target + 1] = -gap / integer(2);
        }
        Ok(RatioCovector { logits })
    }
}

/// A comparison with an actually received complex face, in the same receiving chart.
///
/// [agent-inferred] A participating Holon's observation need not be a single class. At the
/// declared grain its mass chart is `q`, so the reached real covector is `p_tilde - q_tilde`
/// and the imaginary covector is `-q_tilde (phi_q - phi_p)/2`. This is the same comparison
/// law as the categorical ratio, without selecting a class from an observed superposition.
/// The observation's original grain cells, phases and unresolved fibres remain present.
///
/// Chart, source, clock and encounter provenance belong to the producing interaction owner.
/// This arithmetic owner checks equal grain and class extent; equality of those extents alone
/// does not certify the two boundary charts. Requested consequences never construct a target
/// here: `observed` is the actual post-interaction receipt, with `None` on uncompared regions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceivingFaceRatio {
    produced: Faces,
    observed: Vec<Option<Face>>,
    stations: Vec<usize>,
    branch: BigInt,
}

impl ReceivingFaceRatio {
    /// Pair actually produced and observed faces after their common chart/clock transport.
    /// A missing region contributes neither a comparison nor a covector.
    pub fn compare_partition(
        produced: Faces,
        observed: Vec<Option<Face>>,
        branch: BigInt,
    ) -> Result<Self, HnnError> {
        if produced.faces.len() != observed.len() {
            return Err(HnnError::Shape {
                what: "one observed receiving region slot per produced region",
                expected: produced.faces.len(),
                found: observed.len(),
            });
        }
        let stations: Vec<_> = observed.iter().enumerate()
            .filter_map(|(j, q)| q.as_ref().map(|_| j)).collect();
        for &j in &stations {
            let p = &produced.faces[j];
            let q = observed[j].as_ref().expect("an observed receiving region");
            if p.cells().is_empty() || p.grain() != q.grain()
                || p.cells().len() != q.cells().len()
                || p.phases().len() != p.cells().len()
                || q.phases().len() != q.cells().len()
            {
                return Err(HnnError::Unadmitted {
                    reason: "paired receiving faces keep their declared grain and complete class extent",
                });
            }
        }
        Ok(Self { produced, observed, stations, branch })
    }

    pub fn faces(&self) -> &Faces { &self.produced }
    pub fn observed(&self) -> &[Option<Face>] { &self.observed }
    pub fn stations(&self) -> &[usize] { &self.stations }

    /// The actual target-to-produced phase gap, including its winding and unresolved phase.
    pub fn phase_gap(&self, station: usize, class: usize) -> Result<Reading, HnnError> {
        let q = self.observed.get(station).and_then(Option::as_ref)
            .ok_or(HnnError::Unadmitted { reason: "an actual compared receiving region" })?;
        let p = &self.produced.faces[station];
        let (Some(p), Some(q)) = (p.phases().get(class), q.phases().get(class)) else {
            return Err(HnnError::CellOutside { code: class, alphabet: p.cells().len() });
        };
        Ok(Reading::of_turns(&(q - p)))
    }

    /// The undivided `(q_tilde : p_tilde)` mass pair at a compared class and its phase winding.
    /// The open phase remains in `phase_gap`; neither the pair nor its branch is collapsed.
    pub fn log_ratio(&self, station: usize, class: usize) -> Result<LogRatio, HnnError> {
        let gap = self.phase_gap(station, class)?;
        let q = self.observed[station].as_ref().expect("a compared receiving region");
        let p_mass = self.produced.faces[station].odometer_masses()?[class].clone();
        let q_mass = q.odometer_masses()?[class].clone();
        let winding = (&self.branch + gap.windings()).to_i64().ok_or(HnnError::CountOverflow)?;
        LogRatio::new(GaussianRat::real(q_mass), GaussianRat::real(p_mass), winding)
            .map_err(|_| HnnError::Unadmitted { reason: "a nonzero paired receiving mass" })
    }

    /// Cross-entropy at the observed grain representative, region by region.
    /// This enclosure is an exterior reading, not retained state or a descent certificate.
    pub fn code_length(&self) -> Result<ExactInterval, HnnError> {
        let mut total = ExactInterval::point(Rat::zero());
        for &j in &self.stations {
            let q = self.observed[j].as_ref().expect("a compared receiving region");
            for (class, mass) in q.odometer_masses()?.iter().enumerate() {
                let length = self.produced.faces[j].code_length(class)?;
                let weighted = ExactInterval::new(&length.lower * mass, &length.upper * mass)?;
                total = interval_sum(&total, &weighted)?;
            }
        }
        Ok(total)
    }

    /// The phase part of the same comparison, weighted by the actually observed mass.
    pub fn excess(&self) -> Result<Rat, HnnError> {
        let mut total = Rat::zero();
        for &j in &self.stations {
            let q = self.observed[j].as_ref().expect("a compared receiving region");
            for (class, mass) in q.odometer_masses()?.iter().enumerate() {
                let gap = self.phase_gap(j, class)?.turns();
                total += mass * &gap * &gap / integer(2);
            }
        }
        Ok(total)
    }

    /// The reached covector uses both producing operands and the observed target face.
    /// Unobserved regions have exactly zero covectors; no class leader is substituted for q.
    pub fn covector(&self) -> Result<RatioCovector, HnnError> {
        let mut logits: Vec<_> = self.produced.faces.iter()
            .map(|p| vec![Rat::zero(); 2 * p.cells().len()]).collect();
        for &j in &self.stations {
            let p = &self.produced.faces[j];
            let q = self.observed[j].as_ref().expect("a compared receiving region");
            let p_mass = p.odometer_masses()?;
            let q_mass = q.odometer_masses()?;
            for class in 0..p.cells().len() {
                logits[j][2 * class] = &p_mass[class] - &q_mass[class];
                let gap = &q.phases()[class] - &p.phases()[class];
                logits[j][2 * class + 1] = -(&q_mass[class] * gap) / integer(2);
            }
        }
        Ok(RatioCovector { logits })
    }
}

/// [definition] **`R⁻¹dR` at the face**: per receiving phase, the gradient of the ratio's log on
/// the realified logits `[Re f_0, Im f_0, …]`, magnitude in bits per unit of the base-2 exponent and
/// phase in turns (`ln 2` relates bits to nats: a declared factor, never evaluated). Only a
/// The declared comparison owners [`HolonRatio`] and [`ReceivingFaceRatio`] construct one:
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

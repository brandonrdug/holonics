//! **The receiving phases and the read at the receiver's grain.**
//!
//! [definition] A receiver reads the front crossing its ring (design (a), `receive`; "Exact
//! charts", the receiving face). [`ReceivingPhases`] names the receiving ring `R`, its first epoch
//! `e_0 = min_(g∈𝒮) dist(g, R)`, its aperture `A` (so `e_last = e_0 + A − 1` and the word evaluates
//! `e_max = e_0 + A` junction steps), its grain `L_R = ⌈1/ε_bits⌉`, derived from the receiver's
//! declared code tolerance `ε_bits` per cell (R2 M2), and its declared region partition
//! ([`Regions`], Decision 27). It refuses `A` beyond the rank of the receiving ring's observability
//! over the word, and reports that rank (review C7).
//!
//! ```text
//! f_j = k(r)/L_R + R · P_R^(τ_R) v_R(e_j)       complex logits over |A| classes, realified [Re, Im, …]
//! Re f_c = n_c + k_c/L_R + ε_c,  ε_c ∈ [0, 1/L_R)   the grain cell (carry, phase class) and the fibre
//! φ^H_c = Im f_c / 2                             each class's phase, in turns
//! ```
//!
//! [definition; agent-inferred] **The combined face** (Decision 27; `hnn::masses`). The scored
//! logits are the receiving parametron's count face at the window's region `r`, read at the grain
//! (`k_c(r)/L_R` on the real rows, zero on the imaginary rows: [`CountFace`]), plus the wave's
//! `R P_R^(τ_R) v_R`. The region is computed from the pending ratio's retained operands alone
//! ([`ReceivingPhases::count_face`]: the moment's window), so every receiving phase of a window
//! reads the same count face. The count logits lie on the grain, so each class's grain cell is the
//! wave's shifted by `k_c/L_R` and its fibre is the wave's. The ratio's covector on the combined
//! face flows back through `R` alone (`hnn::port::Word::pull_back`): the count part is a stored
//! face, deposited by its own law (`hnn::masses::ClassMasses::deposit`).
//!
//! [definition] **Exact inside, grain only at the face.** The logits are exact rationals. The grain
//! reading returns the carry `n_c`, the phase class `k_c ∈ ℤ/L_R` and the fibre `ε_c`, the
//! receiver's unresolved remainder, which is returned and never rounded (guard 15). The normalized
//! face `p̂ ∝ 2^(n + k/L_R)` lives in `ℚ(θ_R)`, `θ_R^(L_R) = 2`, and is built from the cells by the
//! ratio module's carried power (addition 4); this module stops at the cells.
//!
//! | Lean | Rust |
//! |---|---|
//! | `HNN/Ratio.face_constant_on_fibre` (the face reads only `(n, k)`) | [`GrainCell`] |
//! | `HNN/Ratio.grain_of_tolerance` (`L_R = ⌈1/ε_bits⌉`) | [`ReceivingPhases::declare`] |
//! | `receiver::reception::ReceiverFace::read` with `C_S = R P_R^(τ_R) Π_R` | [`ReceivingPhases::read`] |
//! | `HNN/RegionCounts.{combinedLogits, combined_face_pullback, combined_code_pullback}` (Decision 27) | [`ReceivingRead::combined`], [`ReceivingPhases::count_face`] |

use std::ops::Range;

use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};

use crate::hnn::HnnError;
use crate::hnn::field::{ConstitutionRead, Current, Field, ReceiverDeclaration};
use crate::hnn::masses::{ClassMasses, CountFace, Regions};
use crate::hnn::moment::SourceMoment;
use crate::hnn::propagation::Operands;
use crate::hnn::realization::{apply_rows, indexed};
use crate::hnn::word::Word;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer};

/// [definition] **One exponent read at a grain**: `value = carry + phase/grain + fibre`, with
/// `phase ∈ ℤ/grain` and `fibre ∈ [0, 1/grain)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrainCell {
    pub carry: BigInt,
    pub phase: u64,
    pub fibre: Rat,
}

impl GrainCell {
    /// Read `value` at `grain ≥ 1`, exactly: nothing is rounded, the remainder is the fibre.
    ///
    /// [definition; agent-inferred] Two integer divisions with remainder of `value = p/q`
    /// (`q > 0`): `p = n q + r` with `0 ≤ r < q`, then `L r = k q + s` with `0 ≤ s < q`, so the
    /// carry is `n`, the phase class `k` and the fibre `s/(L q)`, normalized once. These are the
    /// floor readings `n = ⌊value⌋`, `k = ⌊L(value − n)⌋`, `ε = (L(value − n) − k)/L` exactly.
    pub fn of(value: &Rat, grain: u64) -> Self {
        let (numerator, denominator) = (value.numer(), value.denom());
        // A reduced ratio carries a positive denominator, so the truncated remainder is
        // corrected once for a negative numerator.
        let (mut carry, mut remainder) = (numerator / denominator, numerator % denominator);
        if remainder.is_negative() {
            carry -= 1;
            remainder += denominator;
        }
        let scaled = remainder * BigInt::from(grain);
        let (phase, residue) = (&scaled / denominator, &scaled % denominator);
        let fibre = Rat::new(residue, denominator * BigInt::from(grain));
        Self {
            carry,
            phase: phase.to_u64().expect("a phase class lies in ℤ/grain"),
            fibre,
        }
    }

    /// The cell's representative `carry + phase/grain`: the point every value of the cell reads as.
    pub fn representative(&self, grain: u64) -> Rat {
        Rat::from_integer(self.carry.clone())
            + Rat::new(BigInt::from(self.phase), BigInt::from(grain))
    }
}

/// [definition] **One receiving read**: the exact realified logits `f`, each class's grain cell of
/// `Re f_c`, and each class's phase `φ^H_c = Im f_c / 2` in turns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceivingRead {
    pub logits: Vec<Rat>,
    pub cells: Vec<GrainCell>,
    pub phases: Vec<Rat>,
}

impl ReceivingRead {
    /// **A read of given realified logits at a grain**: each class's real logit read at the grain
    /// with its fibre, and its imaginary logit halved into turns. The classes are read alone and run
    /// together (`hnn::realization`).
    pub fn of_logits(logits: Vec<Rat>, grain: u64) -> Self {
        let classes = logits.len() / 2;
        let cells = indexed(classes, |class| {
            Ok::<_, HnnError>(GrainCell::of(&logits[2 * class], grain))
        })
        .expect("a grain reading refuses nothing");
        let phases = logits.chunks(2).map(|pair| &pair[1] / integer(2)).collect();
        Self {
            logits,
            cells,
            phases,
        }
    }

    /// **The combined read** (module header, Decision 27): the wave's exact logits `R P_R^(τ_R) v_R`
    /// plus the count face's grain logits, read at the grain. Refused when the two disagree in
    /// length or grain. The host reference and every device realization form their faces here.
    pub fn combined(wave: Vec<Rat>, count: &CountFace, grain: u64) -> Result<Self, HnnError> {
        let stored = count.logits();
        if stored.len() != wave.len() || count.grain() != grain {
            return Err(HnnError::Shape {
                what: "the count face's grain logits against the wave's logits",
                expected: wave.len(),
                found: stored.len(),
            });
        }
        let logits = wave
            .into_iter()
            .zip(stored)
            .map(|(wave, stored)| {
                if stored.is_zero() {
                    wave
                } else {
                    wave + stored
                }
            })
            .collect();
        Ok(Self::of_logits(logits, grain))
    }
}

/// [definition] **The receiving phases** of one admitted receiver. See the module header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceivingPhases {
    ring: usize,
    first_epoch: usize,
    aperture: usize,
    grain: u64,
    tolerance: Rat,
    regions: Regions,
    rank: usize,
}

impl ReceivingPhases {
    /// **Declare an admitted receiver's phases** at the medium `(Θ, λ)`: its first epoch from the
    /// source rings, its grain from its code tolerance, and its observability rank over the word,
    /// refusing an aperture beyond it.
    pub fn declare(
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
        receiver: &ReceiverDeclaration,
    ) -> Result<Self, HnnError> {
        if receiver.ring >= field.rings().len() {
            return Err(HnnError::RingOutside {
                ring: receiver.ring,
                rings: field.rings().len(),
            });
        }
        if receiver.tolerance <= Rat::zero() {
            return Err(HnnError::Tolerance {
                tolerance: receiver.tolerance.clone(),
            });
        }
        if receiver.aperture == 0 {
            return Err(HnnError::Observability {
                aperture: 0,
                rank: 0,
            });
        }
        let first_epoch = field
            .first_epoch(receiver.ring)
            .ok_or(HnnError::Unreached {
                ring: receiver.ring,
            })?;
        let grain = receiver
            .tolerance
            .recip()
            .ceil()
            .to_integer()
            .to_u64()
            .ok_or(HnnError::Tolerance {
                tolerance: receiver.tolerance.clone(),
            })?;
        let mut phases = Self {
            ring: receiver.ring,
            first_epoch,
            aperture: receiver.aperture,
            grain,
            tolerance: receiver.tolerance.clone(),
            regions: receiver.regions,
            rank: 0,
        };
        phases.rank = phases.observability(field, constitution, current)?;
        if phases.aperture > phases.rank {
            return Err(HnnError::Observability {
                aperture: phases.aperture,
                rank: phases.rank,
            });
        }
        Ok(phases)
    }

    /// **The receiving ring's observability rank over the word**: the rank of the exact law's linear
    /// map from the source rings' open storage to the anchors `(v_R(e_0), …, v_R(e_last))`, one
    /// word per source coordinate. [agent-inferred] The rank is the medium's, read under the exact
    /// law ([`Operands::exact_at_cut`]): the executed word carries its transients on a lattice and
    /// is linear only up to its released remainders, so a rank read through it would count the
    /// splits, not the medium.
    pub fn observability(
        &self,
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
    ) -> Result<usize, HnnError> {
        let operands = Operands::exact_at_cut(field, constitution, current)?;
        let mut columns: Vec<Vec<Rat>> = Vec::new();
        for &source in field.sources() {
            for coordinate in 0..field.ring(source).width() {
                let mut storage: Vec<Vec<Rat>> = field
                    .rings()
                    .iter()
                    .map(|ring| vec![Rat::zero(); ring.width()])
                    .collect();
                storage[source][coordinate] = integer(1);
                let mut word = Word::on_operands(field, operands.clone(), storage)?;
                columns.push(word.forward(self)?.concat());
            }
        }
        let rows = columns.first().map_or(0, Vec::len);
        let matrix = ExactRatMatrix::shaped(
            rows,
            columns.len(),
            (0..rows)
                .map(|row| columns.iter().map(|column| column[row].clone()).collect())
                .collect(),
        )?;
        Ok(matrix.rank()?)
    }

    pub fn ring(&self) -> usize {
        self.ring
    }

    /// `e_0`.
    pub fn first_epoch(&self) -> usize {
        self.first_epoch
    }

    /// `A`.
    pub fn aperture(&self) -> usize {
        self.aperture
    }

    /// `e_last = e_0 + A − 1`.
    pub fn last_epoch(&self) -> usize {
        self.first_epoch + self.aperture - 1
    }

    /// `e_max = e_0 + A`: the junction steps the word evaluates.
    pub fn junction_steps(&self) -> usize {
        self.first_epoch + self.aperture
    }

    /// The receiving epochs `e_0 … e_last`.
    pub fn epochs(&self) -> Range<usize> {
        self.first_epoch..self.first_epoch + self.aperture
    }

    /// `L_R = ⌈1/ε_bits⌉`.
    pub fn grain(&self) -> u64 {
        self.grain
    }

    /// The declared code tolerance `ε_bits`.
    pub fn tolerance(&self) -> &Rat {
        &self.tolerance
    }

    /// The declared region partition (Decision 27).
    pub fn regions(&self) -> Regions {
        self.regions
    }

    /// **The observability rank reported at declaration**: a reading at the declaring medium
    /// `(Θ, λ)` only. A later class configuration (the rings' phases after ingest, the sheet
    /// classes after deposits) can have a lower rank; nothing re-reads it, and no law consumes it
    /// past the declaration's refusal of a wider aperture.
    pub fn rank(&self) -> usize {
        self.rank
    }

    /// **The count face of a window** (module header; Decision 27): the receiving parametron's
    /// masses at the region of the moment's retained window, read at the grain. Refused when the
    /// constitution carries no masses on the receiving ring, or masses of another partition.
    pub fn count_face(
        &self,
        constitution: &impl ConstitutionRead,
        moment: &SourceMoment,
    ) -> Result<CountFace, HnnError> {
        let masses = constitution
            .class_masses(self.ring)
            .ok_or(HnnError::MissingReceivingMap { ring: self.ring })?;
        self.count_face_at(masses, moment)
    }

    /// **The count face of a window at given masses** (a device realization reads the masses its
    /// publication keeps on the host): refused for masses of another partition.
    pub fn count_face_at(
        &self,
        masses: &ClassMasses,
        moment: &SourceMoment,
    ) -> Result<CountFace, HnnError> {
        if masses.regions() != self.regions {
            return Err(HnnError::Shape {
                what: "the receiving parametron's region partition against the receiver's",
                expected: self.regions.code() as usize,
                found: masses.regions().code() as usize,
            });
        }
        let region = self.regions.region(&moment.window(), masses.classes())?;
        CountFace::read(masses, region, self.grain)
    }

    /// **The read at one receiving epoch**: `f = k(r)/L_R + R · P_R^(τ_R) v_R` (module header, the
    /// combined face), each class's real logit read at the grain with its fibre, and its imaginary
    /// logit halved into turns.
    pub fn read(
        &self,
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
        anchor: &[Rat],
        count: &CountFace,
    ) -> Result<ReceivingRead, HnnError> {
        let ring = field.ring(self.ring);
        if anchor.len() != ring.width() {
            return Err(HnnError::Shape {
                what: "receiving anchor",
                expected: ring.width(),
                found: anchor.len(),
            });
        }
        let map = constitution
            .receiving_map(self.ring)
            .ok_or(HnnError::MissingReceivingMap { ring: self.ring })?;
        if map.rows() != 2 * field.alphabet() || map.columns() != ring.width() {
            return Err(HnnError::Shape {
                what: "receiving map R",
                expected: 2 * field.alphabet() * ring.width(),
                found: map.rows() * map.columns(),
            });
        }
        // The map's rows, then the classes' grain cells, each read alone, run together
        // (`hnn::realization`); the map has `2|A|` rows, so the classes pair them exactly.
        let wave = apply_rows(map, &ring.rotate(anchor, &current.lift()[self.ring]))?;
        ReceivingRead::combined(wave, count, self.grain)
    }
}

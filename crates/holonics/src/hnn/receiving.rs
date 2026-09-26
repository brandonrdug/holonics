//! **The receiving phases, the receiving parametron's active suffix address, and the combined
//! read at the receiver's grain.**
//!
//! [definition] A receiver reads the front crossing its ring (design (a), `receive`; "Exact
//! charts", the receiving face). [`ReceivingPhases`] names the receiving ring `R`, its first epoch
//! `e_0 = min_(g∈𝒮) dist(g, R)`, its aperture `A` (so `e_last = e_0 + A − 1` and the word evaluates
//! `e_max = e_0 + A` junction steps), its grain `L_R = ⌈1/ε_bits⌉`, derived from the receiver's
//! declared code tolerance `ε_bits` per cell (R2 M2), and the depth `D` of its landmark tree's
//! address (Decision 28). It refuses `A` beyond the rank of the receiving ring's observability
//! over the word, and reports that rank (review C7).
//!
//! ```text
//! a_j = [x_(p+j−1), …, x_p, x_(p−1), …]_D        phase j's address: the window's earlier targets, then the active suffix address
//! f_j = k(a_j)/L_R + R · P_R^(τ_R) v_R(e_j)      complex logits over |A| classes, realified [Re, Im, …]
//! 2^(k_c) ≤ q(c | a_j)^(L_R) < 2^(k_c+1)         the tree face's grain exponent (integer comparisons)
//! Re f_c = n_c + k_c/L_R + ε_c,  ε_c ∈ [0, 1/L_R)   the grain cell (carry, phase class) and the fibre
//! φ^H_c = Im f_c / 2                             each class's phase, in turns
//! ```
//!
//! [definition; agent-inferred] **The receiving parametron's storage is the landmark tree**
//! (Decision 28, `hnn::landmark::Landmarks`, held in `Θ` at the receiving locus beside `R`). It
//! replaces Decision 27's region table, which is its depth-one case (Lean
//! `HNN/LandmarkTree.depth_one_is_decision_27`; Decision 27's laws stay in Lean `HNN/RegionCounts`).
//! The tree is declared from the receiver ([`landmark_declaration`]): the cell emitted as its
//! odometer digits, the depth `D` (4 on campaign 1, chosen on the development cells in the landmark
//! receipt), no forced split, the field's declared population `n*` and the receiver's grain, from
//! which the owner derives its widths (the path lattice `M_p` and the β carrier `W`).
//!
//! [definition; agent-inferred] **The active suffix address** ([`ActiveAddress`]; the tower thread,
//! the suffix restriction of the source navigator's word). The last `D` cells the receiver has
//! received, newest first, `Boundary` before the passage's first cell. It is the receiving
//! parametron's own state, kept by the resident beside the tree and shifted at every ingested
//! cell. It is not the source moment's state: the word never reads it, so the moment's window
//! stays `max Δ` and the capacity `n*` (which counts the source state the word reads) is unchanged
//! by construction. Its bits count in the resident's state bits, and the aeon collapse keeps it
//! with the tree (Lean `HNN/LandmarkTree.release_rule`: only nodes deeper than `D` are releasable,
//! and there are none). A pending ratio copies it at its cut, an operand like the moment's counts.
//! **The address is per cell and causal**: phase `j` of the window opening at `p` reads the tree at
//! `a_j = [x_(p+j−1), …, x_p]` (the window's own earlier targets, known at compare) followed by the
//! copied suffix `[x_(p−1), …]`, truncated to `D` ([`ActiveAddress::phase`]). It equals
//! `hnn::landmark::address(cells, p + j, D)` exactly (the test
//! `the_phase_address_is_the_trees_causal_address`), so an aperture-two window reads its two
//! phases at their own addresses (the located failure pooled lags one and two at one region).
//!
//! [definition; agent-inferred] **The combined face** (Decision 27's combined read, with the tree's
//! face in place of the region table's). The scored logits are the tree face's grain logits
//! (`k_c/L_R` on the real rows, zero on the imaginary rows: [`grain_logits`]) plus the wave's
//! `R P_R^(τ_R) v_R` ([`ReceivingRead::combined`]). The wave part is the refine's; the tree part
//! needs each phase's address, so it is read at **compare**, per phase
//! ([`ReceivingPhases::tree_faces`], [`ReceivingPhases::combine`]). The tree logits lie on the
//! grain, so each class's grain cell is the wave's shifted by `k_c/L_R` and its fibre is the
//! wave's. The ratio's covector on the combined face flows back through `R` alone
//! (`hnn::port::Word::pull_back`; Lean `HNN/RegionCounts.combined_face_pullback` holds for any
//! stored grain logits): the tree part is a stored face, deposited by its own law (the reached
//! comparisons' cells on their opened paths, `hnn::constitution::LandmarkStep`).
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
//! | `HNN/RegionCounts.{grainExponent_spec, grain_log_iff_pow_bounds, grain_face_residual, grain_code_residual}` | [`grain_exponent`], [`grain_logits`] |
//! | `receiver::reception::ReceiverFace::read` with `C_S = R P_R^(τ_R) Π_R` | [`ReceivingPhases::read`] |
//! | `HNN/RegionCounts.{combinedLogits, combined_face_pullback, combined_code_pullback}` | [`ReceivingRead::combined`], [`ReceivingPhases::combine`] |
//! | `HNN/LandmarkTree.{unfounded_reads_prior, founded_tree_same_law, release_rule}` (the typed suffix address, kept whole by the collapse) | [`ActiveAddress`], [`ReceivingPhases::tree_faces`] |

use std::ops::Range;

use num_bigint::{BigInt, BigUint};
use num_traits::{Signed, ToPrimitive, Zero};

use crate::compression::cost::ceil_log2;
use crate::hnn::HnnError;
use crate::hnn::field::{ConstitutionRead, Current, Field, ReceiverDeclaration};
use crate::hnn::landmark::{LandmarkDeclaration, LandmarkFace, Letter};
use crate::hnn::propagation::Operands;
use crate::hnn::ratio::{Face, Faces};
use crate::hnn::realization::{apply_rows, indexed};
use crate::hnn::word::Word;
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer};

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

/// [definition] **The tree face's grain logits**, realified `[k_0/L_R, 0, k_1/L_R, 0, …]` (Lean
/// `HNN/RegionCounts.grainLogits`): each class's grain exponent over the grain on its real row,
/// zero on its imaginary row.
pub fn grain_logits(face: &LandmarkFace) -> Vec<Rat> {
    let grain = BigInt::from(face.grain);
    face.exponents
        .iter()
        .flat_map(|k| [Rat::new(k.clone(), grain.clone()), Rat::zero()])
        .collect()
}

/// **The tree face alone's code length** `−log₂ p̂(c)` of one class, enclosed: the scored face of
/// its grain logits alone, `θ^(k_c)/Σ_d θ^(k_d)` in `ℚ(θ)` (`hnn::ratio::Face`), the face the
/// combined read opens at when the wave reads zero.
pub fn tree_code_length(face: &LandmarkFace, class: usize) -> Result<ExactInterval, HnnError> {
    let read = ReceivingRead::of_logits(grain_logits(face), face.grain);
    Face::of_read(&read, face.grain)?.code_length(class)
}

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

    /// **The combined read** (module header): the wave's exact logits `R P_R^(τ_R) v_R` plus the
    /// tree face's grain logits, read at the grain. Refused when the two disagree in length or
    /// grain. The host reference and every device realization form their faces here.
    pub fn combined(wave: Vec<Rat>, tree: &LandmarkFace, grain: u64) -> Result<Self, HnnError> {
        let stored = grain_logits(tree);
        if stored.len() != wave.len() || tree.grain != grain {
            return Err(HnnError::Shape {
                what: "the tree face's grain logits against the wave's logits",
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

// -------------------------------------------------------------------------------------------
// the active suffix address

/// [definition; agent-inferred] **The receiving parametron's active suffix address** (module
/// header): the last `D` cells received, newest first, `Boundary` before the passage's first cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActiveAddress {
    letters: Vec<Letter>,
}

impl ActiveAddress {
    /// **The address before any cell**: `D` boundary letters.
    pub fn boundary(depth: usize) -> Self {
        Self {
            letters: vec![Letter::Boundary; depth],
        }
    }

    /// **The resident's address register** for a field: at the deepest declared receiver's depth,
    /// each receiver reading its own first `D` letters.
    pub fn of_field(field: &Field) -> Self {
        Self::boundary(
            field
                .receivers()
                .iter()
                .map(|receiver| receiver.depth)
                .max()
                .unwrap_or(0),
        )
    }

    /// `D`.
    pub fn depth(&self) -> usize {
        self.letters.len()
    }

    /// The letters, newest first.
    pub fn letters(&self) -> &[Letter] {
        &self.letters
    }

    /// **Receive one cell**: it becomes the newest letter, and the oldest leaves.
    pub fn receive(&mut self, cell: usize) {
        if self.letters.is_empty() {
            return;
        }
        self.letters.pop();
        self.letters.insert(0, Letter::Cell(cell));
    }

    /// **The address's first `depth` letters** (a receiver of a shallower tree), refused past the
    /// register's depth.
    pub fn truncated(&self, depth: usize) -> Result<Self, HnnError> {
        if depth > self.letters.len() {
            return Err(HnnError::Shape {
                what: "a receiver's address depth within the resident's register",
                expected: self.letters.len(),
                found: depth,
            });
        }
        Ok(Self {
            letters: self.letters[..depth].to_vec(),
        })
    }

    /// **Phase `j`'s address** (module header): the window's cells before phase `j` that are known,
    /// newest first (`known[j−1], …, known[0]`, at most the `known.len()` of them), then this
    /// suffix, truncated to its depth. At a compare every earlier target is known, so this is
    /// `hnn::landmark::address(cells, p + j, D)`; at a release no cell of the window is known and
    /// every phase reads the window's opening address (`hnn::port`'s release).
    pub fn phase(&self, known: &[usize], j: usize) -> Vec<Letter> {
        let depth = self.letters.len();
        known[..j.min(known.len())]
            .iter()
            .rev()
            .map(|&cell| Letter::Cell(cell))
            .chain(self.letters.iter().copied())
            .take(depth)
            .collect()
    }

    /// **Its exact bits**: each letter one of `|A| + 1` values (the boundary or a cell), at
    /// `⌈log₂(|A| + 1)⌉` bits.
    pub fn bits(&self, alphabet: usize) -> u64 {
        self.letters.len() as u64 * ceil_log2(&BigUint::from(alphabet + 1))
    }
}

/// [definition; agent-inferred] **The landmark tree a receiver declares** (module header): the
/// field's exterior chart `|A|` (the cell emitted as its odometer digits), the receiver's depth `D`
/// with no forced split, the field's declared population (the passage the tree's certificates hold within) and
/// the receiver's grain `L_R = ⌈1/ε_bits⌉`.
pub fn landmark_declaration(
    field: &Field,
    receiver: &ReceiverDeclaration,
) -> Result<LandmarkDeclaration, HnnError> {
    Ok(LandmarkDeclaration {
        alphabet: field.alphabet(),
        depth: receiver.depth,
        forced: 0,
        population: field.population(),
        grain: grain_of(&receiver.tolerance)?,
    })
}

/// `L_R = ⌈1/ε_bits⌉`, refused at a tolerance that is not positive or whose grain passes the word.
fn grain_of(tolerance: &Rat) -> Result<u64, HnnError> {
    if *tolerance <= Rat::zero() {
        return Err(HnnError::Tolerance {
            tolerance: tolerance.clone(),
        });
    }
    tolerance
        .recip()
        .ceil()
        .to_integer()
        .to_u64()
        .ok_or(HnnError::Tolerance {
            tolerance: tolerance.clone(),
        })
}

// -------------------------------------------------------------------------------------------
// the receiving phases

/// [definition] **The receiving phases** of one admitted receiver. See the module header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceivingPhases {
    ring: usize,
    first_epoch: usize,
    aperture: usize,
    grain: u64,
    tolerance: Rat,
    depth: usize,
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
        let grain = grain_of(&receiver.tolerance)?;
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
        let mut phases = Self {
            ring: receiver.ring,
            first_epoch,
            aperture: receiver.aperture,
            grain,
            tolerance: receiver.tolerance.clone(),
            depth: receiver.depth,
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

    /// `D`, the depth of the landmark tree's address (Decision 28).
    pub fn depth(&self) -> usize {
        self.depth
    }

    /// **The observability rank reported at declaration**: a reading at the declaring medium
    /// `(Θ, λ)` only. A later class configuration (the rings' phases after ingest, the sheet
    /// classes after deposits) can have a lower rank; nothing re-reads it, and no law consumes it
    /// past the declaration's refusal of a wider aperture.
    pub fn rank(&self) -> usize {
        self.rank
    }

    /// **The wave's read at one receiving epoch**: `R · P_R^(τ_R) v_R`, each class's real logit read
    /// at the grain with its fibre, and its imaginary logit halved into turns. The tree part is
    /// added at compare ([`ReceivingPhases::combine`]).
    pub fn read(
        &self,
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
        anchor: &[Rat],
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
        Ok(ReceivingRead::of_logits(wave, self.grain))
    }

    /// **The window's phase addresses** (module header): phase `j` at
    /// [`ActiveAddress::phase`] of the window's known targets. Refused when the suffix is not of
    /// the receiver's depth.
    pub fn addresses(
        &self,
        address: &ActiveAddress,
        known: &[usize],
    ) -> Result<Vec<Vec<Letter>>, HnnError> {
        if address.depth() != self.depth {
            return Err(HnnError::Shape {
                what: "the active suffix address against the receiver's depth",
                expected: self.depth,
                found: address.depth(),
            });
        }
        Ok((0..self.aperture)
            .map(|j| address.phase(known, j))
            .collect())
    }

    /// **The tree faces of one window** (module header): the receiving parametron's tree read at
    /// each phase's address, every class's executed face with its grain exponent. The phases each
    /// read only their own address and run together (`hnn::realization`). Refused when the
    /// constitution carries no tree on the receiving ring.
    pub fn tree_faces(
        &self,
        constitution: &impl ConstitutionRead,
        address: &ActiveAddress,
        known: &[usize],
    ) -> Result<Vec<LandmarkFace>, HnnError> {
        let tree = constitution
            .landmarks(self.ring)
            .ok_or(HnnError::MissingReceivingMap { ring: self.ring })?;
        let addresses = self.addresses(address, known)?;
        indexed(addresses.len(), |j| tree.face(&addresses[j], self.grain))
    }

    /// **The combined faces of one window** (module header): each phase's wave logits plus its tree
    /// face's grain logits, read at the grain. Refused unless there is one tree face per phase.
    pub fn combine(&self, waves: &Faces, trees: &[LandmarkFace]) -> Result<Faces, HnnError> {
        if waves.logits.len() != trees.len() {
            return Err(HnnError::Shape {
                what: "one tree face per receiving phase",
                expected: waves.logits.len(),
                found: trees.len(),
            });
        }
        let reads = indexed(trees.len(), |j| {
            ReceivingRead::combined(waves.logits[j].clone(), &trees[j], self.grain)
        })?;
        Faces::of_reads(&reads, self.grain)
    }
}

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
//! replaces Decision 27's region table, whose laws stay in Lean (`HNN/RegionCounts`). The region
//! table is the depth-one forced case of the whole-cell emission (`|A|`-ary masses at a node; Lean
//! `HNN/LandmarkTree.depth_one_is_decision_27`), which lives in Lean only; this tree emits the
//! cell's odometer digits, and its depth-one forced case is a product of binary KT faces at the
//! preceding cell, not the region table's `|A|`-ary face.
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
//! with the tree whole (Lean `HNN/LandmarkTree.release_rule` proves that nodes deeper than `D` are
//! releasable, of which the tree founds none, and that a retention is lawful exactly when it
//! refines the causal signature; it does not prove that no shallower merge is lawful, and the
//! collapse attempts none). A pending ratio copies it at its cut, an operand like the moment's
//! counts.
//! **The address is per cell and causal**: phase `j` of the window opening at `p` reads the tree at
//! `a_j = [x_(p+j−1), …, x_p]` (the window's own earlier targets, known at compare) followed by the
//! copied suffix `[x_(p−1), …]`, truncated to `D` ([`ActiveAddress::phase`]). It equals
//! `hnn::landmark::address(cells, p + j, D)` exactly (the test
//! `the_phase_address_is_the_trees_causal_address`), so an aperture-two window reads its two
//! phases at their own addresses (the located failure pooled lags one and two at one region).
//! **The window is read in cell order** (Decision 29 within a window): phase `j`'s tree face is read
//! at the standing after the window's earlier phases' tree deposits (their targets are known at
//! compare), on a working overlay of the nodes those deposits write
//! (`hnn::landmark::Landmarks::window_faces`); the deposit then applies exactly those steps to the
//! published tree, in cell order, so the tree it publishes is the overlay's last standing plus the
//! last phase's step. The wave's part of a window is the one refine's, read at the window's opening
//! standing: the wave's maps are deposited once a window, by the normal law.
//!
//! [definition; agent-inferred] **The receiving letters** (campaign 2; Lean
//! `HNN/LandmarkAddress`). The address register holds typed bundles, not bare cells: each earlier
//! cell's tick contributes its cell and the declared features' letters ([`LetterFamily`]), newest
//! bundle first, and the register restricts by dropping its oldest whole bundle. A letter is read
//! from the retained sufficient state before the cell it predicts: the register's reader
//! ([`LetterReader`]) keeps the clock of the rings its phase letters read (their phases
//! `λ_g mod d_g`, stepped by the selective step at every received cell, synchronized with the lift
//! point at the mount and after every re-keying, and checked against it at every ingest), reads each
//! tick's letter after the tick, and never reads it again; a pending ratio copies the register, its
//! clock included, at its cut, so each phase's letters of the window's known targets are read by a
//! copy of that clock (`bundle_causal`). A ring's phase class at its declared grain is read by
//! [`GrainCell::of`] of the phase in turns; a contact's lock address and site kind arrive as the
//! plain-data [`ContactReading`] `(contact, lock, kind)` per tick ([`ActiveAddress::receive_read`]).
//! The clock-only letters of a passage are replayed without the wave ([`clock_letters`]: the
//! resident's clock law with its key location and re-keying at each carry-out), the development
//! harness's letters (Decision 31). The field's declared family ([`letter_family`]) is the harness's
//! choice: on the standing cut's development cells no clock-only family lowered the code length by
//! its description charge, so it is the cell-only family, and the register is campaign 1's.
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
//! [definition; agent-inferred] **The scored face is the mixture** ([`Mixture`], the primary's ruling
//! A): the receiver scores the two-way mixture of the tree's face and the combined face, weighted by
//! their prequential likelihood ratio `β` in Θ at the receiving locus, as a tree node weighs its own
//! face against its split, `β` stepped after every cell in cell order, within a window too. The
//! wave keeps learning from the combined face's covector.
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
//! | `HNN/LandmarkTree.{sequential_mixture, sequential_mixture_bounds, sequential_mixture_executed}` (the two-face mixture stepped cell by cell, within one bit of the better face plus the chart's drift) | [`Mixture`] |
//! | `HNN/LandmarkAddress.{bundle_causal, bundle_restrict, feature_scale_square, address_descends_retention, phase_partition_finite}` (the typed bundles read from the retained clock before the cell they predict) | [`LetterReader`], [`ActiveAddress`], [`clock_letters`] |

use std::ops::Range;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::compression::cost::ceil_log2;
use crate::hnn::HnnError;
use crate::hnn::field::{ConstitutionRead, Current, Field, ReceiverDeclaration};
use crate::hnn::keys;
use crate::hnn::landmark::{
    Beta, Bundle, ContactReading, Feature, LandmarkDeclaration, LandmarkFace, Letter, LetterFamily,
    code_length,
};
use crate::hnn::propagation::Operands;
use crate::hnn::ratio::{Face, Faces};
use crate::hnn::realization::{apply_rows, indexed};
use crate::hnn::word::Word;
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::exponentiated::CarriedPower;
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

/// **The tree face at the grain**: the code length `−log₂ p̂(c)` of one class, enclosed, under the
/// face of the tree's grain logits alone, `θ^(k_c)/Σ_d θ^(k_d)` in `ℚ(θ)` (`hnn::ratio::Face`), the
/// face the combined read opens at when the wave reads zero. It is not the tree's executed face
/// `q_T(c)`, which the mixture weighs ([`Scored::tree`] reads that one): the two differ by the
/// grain's rounding of the exponents and the renormalization.
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
// the receiving letters: the clock register and the active suffix address

/// One ring's clock law as the register reads it: its period and its lock on the port chart
/// `port(x) = x mod d` (`hnn::field::Ring::{port, fits}`).
#[derive(Clone, Debug, PartialEq, Eq)]
struct ClockRing {
    period: u64,
    lock: Vec<bool>,
}

/// [definition; agent-inferred] **The letters' reader** (module header, "The receiving letters"):
/// the declared family, the clock law of the rings its phase letters read (rings `0 ..= g_max` in
/// carry order, since a ring's step reads its predecessors' carries: Lean
/// `HNN/Moment.selective_position`), and their phases `λ_g mod d_g` at the register's cut. It is
/// the retained sufficient clock state the letters are read from (Lean
/// `HNN/LandmarkAddress.address_descends_retention`): a tick's letter is read after the tick,
/// before the cell it predicts, and nothing of the past is kept.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LetterReader {
    family: LetterFamily,
    rings: Vec<ClockRing>,
    phases: Vec<u64>,
}

impl LetterReader {
    /// The cell-only family's reader: no clock is read.
    pub fn cells() -> Self {
        Self {
            family: LetterFamily::cells(),
            rings: Vec::new(),
            phases: Vec::new(),
        }
    }

    /// **The reader of a declared family at a lift point**. Refused at a phase letter of a ring
    /// outside the field, at a grain that is zero, or at a contact slot of a contact outside it.
    pub fn of(field: &Field, family: LetterFamily, current: &Current) -> Result<Self, HnnError> {
        let mut reach = 0usize;
        for feature in family.features() {
            match *feature {
                Feature::Phase { ring, grain } => {
                    if ring >= field.rings().len() {
                        return Err(HnnError::RingOutside {
                            ring,
                            rings: field.rings().len(),
                        });
                    }
                    if grain == 0 {
                        return Err(HnnError::NonpositiveDeclaration);
                    }
                    reach = reach.max(ring + 1);
                }
                Feature::Contact { contact, .. } => {
                    if contact >= field.contacts().len() {
                        return Err(HnnError::Shape {
                            what: "a contact letter of a declared contact",
                            expected: field.contacts().len(),
                            found: contact,
                        });
                    }
                }
            }
        }
        let rings = field.rings()[..reach]
            .iter()
            .map(|ring| ClockRing {
                period: ring.period(),
                lock: (0..ring.period() as usize)
                    .map(|port| ring.fits(port))
                    .collect(),
            })
            .collect();
        let mut reader = Self {
            family,
            rings,
            phases: vec![0; reach],
        };
        reader.synchronize(field, current)?;
        Ok(reader)
    }

    pub fn family(&self) -> &LetterFamily {
        &self.family
    }

    /// **Take the rings' phases from a lift point** (at the mount, and after a re-keying).
    pub fn synchronize(&mut self, field: &Field, current: &Current) -> Result<(), HnnError> {
        for (ring, phase) in self.phases.iter_mut().enumerate() {
            *phase = current.phase(field, ring)?;
        }
        Ok(())
    }

    /// Whether the register's clock is the lift point's (the resident checks it at every ingest).
    pub fn agrees(&self, field: &Field, current: &Current) -> bool {
        self.phases
            .iter()
            .enumerate()
            .all(|(ring, phase)| current.phase(field, ring).ok() == Some(*phase))
    }

    /// **One cell's selective step on the kept rings** (`hnn::field::Field::selective_step`):
    /// ring `g` advances `[port_g(x) ∈ N_g]` plus its predecessor's carry.
    fn step(&mut self, cell: usize) {
        let mut carry = 0u64;
        for (ring, phase) in self.rings.iter().zip(self.phases.iter_mut()) {
            let port = (cell as u64 % ring.period) as usize;
            let advance = u64::from(ring.lock[port]) + carry;
            let next = *phase + advance;
            carry = u64::from(next >= ring.period);
            *phase = next % ring.period;
        }
    }

    /// **Ring `g`'s phase class at grain `g_R`**: `⌊g_R·phase⌋ mod g_R` of the phase `λ_g/d_g` in
    /// turns (`GrainCell::of`, its fibre the remainder; Lean `phase_partition_finite`).
    fn class(&self, ring: usize, grain: u64) -> u64 {
        let period = self.rings[ring].period;
        GrainCell::of(
            &Rat::new(BigInt::from(self.phases[ring]), BigInt::from(period)),
            grain,
        )
        .phase
    }

    /// **The letter of one tick**: the cell's selective step, then its bundle read after the tick
    /// (the cell alone for the cell-only family), each contact slot from its reading. Refused when
    /// a declared contact slot has no reading.
    pub fn tick(&mut self, cell: usize, contacts: &[ContactReading]) -> Result<Letter, HnnError> {
        self.step(cell);
        if self.family.is_empty() {
            return Ok(Letter::Cell(cell));
        }
        let values = self
            .family
            .features()
            .iter()
            .map(|feature| match *feature {
                Feature::Phase { ring, grain } => Ok(self.class(ring, grain)),
                Feature::Contact { contact, .. } => {
                    let reading = contacts
                        .iter()
                        .find(|reading| reading.contact == contact)
                        .ok_or(HnnError::Shape {
                            what: "a contact reading for each declared contact letter",
                            expected: contact,
                            found: contacts.len(),
                        })?;
                    feature.contact_value(reading)
                }
            })
            .collect::<Result<Vec<u64>, HnnError>>()?;
        Ok(Letter::Bundle(Bundle {
            cell,
            features: self.family.encode(&values)?,
        }))
    }

    /// Its exact bits: each kept ring's phase, `⌈log₂ d_g⌉`.
    pub fn bits(&self) -> u64 {
        self.rings
            .iter()
            .map(|ring| ceil_log2(&BigUint::from(ring.period)))
            .sum()
    }
}

/// [definition; agent-inferred] **The receiving parametron's active suffix address** (module
/// header): the last `D` ticks' letters received, newest bundle first, `Boundary` before the
/// passage's first cell, and the reader of the next letters (the clock at the register's cut).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActiveAddress {
    letters: Vec<Letter>,
    reader: LetterReader,
}

impl ActiveAddress {
    /// **The address before any cell**, the cell-only family: `D` boundary letters.
    pub fn boundary(depth: usize) -> Self {
        Self {
            letters: vec![Letter::Boundary; depth],
            reader: LetterReader::cells(),
        }
    }

    /// **The resident's address register** for a field at a lift point: at the deepest declared
    /// receiver's depth, each receiver reading its own first `D` letters, with the field's declared
    /// letter family ([`letter_family`]).
    pub fn of_field(field: &Field, current: &Current) -> Result<Self, HnnError> {
        let depth = field
            .receivers()
            .iter()
            .map(|receiver| receiver.depth)
            .max()
            .unwrap_or(0);
        Ok(Self {
            letters: vec![Letter::Boundary; depth],
            reader: LetterReader::of(field, letter_family(field), current)?,
        })
    }

    /// **A register of depth `D` with a declared reader**, before any cell.
    pub fn of_reader(depth: usize, reader: LetterReader) -> Self {
        Self {
            letters: vec![Letter::Boundary; depth],
            reader,
        }
    }

    /// `D`.
    pub fn depth(&self) -> usize {
        self.letters.len()
    }

    /// The letters, newest first.
    pub fn letters(&self) -> &[Letter] {
        &self.letters
    }

    /// The reader of the next letters.
    pub fn reader(&self) -> &LetterReader {
        &self.reader
    }

    /// **Receive one cell** (the clock-only letters): its tick's letter becomes the newest, and the
    /// oldest leaves. Refused when the family declares contact letters (their readings are
    /// [`ActiveAddress::receive_read`]'s).
    pub fn receive(&mut self, cell: usize) -> Result<(), HnnError> {
        self.receive_read(cell, &[])
    }

    /// **Receive one cell with its contacts' readings at its tick**.
    pub fn receive_read(
        &mut self,
        cell: usize,
        contacts: &[ContactReading],
    ) -> Result<(), HnnError> {
        let letter = self.reader.tick(cell, contacts)?;
        if !self.letters.is_empty() {
            self.letters.pop();
            self.letters.insert(0, letter);
        }
        Ok(())
    }

    /// **Take the clock from a lift point** after a re-keying (the letters already read keep their
    /// ticks' values: Lean `bundle_causal`).
    pub fn synchronize(&mut self, field: &Field, current: &Current) -> Result<(), HnnError> {
        self.reader.synchronize(field, current)
    }

    /// **The address's first `depth` letters** (a receiver of a shallower tree), with its reader,
    /// refused past the register's depth.
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
            reader: self.reader.clone(),
        })
    }

    /// **Phase `j`'s address** (module header; Lean `HNN/LandmarkAddress.bundle_causal`): the
    /// letters of the window's cells before phase `j` that are known, newest first (read by a copy
    /// of the register's clock stepped over `known[0], …, known[j−1]`, at most the `known.len()` of
    /// them), then this suffix, truncated to its depth. At a compare every earlier target is known,
    /// so this is `hnn::landmark::letter_address` of the passage's letters at `p + j`; at a release
    /// no cell of the window is known and every phase reads the window's opening address
    /// (`hnn::port`'s release). The target of phase `j` is never read. Refused when the family
    /// declares contact letters.
    pub fn phase(&self, known: &[usize], j: usize) -> Result<Vec<Letter>, HnnError> {
        let depth = self.letters.len();
        let mut reader = self.reader.clone();
        let mut window = known[..j.min(known.len())]
            .iter()
            .map(|&cell| reader.tick(cell, &[]))
            .collect::<Result<Vec<Letter>, HnnError>>()?;
        window.reverse();
        Ok(window
            .into_iter()
            .chain(self.letters.iter().copied())
            .take(depth)
            .collect())
    }

    /// **Its exact bits**: each letter one of the family's bundle codes with the boundary
    /// (`1 + |A| Π_i s_i`, [`LetterFamily::bundle_codes`]; `|A| + 1` for the cell-only family), and
    /// the reader's clock.
    pub fn bits(&self, alphabet: usize) -> u64 {
        self.letters.len() as u64
            * ceil_log2(&BigUint::from(self.reader.family.bundle_codes(alphabet)))
            + self.reader.bits()
    }
}

/// [definition; agent-inferred] **The field's declared letter family** (campaign 2, decided on the
/// development cells by `hnn_landmark`'s harness, Decision 31): the receiving letters every
/// receiver's tree is addressed by. The harness's receipt (the notebook README's `hnn_landmark`
/// row) chose the cell-only family: no clock-only family lowered the development code length by its
/// description charge.
pub fn letter_family(_field: &Field) -> LetterFamily {
    LetterFamily::cells()
}

/// [definition; agent-inferred] **The clock-only letters of a passage** (the development harness's
/// letters, Decision 31): the resident's clock law replayed without the wave. Each cell steps the
/// lift point (`Current::step`) and its tick's letter is read after the step; at the joint clock's
/// carry-out the keys are located on the closing crib (its last `W_crib` cells, the aeon's own,
/// read at the declared offset: `keys::locate_closing`, as the exposure locates them) and re-key
/// the lift point, which the reader takes. A family with contact letters is refused (their
/// readings need the word).
pub fn clock_letters(
    field: &Field,
    family: &LetterFamily,
    cells: &[usize],
) -> Result<Vec<Letter>, HnnError> {
    let mut current = Current::at_rest(field);
    let mut reader = LetterReader::of(field, family.clone(), &current)?;
    let crib = field.crib();
    let mut aeon_start = 0usize;
    let mut letters = Vec::with_capacity(cells.len());
    for (at, &cell) in cells.iter().enumerate() {
        let step = current.step(field, cell)?;
        letters.push(reader.tick(cell, &[])?);
        if step.carry_out {
            let end = at + 1;
            let from = end.saturating_sub(crib.window).max(aeon_start);
            if end - from > crib.offset {
                let location =
                    keys::locate_closing(field, &current, &cells[from..end], crib.offset)?;
                location.rekey(field, &mut current)?;
                reader.synchronize(field, &current)?;
            }
            aeon_start = end;
        }
    }
    Ok(letters)
}

/// [definition; agent-inferred] **The landmark tree a receiver declares** (module header): the
/// field's exterior chart `|A|` (the cell emitted as its odometer digits), the receiver's depth `D`
/// with no forced split, the field's declared population (the passage the tree's certificates hold
/// within), the receiver's grain `L_R = ⌈1/ε_bits⌉` and the field's letter family
/// ([`letter_family`]), from which the owner derives its widths (the path lattice `M_p`, the β
/// carrier `W` and, past `u128`, the carrier's rebase `R`).
pub fn landmark_declaration(
    field: &Field,
    receiver: &ReceiverDeclaration,
) -> Result<LandmarkDeclaration, HnnError> {
    landmark_declaration_with(field, receiver, letter_family(field))
}

/// **The landmark tree a receiver declares with a given family** (the harness's and the tests').
pub fn landmark_declaration_with(
    field: &Field,
    receiver: &ReceiverDeclaration,
    family: LetterFamily,
) -> Result<LandmarkDeclaration, HnnError> {
    Ok(LandmarkDeclaration {
        alphabet: field.alphabet(),
        depth: receiver.depth,
        forced: 0,
        population: field.population(),
        grain: grain_of(&receiver.tolerance)?,
        family,
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
// the mixture of the tree and the combined face

/// [definition; agent-inferred] **The receiver's scored face is weighed like a landmark** (the
/// primary's ruling A, from Decision 28's own law, which weighs every landmark by its code-length
/// evidence and not by a rule): the two-way mixture of the tree's face `q_T` and the combined face
/// `q_C` (the tree's grain logits plus the wave), weighted by their prequential likelihood ratio,
/// exactly as a tree node weighs its own KT face against its split:
///
/// ```text
/// q = λ q_T + (1 − λ) q_C ,   λ = β/(1 + β) ,   β = W_T/W_C = 1 at the opening (prior ½/½)
/// β' = β · q_T(x)/q_C(x)      after each cell x, in cell order: phase j of a window reads β after phases < j
/// ∏ q = ½ W_T + ½ W_C ,       min(L_T, L_C) ≤ L_model ≤ min(L_T, L_C) + 1 bit          (ideal)
/// L_model ≤ min(L_T, L_C) + 1 bit + Σ |log₂ ρ|      the executed chart, ρ its factor a step
/// ```
///
/// Any `λ ∈ [0, 1]` keeps `q` a positive normalized face (Lean
/// `HNN/LandmarkTree.path_face_normalized`), so the executed mixture is exactly scored. The
/// telescope and the bounds are Lean `HNN/LandmarkTree.{sequential_mixture,
/// sequential_mixture_bounds}` (the two-child case of `kraft_and_dominance`), which hold only when
/// each cell's weight is the ratio after every earlier cell; with the ratio carried by a chart they
/// are `sequential_mixture_executed`, the drift `Σ_t |log₂ ρ_t|` added once. `q_C(x)` lives in
/// `ℚ(θ)`, so `β` steps by a declared rational chart of it: the lower endpoint of its exact
/// enclosure at the carried power's reading bits, whose certified residual `|log₂ q_C − log₂ q̃_C|`
/// is at most `(hi − lo)/lo · 3/2` (`|ln x| ≤ |x − 1|/min(x, 1)`, `log₂ e < 3/2`), carried rounded
/// up on the dyadic grid `2^(−128)` so the drift's sum keeps one denominator. `β` is carried
/// on the landmark β chart (`hnn::landmark::Beta`: odd over odd times `2^e`) at the tree's carrier
/// width `W`, rebased to its `W`-bit mantissa when its odd parts outgrow it, with the certified
/// residual `|log₂(1 − r)| < 3 · 2^(−W)` a rebase. A step's factor is `ρ = q̃_C/(q_C (1 − r))`, so
/// its drift (the sum of both residuals over its steps) bounds `Σ |log₂ ρ|`, and it is reported,
/// never silent. The wave still learns from its own comparison, the covector of `q_C` against the
/// target, and the tree's face is stored, not pulled back; the mixture is scored on the host at
/// compare, beside the tree read, on every realization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mixture {
    beta: Beta,
    width: u64,
    rebases: u64,
    drift: Rat,
}

/// [definition] **One reached comparison's step of the mixture's ratio** `β' = β q_T(x)/q̃_C(x)`:
/// its receiving ring, the tree's executed face of the target `q_T(x)`, the combined face's
/// rational chart `q̃_C(x)` and the chart's certified residual in bits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MixtureStep {
    pub ring: usize,
    pub tree: Rat,
    pub combined: Rat,
    pub residual: Rat,
}

/// [definition] **A window scored by the mixture**: each phase's code length under the mixture
/// `q` (the model's) and under the tree's executed face `q_T` alone (the face the mixture weighs,
/// `hnn::landmark::code_length` of `q_T(t_j)`), and the steps its deposit applies to `β` in cell
/// order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Scored {
    pub model: Vec<ExactInterval>,
    pub tree: Vec<ExactInterval>,
    pub steps: Vec<MixtureStep>,
}

impl Mixture {
    /// **The opening mixture**: `β = 1`, the prior ½/½, carried at width `W`.
    pub fn new(width: u64) -> Self {
        Self {
            beta: Beta::ONE,
            width,
            rebases: 0,
            drift: Rat::zero(),
        }
    }

    /// `β = W_T/W_C`, exact.
    pub fn beta(&self) -> Rat {
        self.beta.value()
    }

    /// `λ = β/(1 + β)`, the tree's weight.
    pub fn weight(&self) -> Rat {
        let beta = self.beta();
        &beta / (Rat::one() + &beta)
    }

    /// The carrier width `W`.
    pub fn width(&self) -> u64 {
        self.width
    }

    /// The rebases so far.
    pub fn rebases(&self) -> u64 {
        self.rebases
    }

    /// The certified drift of the carried `β` against the exact likelihood ratio, in bits.
    pub fn drift(&self) -> &Rat {
        &self.drift
    }

    /// **`log₂ β`, enclosed** by the certified binary logarithm (`hnn::landmark::code_length` of
    /// `1/β`).
    pub fn log2_beta(&self) -> Result<ExactInterval, HnnError> {
        code_length(&self.beta().recip())
    }

    /// **Its exact bits**: `β`'s numerator and denominator, each by its bits.
    pub fn bits(&self) -> u64 {
        let beta = self.beta();
        beta.numer().bits() + beta.denom().bits()
    }

    /// **One step** `β' = β q_T(x)/q̃_C(x)`, carried at `W` (module header of this section).
    /// Refused at a face that is not positive.
    pub fn step(&mut self, step: &MixtureStep) -> Result<(), HnnError> {
        if !step.tree.is_positive() || !step.combined.is_positive() {
            return Err(HnnError::Shape {
                what: "positive faces in the mixture's step",
                expected: 1,
                found: 0,
            });
        }
        let value = self.beta() * &step.tree / &step.combined;
        let (beta, rebased) = carry_ratio(&value, self.width);
        self.beta = beta;
        self.drift += &step.residual;
        if rebased {
            self.rebases += 1;
            self.drift += Rat::new(BigInt::from(3), BigInt::one() << self.width as usize);
        }
        Ok(())
    }

    /// **Score a window in cell order** (module header of this section; Lean
    /// `HNN/LandmarkTree.sequential_mixture`): phase `j` reads `β_j`, the carried ratio after the
    /// window's earlier phases' steps (their targets are known at compare), the tree's face
    /// `q_T,j(t_j)` and the combined face's exact enclosure `q_C,j(t_j) ∈ [lo, hi]`, so the mixture
    /// `q_j(t_j) ∈ [λ_j q_T + (1 − λ_j) lo, λ_j q_T + (1 − λ_j) hi]` and its code length is enclosed
    /// by the certified binary logarithm. Its step `β_(j+1) = β_j q_T/q̃_C` (the chart `q̃_C = lo`)
    /// is taken on a local copy of the ratio by [`Mixture::step`] and staged, so the deposit, which
    /// applies the staged steps in cell order by the same step, reaches the same carried `β`. The
    /// tree's own code length `−log₂ q_T,j(t_j)` is returned beside it. Refused unless there is one
    /// combined face, one tree face and one target per phase.
    pub fn score(
        &self,
        ring: usize,
        combined: &Faces,
        trees: &[LandmarkFace],
        targets: &[usize],
    ) -> Result<Scored, HnnError> {
        if combined.faces.len() != trees.len() || trees.len() != targets.len() {
            return Err(HnnError::Shape {
                what: "one combined face, one tree face and one target per phase",
                expected: trees.len(),
                found: targets.len(),
            });
        }
        let mut local = self.clone();
        let mut scored = Scored {
            model: Vec::with_capacity(targets.len()),
            tree: Vec::with_capacity(targets.len()),
            steps: Vec::with_capacity(targets.len()),
        };
        for ((face, tree), &target) in combined.faces.iter().zip(trees).zip(targets) {
            let weight = local.weight();
            let rest = Rat::one() - &weight;
            let q_tree = tree
                .probabilities
                .get(target)
                .ok_or(HnnError::CellOutside {
                    code: target,
                    alphabet: tree.probabilities.len(),
                })?
                .clone();
            let q_combined = face_enclosure(face, target)?;
            let lower = &weight * &q_tree + &rest * &q_combined.lower;
            let upper = &weight * &q_tree + &rest * &q_combined.upper;
            let (short, long) = (code_length(&upper)?, code_length(&lower)?);
            scored
                .model
                .push(ExactInterval::new(short.lower, long.upper).map_err(|_| {
                    HnnError::Shape {
                        what: "an ordered enclosure of the mixture's code length",
                        expected: 0,
                        found: 1,
                    }
                })?);
            let residual = grid_ceiling(
                &((&q_combined.upper - &q_combined.lower) / &q_combined.lower
                    * Rat::new(BigInt::from(3), BigInt::from(2))),
            );
            scored.tree.push(code_length(&q_tree)?);
            let step = MixtureStep {
                ring,
                tree: q_tree,
                combined: q_combined.lower,
                residual,
            };
            local.step(&step)?;
            scored.steps.push(step);
        }
        Ok(scored)
    }
}

/// [definition; agent-inferred] **A residual bound carried on the drift's dyadic grid**
/// `2^(−2·READING_BITS)` (twice the carried power's reading bits, which bound the chart's residual
/// from below by about `2^(−READING_BITS)`), rounded up: the drift's sum over a passage keeps one
/// bounded denominator instead of the least common multiple of every step's.
fn grid_ceiling(value: &Rat) -> Rat {
    let bits = 2 * crate::ratio::exponentiated::READING_BITS as usize;
    let scale = BigInt::one() << bits;
    let scaled = value * Rat::from_integer(scale.clone());
    Rat::new(scaled.ceil().to_integer(), scale)
}

/// **A positive ratio carried on the landmark β chart at width `W`**: exactly when its odd parts
/// fit `W` bits, otherwise rebased to its `W`-bit mantissa `m = ⌊v 2^s⌋ ∈ [2^(W−1), 2^W)`; the flag
/// says whether it was rebased.
fn carry_ratio(value: &Rat, width: u64) -> (Beta, bool) {
    let (numerator, denominator) = (value.numer().magnitude(), value.denom().magnitude());
    let (twos_n, twos_d) = (
        numerator.trailing_zeros().unwrap_or(0),
        denominator.trailing_zeros().unwrap_or(0),
    );
    let (a, b) = (numerator >> twos_n, denominator >> twos_d);
    let exponent = twos_n as i64 - twos_d as i64;
    if a.bits() <= width && b.bits() <= width {
        let (beta, _) = Beta::carry(
            a.to_u128().expect("an odd part within the carrier width"),
            b.to_u128().expect("an odd part within the carrier width"),
            exponent,
            width,
        );
        return (beta, false);
    }
    // `a/b ∈ (2^(t−1), 2^(t+1))`, `t = bits(a) − bits(b)`, so `a 2^s/b ∈ (2^(W−1), 2^(W+1))` at
    // `s = W − t`.
    let floor = |shift: i64| -> BigUint {
        if shift >= 0 {
            (&a << shift as usize) / &b
        } else {
            &a / (&b << shift.unsigned_abs() as usize)
        }
    };
    let mut shift = width as i64 - (a.bits() as i64 - b.bits() as i64);
    let mut mantissa = floor(shift);
    if mantissa.bits() > width {
        shift -= 1;
        mantissa = floor(shift);
    }
    let (beta, _) = Beta::carry(
        mantissa
            .to_u128()
            .expect("a mantissa within the carrier width"),
        1,
        exponent - shift,
        width,
    );
    (beta, true)
}

/// **The exact enclosure of one class's face** `p̂_c = 2^(n_c − n_top) θ^(k_c)/Z` in the real chart
/// `θ ↦ 2^(1/L)` at the carried power's reading bits: the carried power's enclosure over the
/// normalizer's.
fn face_enclosure(face: &Face, class: usize) -> Result<ExactInterval, HnnError> {
    let cells = face.cells();
    let cell = cells.get(class).ok_or(HnnError::CellOutside {
        code: class,
        alphabet: cells.len(),
    })?;
    let top = cells
        .iter()
        .map(|cell| cell.carry.clone())
        .max()
        .expect("a face over at least one class");
    let power = CarriedPower::new(&cell.carry - &top, cell.phase, face.grain())?
        .value()?
        .enclosure()?;
    let normalizer = face.normalizer().enclosure()?;
    ExactInterval::new(
        &power.lower / &normalizer.upper,
        &power.upper / &normalizer.lower,
    )
    .map_err(|_| HnnError::Shape {
        what: "an ordered enclosure of a face",
        expected: 0,
        found: 1,
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
        (0..self.aperture)
            .map(|j| address.phase(known, j))
            .collect()
    }

    /// **The tree faces of one window, in cell order** (module header): the receiving parametron's
    /// tree read at each phase's address, every class's executed face with its grain exponent,
    /// phase `j` at the standing after the deposits of the known earlier phases' targets
    /// (`hnn::landmark::Landmarks::window_faces`: a working overlay, the published tree unchanged;
    /// at a release nothing is known and every phase reads the published standing). The phases then
    /// read together (`hnn::realization`). Refused when the constitution carries no tree on the
    /// receiving ring.
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
        tree.window_faces(&addresses, known, self.grain)
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

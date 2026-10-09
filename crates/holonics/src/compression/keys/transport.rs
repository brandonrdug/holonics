//! **The located transport: each occurrence steps the rings by its located advance** (THE_REBUILD
//! U6, lanes E and B: the helical encoding's missing operation; the
//! [record](../../../../../research/records/2026-10-05_THE_LOCATED_TRANSPORT_EACH_OCCURRENCE_STEPS_THE_RINGS_BY_ITS_LOCATED_ADVANCE.md)).
//!
//! [proved-derived] An occurrence `k` of a source enters at the navigators' phases after its
//! admitted steps, `m_g = Σ_k Ĝ_g(τ_g(k))⁻¹ E(u_k)` (`Transport/SourceMoment`). The phases are one
//! lift `ℓ ∈ ℤ/D`, `D = ∏ d_g`, of the rings' joint clock, and the cell's **located transport**
//! `A(u) ∈ ℤ/D` steps it:
//!
//! ```text
//! ℓ(k+1) = ℓ(k) + A(u_k)                       the address: ℓ(k) = ℓ(0) + Σ_(j<k) A(u_j)
//! odometer chart: τ_g(k+1) = τ_g(k) + a_g(u_k) + carry_g(k) (mod d_g),
//!                 carry_(g+1)(k) = ⌊(τ_g(k) + a_g(u_k) + carry_g(k)) / d_g⌋,  A(u) = Σ_g a_g(u) ∏_(h<g) d_h
//! CRT chart (pairwise coprime d_g): r_g(k+1) = r_g(k) + (A(u_k) mod d_g), no carry
//! ```
//!
//! The two charts are one lift ([`CarryHelix::digits`], [`CarryHelix::residues`]; the odometer is
//! `geometry::winding::Odometer`, whose carry is the defect of additivity, Lean
//! `Geometry/PhaseCarry.winding_add`). The occurrence count's residues `k mod d_g` carry order only
//! at the identity advance; under a located transport the lift is the source word's address.
//!
//! [definition; agent-inferred, October 5] **The receiving chart** reads the last ring's digit, the
//! lift at the grain `D_low = ∏_(g<last) d_g`: `c(ℓ) = ⌊ℓ / D_low⌋`, through injective labels
//! `λ` (cell to class). The hidden rings below it reach the reading only through their joint winding,
//! the carry word into the receiving ring (the winding is the carry), so what a receiver locates is
//! `A(u) ∈ ℤ/D`, each digit `a_g(u)` following from the mixed-radix bijection.
//!
//! [proved-derived; checked by the owner's brute-force test] **The gauge is dihedral.** Every passage
//! is read alike under the receiving ring's rotation `ℓ ↦ ℓ + j D_low`, `λ ↦ λ∘ρ^(−j)`, and under the
//! reflection `ℓ ↦ D_low − 1 − ℓ`, `A ↦ −A`, `λ ↦ λ∘(c ↦ −c)`: the digits of `D − 1 − ℓ` are
//! `d_g − 1 − τ_g`, so the receiving digit reflects and the step negates, and the turn by one cell
//! returns the read set's first cell to `0`. The rotation is fixed by the convention that the read
//! set's first emission reads the receiving digit `0`; the reflection is kept, and a fibre is read in
//! its classes, each class's representative chosen in the classes' first-occurrence order, so the
//! choice reads no label (the relabelling law, below).
//!
//! [definition; agent-inferred] **Location by loop closure** ([`TransportLocation`]). The machine's
//! own family: rings of the declared periods with carry, every transport, every injective label map,
//! every key. A survivor is a partial transport, a partial label map and the lifts it still admits.
//! Each emission closes the loop since its class's last visit: the lift must lie in the cell its
//! class is labelled with, so a recurrence `u_k = u_k′` declares
//! `c(ℓ(0) + Σ_(j<k) A(u_j)) = c(ℓ(0) + Σ_(j<k′) A(u_j))`, and two different classes declare
//! different cells. A class's first step branches its advance over `ℤ/D`; nothing is set by a
//! class's code. Adding an emission only removes survivors (a failed survivor stays failed, Lean
//! `Keys.fibre_cons`), apart from the branching of an advance or a label read for the first time.
//! The survivors are the future-sufficient quotient of the key fibre: a survivor keeps the lifts it
//! admits now, not the history that produced them.
//!
//! [proved-derived] **The relabelling law.** Location reads only the equality of occurrences, so for
//! every permutation `π` of the classes the survivors on `π∘x` are those on `x` with each advance
//! and label carried by `π`: the located transport on `π∘x` is `A∘π⁻¹`, and the navigator's code
//! length (below) is unchanged, `L(π∘x) = L(x)`. A transport chosen by a class's code (the residue
//! chart `[u mod d_g ∈ N_g]`) is not carried by `π`, and its code length changes.
//!
//! [definition] **The navigator's code** ([`located_code`], [`residual_code`], an actual prefix code
//! over the declared `D`, `|A|`, passage count and lengths): the transport per receiving cell in
//! `⌈log₂ D⌉` bits each, then the residual: the labels as a permutation index in `⌈log₂ |A|!⌉` bits,
//! each passage's key in `⌈log₂ D⌉` bits, a patch count in `⌈log₂(n + 1)⌉` bits, and each patch as
//! its position in `⌈log₂ n⌉` bits and its class among the other `|A| − 1` in `⌈log₂(|A| − 1)⌉`
//! bits. The decoder steps the lift by the decoded cell's advance (the source steps the rings) and
//! reads each next cell through the labels ([`read_residual`]).
//!
//! [definition; agent-inferred] **Repair through the located navigator** ([`LocatedTransport::restrict`]).
//! With the transport and labels located, a damaged passage's lift families are restricted from
//! both sides through `F(ℓ) = ℓ + A(λ(c(ℓ)))`: an intact cell admits its cell's lifts, an erased one
//! every lift, and
//!
//! ```text
//! L_(t+1) ← L_(t+1) ∩ F(L_t),     L_t ← L_t ∩ F⁻¹(L_(t+1))       to the fixed point
//! ```
//!
//! The edges `(t, t + 1)` are one chain, so the fixed point is the joint fibre's projection
//! (arc consistency on an acyclic constraint graph is global consistency, the repair owner's law);
//! the owner checks it exactly against the joint fibre, the keys whose orbit meets every intact cell.
//! An erased cell is released through `receiver::release` at tolerance zero when its class family is
//! one certified class, held otherwise ([`LiftRestriction::release`]). A plural fibre restricts
//! through every member ([`restrict_fibre`]): a member the passage refuses leaves, and a cell's
//! family is the union of the members' families, so a cell is released only where every member
//! agrees. The residual is the repair owner's, the truth's index in the first held family, pinned
//! and re-run ([`lift_residual`], [`lift_reopen`]).
//!
//! | Law | Lean | Rust |
//! |---|---|---|
//! | the odometer and CRT charts are one lift; the carry is the defect of additivity | `Geometry/PhaseCarry.winding_add`, `odometer_iterate`; the CRT chart owed (#62) | [`CarryHelix`] |
//! | the dihedral gauge of the receiving chart | owed (#62) | [`LocatedTransport::reflected`], the owner's brute-force test |
//! | a failed survivor stays failed | `Keys.fibre_cons` | [`TransportLocation::locate`] |
//! | the relabelling law `L(π∘x) = L(x)` | owed (#62) | the owner's relabelling test |
//! | the restriction's fixed point is the joint fibre's projection on a chain | owed (#62, the repair owner's item) | [`LiftRestriction::certified`] |
//! | the residual reopens the source | `Transport/Fold.reopen_apply_fold`, `residual_injective_on_fibre` | [`lift_reopen`], [`read_residual`] |

use num_bigint::BigUint;
use num_traits::{One, Zero};

use crate::compression::CompressionError;
use crate::compression::cost::{ceil_log2, read_index, write_index};
use crate::holarchy::terrain::Draw;
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;

use super::repair::{CellRelease, decide};

/// The ceiling on a helix's joint period `D`: every location branches an advance over `ℤ/D`, and
/// the encoding consumer's chart is `ℚ^D`.
///
/// \[definition; agent-inferred\] A declared-size guard at the order of the image family's
/// ceiling (`super::IMAGE_FAMILY_CEILING`), refused before any allocation.
pub const HELIX_PERIOD_CEILING: u64 = 1 << 12;

/// The ceiling on the classes a navigator's code ranks as one permutation index (`|A|!` within a
/// machine word).
pub const LABEL_CEILING: usize = 12;

fn helix_refusal(reason: &'static str) -> CompressionError {
    CompressionError::Helix { reason }
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

fn bits(population: u64) -> u64 {
    ceil_log2(&BigUint::from(population))
}

// -------------------------------------------------------------------------------------------
// the helix

/// [definition] **The carry helix** (module header): closing rings of pairwise coprime periods
/// cascaded as an odometer, ring 0 least significant; the last ring is the receiving ring.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CarryHelix {
    periods: Vec<u64>,
    period: u64,
    grain: u64,
}

impl CarryHelix {
    /// A helix; refused unless it has at least two rings, each of period at least two, the periods
    /// pairwise coprime, and the joint period within [`HELIX_PERIOD_CEILING`].
    pub fn new(periods: Vec<u64>) -> Result<Self, CompressionError> {
        if periods.len() < 2 || periods.iter().any(|&d| d < 2) {
            return Err(helix_refusal(
                "a helix has a hidden ring and a receiving ring, each of period at least two",
            ));
        }
        for (g, &d) in periods.iter().enumerate() {
            if periods[..g].iter().any(|&e| gcd(d, e) != 1) {
                return Err(helix_refusal("the rings' periods are pairwise coprime"));
            }
        }
        let period = periods
            .iter()
            .try_fold(1u64, |product, &d| product.checked_mul(d))
            .filter(|&product| product <= HELIX_PERIOD_CEILING)
            .ok_or_else(|| helix_refusal("the joint period lies within the helix ceiling"))?;
        let grain = period / periods[periods.len() - 1];
        Ok(Self {
            periods,
            period,
            grain,
        })
    }

    /// The rings' periods `d_g`, ring 0 least significant.
    pub fn periods(&self) -> &[u64] {
        &self.periods
    }

    /// The joint period `D = ∏ d_g`.
    pub fn period(&self) -> u64 {
        self.period
    }

    /// The receiving grain `D_low = ∏_(g<last) d_g`.
    pub fn grain(&self) -> u64 {
        self.grain
    }

    /// The receiving ring's period, its cell count.
    pub fn cells(&self) -> u64 {
        self.periods[self.periods.len() - 1]
    }

    /// The receiving cell `c(ℓ) = ⌊ℓ / D_low⌋`.
    pub fn cell(&self, lift: u64) -> u64 {
        (lift % self.period) / self.grain
    }

    /// The lifts of one receiving cell, `[c D_low, (c + 1) D_low)`.
    pub fn cell_lifts(&self, cell: u64) -> impl Iterator<Item = u64> {
        cell * self.grain..(cell + 1) * self.grain
    }

    /// **The odometer chart**: the lift's digits `τ_g`, ring 0 first.
    pub fn digits(&self, lift: u64) -> Vec<u64> {
        let mut rest = lift % self.period;
        self.periods
            .iter()
            .map(|&d| {
                let digit = rest % d;
                rest /= d;
                digit
            })
            .collect()
    }

    /// **The CRT chart**: the lift's residues `ℓ mod d_g`.
    pub fn residues(&self, lift: u64) -> Vec<u64> {
        self.periods.iter().map(|&d| lift % d).collect()
    }

    /// **The lift of a residue tuple**: the unique `ℓ ∈ [0, D)` with `residues(ℓ) = r`, the inverse
    /// of [`CarryHelix::residues`] on the declared fundamental domain.
    ///
    /// [proved-derived] The periods are pairwise coprime, so two addresses below the product with
    /// equal residues are equal and every tuple below the periods is attained (`D` addresses, `D`
    /// tuples): Lean `HNN/Prediction.joint_residue_determines_position`, the Chinese remainder
    /// theorem. The lift is rebuilt ring by ring, `ℓ_g = ℓ_(g−1) + (d_0⋯d_(g−1)) t_g` with the one
    /// digit `t_g < d_g` that matches `r_g` (Garner's recurrence, a scan of at most `d_g`
    /// candidates a ring). The residues fix the lift only modulo the product: the absolute position
    /// needs the whole winding `ℓ div D` (kept by [`LocatedTransport::lifts`]) or a declared
    /// fundamental domain, here `[0, D)`. Refused with a wrong length or a residue `r_g ≥ d_g`.
    pub fn of_residues(&self, residues: &[u64]) -> Result<u64, CompressionError> {
        if residues.len() != self.periods.len()
            || residues.iter().zip(&self.periods).any(|(&r, &d)| r >= d)
        {
            return Err(helix_refusal(
                "a residue chart has one residue below each ring's period",
            ));
        }
        let mut lift = residues[0];
        let mut modulus = self.periods[0];
        for (&r, &d) in residues.iter().zip(&self.periods).skip(1) {
            let turns = (0..d)
                .find(|&t| (lift + modulus * t) % d == r)
                .ok_or_else(|| helix_refusal("pairwise coprime rings determine a lift"))?;
            lift += modulus * turns;
            modulus *= d;
        }
        Ok(lift)
    }

    /// The lift of digits, `Σ_g τ_g ∏_(h<g) d_h`.
    pub fn of_digits(&self, digits: &[u64]) -> u64 {
        digits
            .iter()
            .zip(&self.periods)
            .rev()
            .fold(0, |lift, (&digit, &d)| lift * d + digit)
    }

    /// **The odometer's step with its carries**: `τ_g + a_g + carry_g`, each ring's carry out into
    /// the next, and the last ring's carry out (the joint clock's turn).
    pub fn step_digits(&self, digits: &[u64], advance: &[u64]) -> (Vec<u64>, Vec<u64>) {
        let mut carry = 0;
        let mut carries = Vec::with_capacity(self.periods.len());
        let stepped = digits
            .iter()
            .zip(advance)
            .zip(&self.periods)
            .map(|((&tau, &a), &d)| {
                let sum = tau + a + carry;
                carry = sum / d;
                carries.push(carry);
                sum % d
            })
            .collect();
        (stepped, carries)
    }
}

// -------------------------------------------------------------------------------------------
// the known-truth terrain

/// [definition; agent-inferred] **A stepped terrain**, known truth generated by an exact routine:
/// the helix, the transport `A(u) ∈ ℤ/D` of each class and the receiving chart's labels (cell to
/// class, a bijection). Its passage from the key `ℓ(0)` is autonomous: `u_k = λ(c(ℓ(k)))`,
/// `ℓ(k+1) = ℓ(k) + A(u_k)`. The machine reads only the emitted classes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SteppedTerrain {
    helix: CarryHelix,
    advances: Vec<u64>,
    labels: Vec<usize>,
}

impl SteppedTerrain {
    /// A terrain; refused unless the labels are a bijection of the receiving cells and every
    /// advance lies in `ℤ/D`.
    pub fn new(
        helix: CarryHelix,
        advances: Vec<u64>,
        labels: Vec<usize>,
    ) -> Result<Self, CompressionError> {
        let cells = usize::try_from(helix.cells()).expect("a cell count fits");
        let mut seen = vec![false; cells];
        if labels.len() != cells
            || advances.len() != cells
            || advances.iter().any(|&a| a >= helix.period())
        {
            return Err(helix_refusal(
                "a terrain labels every receiving cell with one class and steps each class in ℤ/D",
            ));
        }
        for &class in &labels {
            if class >= cells || std::mem::replace(&mut seen[class], true) {
                return Err(helix_refusal("the terrain's labels are a bijection"));
            }
        }
        Ok(Self {
            helix,
            advances,
            labels,
        })
    }

    /// **The terrain's draw** (the order the record pins): each class's advance below `D`, then the
    /// labels by a uniform shuffle of the cells (each cell, in order, takes a uniform class among
    /// those left).
    pub fn draw(helix: CarryHelix, draw: &mut Draw) -> Self {
        let cells = usize::try_from(helix.cells()).expect("a cell count fits");
        let period = usize::try_from(helix.period()).expect("a period fits");
        let advances = (0..cells).map(|_| draw.below(period) as u64).collect();
        let mut left: Vec<usize> = (0..cells).collect();
        let labels = (0..cells)
            .map(|_| left.remove(draw.below(left.len())))
            .collect();
        Self {
            helix,
            advances,
            labels,
        }
    }

    /// The helix.
    pub fn helix(&self) -> &CarryHelix {
        &self.helix
    }

    /// `A(u)` of each class.
    pub fn advances(&self) -> &[u64] {
        &self.advances
    }

    /// The labels, cell to class.
    pub fn labels(&self) -> &[usize] {
        &self.labels
    }

    /// **The passage** of `length` cells from the key `ℓ(0)`.
    pub fn passage(&self, key: u64, length: usize) -> Vec<usize> {
        let mut lift = key % self.helix.period();
        (0..length)
            .map(|_| {
                let class = self.labels[self.helix.cell(lift) as usize];
                lift = (lift + self.advances[class]) % self.helix.period();
                class
            })
            .collect()
    }
}

// -------------------------------------------------------------------------------------------
// the located transport

/// [definition] **A located transport** (module header): the helix, each class's advance and the
/// labels (cell to class, injective).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocatedTransport {
    helix: CarryHelix,
    advances: Vec<u64>,
    labels: Vec<Option<usize>>,
}

impl LocatedTransport {
    /// A located transport; refused unless each advance lies in `ℤ/D`, the labels read every cell
    /// and are injective onto the classes.
    pub fn new(
        helix: CarryHelix,
        advances: Vec<u64>,
        labels: Vec<Option<usize>>,
    ) -> Result<Self, CompressionError> {
        let mut seen = vec![false; advances.len()];
        if labels.len() as u64 != helix.cells() || advances.iter().any(|&a| a >= helix.period())
        {
            return Err(helix_refusal(
                "a located transport reads every receiving cell and steps in ℤ/D",
            ));
        }
        for &class in labels.iter().flatten() {
            if class >= advances.len() || std::mem::replace(&mut seen[class], true) {
                return Err(helix_refusal("the located labels are injective onto the classes"));
            }
        }
        Ok(Self {
            helix,
            advances,
            labels,
        })
    }

    /// The located transport of a terrain's own truth (for the terrain's checks and the harness's
    /// scoring; never read by the location).
    pub fn of_terrain(terrain: &SteppedTerrain) -> Self {
        Self {
            helix: terrain.helix.clone(),
            advances: terrain.advances.clone(),
            labels: terrain.labels.iter().map(|&class| Some(class)).collect(),
        }
    }

    /// The helix.
    pub fn helix(&self) -> &CarryHelix {
        &self.helix
    }

    /// `A(u)` of each class.
    pub fn advances(&self) -> &[u64] {
        &self.advances
    }

    /// The labels, cell to class.
    pub fn labels(&self) -> &[Option<usize>] {
        &self.labels
    }

    /// The class count `|A|`.
    pub fn classes(&self) -> usize {
        self.advances.len()
    }

    /// `A(u)` in the odometer chart: the digits `a_g(u)`.
    pub fn digits(&self, class: usize) -> Vec<u64> {
        self.helix.digits(self.advances[class])
    }

    /// `A(u)` in the CRT chart: `A(u) mod d_g`.
    pub fn residues(&self, class: usize) -> Vec<u64> {
        self.helix.residues(self.advances[class])
    }

    /// **The reflection gauge** (module header): `A ↦ −A`, `λ ↦ λ∘(c ↦ −c)`.
    pub fn reflected(&self) -> Self {
        let period = self.helix.period();
        let cells = self.labels.len();
        Self {
            helix: self.helix.clone(),
            advances: self.advances.iter().map(|&a| (period - a) % period).collect(),
            labels: (0..cells).map(|c| self.labels[(cells - c) % cells]).collect(),
        }
    }

    /// The key's image under the reflection gauge, `ℓ ↦ D_low − 1 − ℓ`.
    pub fn reflect_key(&self, key: u64) -> u64 {
        let period = self.helix.period();
        (self.helix.grain() + period - 1 - key % period) % period
    }

    /// The class the receiving chart reads at a lift, when its cell is labelled.
    pub fn emit(&self, lift: u64) -> Option<usize> {
        self.labels[self.helix.cell(lift) as usize]
    }

    /// The cell a class is labelled at.
    pub fn cell_of(&self, class: usize) -> Option<u64> {
        self.labels
            .iter()
            .position(|&label| label == Some(class))
            .map(|cell| cell as u64)
    }

    /// **The navigator's step** `F(ℓ) = ℓ + A(λ(c(ℓ)))`, when the lift's cell is labelled.
    pub fn step(&self, lift: u64) -> Option<u64> {
        self.emit(lift)
            .map(|class| (lift + self.advances[class]) % self.helix.period())
    }

    /// **The regenerated passage** of `length` cells from a key, or `None` past an unlabelled cell.
    pub fn regenerate(&self, key: u64, length: usize) -> Option<Vec<usize>> {
        let mut lift = key % self.helix.period();
        (0..length)
            .map(|_| {
                let class = self.emit(lift)?;
                lift = (lift + self.advances[class]) % self.helix.period();
                Some(class)
            })
            .collect()
    }

    /// **The absolute lifts of a word from a key**: the `n + 1` lifts
    /// `ℓ_0 = key mod D`, `ℓ_(k+1) = ℓ_k + A(u_k)` with no reduction. It reads no label.
    ///
    /// [definition] Helix = circle + carry: each lift is its phase `ℓ mod D` (what the receiving
    /// chart reads) and its whole winding `ℓ div D` (the carry), `ℓ = (ℓ div D) D + ℓ mod D`
    /// (Lean `Geometry/PhaseCarry.winding_add`). The driven reading's private stepping
    /// (`driven_patches`) takes the same steps modulo `D`; this keeps the winding it discards, and a
    /// consumer takes the quotient to `ℤ/D` only after the terminal carry probe is read. Refused
    /// with a class outside the advances and with an overflow of the machine word.
    pub fn lifts(&self, key: u64, word: &[usize]) -> Result<Vec<u64>, CompressionError> {
        let mut lift = key % self.helix.period();
        let mut lifts = Vec::with_capacity(word.len() + 1);
        lifts.push(lift);
        for &class in word {
            let advance = *self
                .advances
                .get(class)
                .ok_or(CompressionError::IndexOutside {
                    index: class,
                    population: self.advances.len(),
                })?;
            lift = lift
                .checked_add(advance)
                .ok_or_else(|| helix_refusal("an absolute lift stays within the machine word"))?;
            lifts.push(lift);
        }
        Ok(lifts)
    }

    /// **A passage's key fibre**: every key whose regenerated passage is the passage.
    pub fn keys(&self, passage: &[usize]) -> Vec<u64> {
        (0..self.helix.period())
            .filter(|&key| self.regenerate(key, passage.len()).as_deref() == Some(passage))
            .collect()
    }

    /// **The driven reading's patches** (module header, the code): stepping the lift by each actual
    /// class, the cells where the labelled reading differs from the passage (an unlabelled cell is a
    /// patch).
    pub fn patches(&self, passage: &[usize], key: u64) -> usize {
        driven_patches(&self.helix, &self.advances, &self.labels, passage, key).len()
    }

    /// **The encoding consumer's chart** on the helix `ℚ^D`, read in the receiving cells and never
    /// in the labels: each labelled cell's transport `T_c e_ℓ = e_(ℓ + A(λ(c)))`, in cell order; the
    /// receiving forms `ρ_c = Σ_(ℓ: c(ℓ) = c) e_ℓ*`, one per cell of the receiving ring; and an
    /// opening `e_k` per key. `hnn::encoding::PassageChart::located` reads them.
    ///
    /// [proved-derived; agent-inferred, October 5] The labels `λ` enter nowhere, so under the
    /// relabelling law (module header) the chart of `π∘x` is the chart of `x`: the transport of cell
    /// `c` is `A_(π∘x)(π λ(c)) = A_x(λ(c))`, and the founded encoding is equal, not only isomorphic
    /// (`transport::tests`, the located route). Its classes are the receiving ring's ports; the labels
    /// stay the boundary's decoder (`hnn::encoding::Encoded::label`).
    #[allow(clippy::type_complexity)]
    pub fn chart(
        &self,
        keys: &[u64],
    ) -> Result<(usize, Vec<ExactRatMatrix>, Vec<Vec<Rat>>, Vec<Vec<Rat>>), CompressionError> {
        let n = usize::try_from(self.helix.period()).expect("a period fits");
        let unit = |i: usize| {
            let mut vector = vec![Rat::zero(); n];
            vector[i] = Rat::one();
            vector
        };
        let transports = self
            .labels
            .iter()
            .flatten()
            .map(|&class| {
                let a = usize::try_from(self.advances[class]).expect("an advance fits");
                ExactRatMatrix::new(
                    (0..n)
                        .map(|row| unit((row + n - a) % n))
                        .collect(),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let coupling = (0..self.helix.cells())
            .map(|cell| {
                (0..n)
                    .map(|lift| {
                        if self.helix.cell(lift as u64) == cell {
                            Rat::one()
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect()
            })
            .collect();
        let openings = keys
            .iter()
            .map(|&key| unit(usize::try_from(key % self.helix.period()).expect("a key fits")))
            .collect();
        Ok((n, transports, coupling, openings))
    }
}

/// The driven reading's patches: positions where `λ(c(ℓ(k)))` differs from `x_k`, the lift stepped
/// by each actual class; each patch with its class and the reading it replaces.
fn driven_patches(
    helix: &CarryHelix,
    advances: &[u64],
    labels: &[Option<usize>],
    passage: &[usize],
    key: u64,
) -> Vec<(usize, usize, Option<usize>)> {
    let mut lift = key % helix.period();
    let mut patches = Vec::new();
    for (k, &class) in passage.iter().enumerate() {
        let predicted = labels[helix.cell(lift) as usize];
        if predicted != Some(class) {
            patches.push((k, class, predicted));
        }
        lift = (lift + advances[class]) % helix.period();
    }
    patches
}

// -------------------------------------------------------------------------------------------
// location by loop closure

/// One survivor: a partial transport, a partial label map (cell to class) and the lifts it admits
/// at the current emission.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Survivor {
    advances: Vec<Option<u64>>,
    labels: Vec<Option<usize>>,
    lifts: Vec<u64>,
}

impl Survivor {
    fn cell_of(&self, class: usize) -> Option<u64> {
        self.labels
            .iter()
            .position(|&label| label == Some(class))
            .map(|cell| cell as u64)
    }

    fn complete(&self, classes: usize) -> bool {
        self.advances.iter().all(Option::is_some) && self.labels.iter().flatten().count() == classes
    }
}

/// [definition] **The survivors at one observation**: survivors (each a transport-and-label class
/// with its admitted lifts), their lifts summed, and whether every survivor has read every class's
/// advance and label.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SurvivorCount {
    pub survivors: u64,
    pub lifts: u64,
    pub complete: bool,
}

/// [definition] **The fibre's outcome** at the read set's end: no survivor, one gauge class with
/// every class's advance and label read, or more (a plural fibre, or one class with an advance or
/// label never read, whose fibre is plural in that coordinate).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TransportFibre {
    Empty,
    One(LocatedTransport),
    Plural { classes: usize },
}

/// [definition] **Location by loop closure** (module header): the survivors at the read set's
/// end, the curve of their counts at every observation, and the classes' first-occurrence order.
///
/// [definition; agent-inferred] The survivors are explored depth first along the read set's
/// emissions: each survivor at observation `k` has its successors at `k + 1` (one when its
/// previous class's advance and the class's label are read; a branch over the advance's `ℤ/D` or
/// the label's free cells otherwise). The count at each observation is the number of survivors
/// there, the same count a breadth-first sweep holds, but only one path of the exploration is held
/// at a time.
#[derive(Clone, Debug)]
pub struct TransportLocation {
    helix: CarryHelix,
    classes: usize,
    survivors: Vec<Survivor>,
    order: Vec<usize>,
    curve: Vec<SurvivorCount>,
}

impl TransportLocation {
    /// **Locate** over a read set of passages on the helix, `classes` classes; refused unless the
    /// classes fit the receiving cells injectively and every emission is a declared class.
    pub fn locate(
        helix: CarryHelix,
        classes: usize,
        passages: &[Vec<usize>],
    ) -> Result<Self, CompressionError> {
        if classes == 0 || classes as u64 > helix.cells() {
            return Err(helix_refusal(
                "the classes are injective labels of the receiving cells",
            ));
        }
        if let Some(&class) = passages.iter().flatten().find(|&&class| class >= classes) {
            return Err(CompressionError::IndexOutside {
                index: class,
                population: classes,
            });
        }
        let emissions: Vec<(usize, bool)> = passages
            .iter()
            .flat_map(|passage| {
                passage
                    .iter()
                    .enumerate()
                    .map(|(k, &class)| (class, k == 0))
            })
            .collect();
        let mut order = Vec::new();
        for &(class, _) in &emissions {
            if !order.contains(&class) {
                order.push(class);
            }
        }
        let mut location = Self {
            helix,
            classes,
            survivors: Vec::new(),
            order,
            curve: vec![
                SurvivorCount {
                    survivors: 0,
                    lifts: 0,
                    complete: true,
                };
                emissions.len()
            ],
        };
        let Some(&(first, _)) = emissions.first() else {
            return Ok(location);
        };
        // The rotation gauge: the read set's first emission reads the receiving digit 0.
        let cells = location.helix.cells() as usize;
        let mut labels = vec![None; cells];
        labels[0] = Some(first);
        let mut stack = vec![(
            0usize,
            Survivor {
                advances: vec![None; classes],
                labels,
                lifts: location.helix.cell_lifts(0).collect(),
            },
        )];
        while let Some((k, survivor)) = stack.pop() {
            let count = &mut location.curve[k];
            count.survivors += 1;
            count.lifts += survivor.lifts.len() as u64;
            count.complete &= survivor.complete(classes);
            if k + 1 == emissions.len() {
                location.survivors.push(survivor);
                continue;
            }
            let (class, starts) = emissions[k + 1];
            let previous = (!starts).then_some(emissions[k].0);
            location.successors(&survivor, previous, class, |child| stack.push((k + 1, child)));
        }
        location.survivors.sort_by(|a, b| (&a.advances, &a.labels).cmp(&(&b.advances, &b.labels)));
        Ok(location)
    }

    /// **A survivor's successors at the next emission** (module header): its lifts stepped by the
    /// previous class's advance (each advance of `ℤ/D` when unread; every lift at a passage's start),
    /// kept in the cell the class is labelled with, or else in each unlabelled cell with the label
    /// read there.
    fn successors(
        &self,
        parent: &Survivor,
        previous: Option<usize>,
        class: usize,
        mut emit: impl FnMut(Survivor),
    ) {
        let helix = &self.helix;
        let period = helix.period();
        let mut place = |advances: &Vec<Option<u64>>, moved: &[u64]| {
            let mut keep = |cell: u64, labels: Vec<Option<usize>>| {
                let lifts: Vec<u64> = moved
                    .iter()
                    .copied()
                    .filter(|&lift| helix.cell(lift) == cell)
                    .collect();
                if !lifts.is_empty() {
                    emit(Survivor {
                        advances: advances.clone(),
                        labels,
                        lifts,
                    });
                }
            };
            match parent.cell_of(class) {
                Some(cell) => keep(cell, parent.labels.clone()),
                None => {
                    for cell in 0..helix.cells() {
                        if parent.labels[cell as usize].is_none() {
                            let mut labels = parent.labels.clone();
                            labels[cell as usize] = Some(class);
                            keep(cell, labels);
                        }
                    }
                }
            }
        };
        match previous {
            None => {
                let every: Vec<u64> = (0..period).collect();
                place(&parent.advances, &every);
            }
            Some(previous) => {
                let candidates: Vec<u64> = match parent.advances[previous] {
                    Some(a) => vec![a],
                    None => (0..period).collect(),
                };
                for a in candidates {
                    let mut moved: Vec<u64> =
                        parent.lifts.iter().map(|&lift| (lift + a) % period).collect();
                    moved.sort_unstable();
                    let mut advances = parent.advances.clone();
                    advances[previous] = Some(a);
                    place(&advances, &moved);
                }
            }
        }
    }

    /// The observations read.
    pub fn observations(&self) -> u64 {
        self.curve.len() as u64
    }

    /// The survivors at each observation.
    pub fn curve(&self) -> &[SurvivorCount] {
        &self.curve
    }

    /// The classes in their first-occurrence order (the gauge convention's order, label-free).
    pub fn order(&self) -> &[usize] {
        &self.order
    }

    /// **`n*_machine`**: the least observation count from which the survivors are the read set's
    /// final fibre (every survivor complete, and none removed after it); `None` on an empty fibre
    /// or one never complete.
    pub fn located_from(&self) -> Option<u64> {
        let last = self.curve.last()?;
        if !last.complete || last.survivors == 0 {
            return None;
        }
        let unsettled = self
            .curve
            .iter()
            .rposition(|count| !count.complete || count.survivors != last.survivors);
        Some(unsettled.map_or(1, |k| k as u64 + 2))
    }

    /// A survivor's ordering key in the classes' first-occurrence order: each advance (`D` unread),
    /// then each cell's label as its class's first-occurrence rank (`|A|` unread).
    fn ordering(&self, advances: &[Option<u64>], labels: &[Option<usize>]) -> (Vec<u64>, Vec<usize>) {
        let rank = |class: usize| self.order.iter().position(|&c| c == class).unwrap_or(self.classes);
        (
            self.order
                .iter()
                .map(|&class| advances[class].unwrap_or(self.helix.period()))
                .chain(
                    (0..self.classes)
                        .filter(|class| !self.order.contains(class))
                        .map(|class| advances[class].unwrap_or(self.helix.period())),
                )
                .collect(),
            labels
                .iter()
                .map(|label| label.map_or(self.classes, rank))
                .collect(),
        )
    }

    /// A survivor's gauge class representative: itself or its reflection, whichever orders first.
    fn representative(&self, survivor: &Survivor) -> (Vec<Option<u64>>, Vec<Option<usize>>) {
        let period = self.helix.period();
        let cells = survivor.labels.len();
        let reflected_advances: Vec<Option<u64>> = survivor
            .advances
            .iter()
            .map(|a| a.map(|a| (period - a) % period))
            .collect();
        let reflected_labels: Vec<Option<usize>> =
            (0..cells).map(|c| survivor.labels[(cells - c) % cells]).collect();
        if self.ordering(&reflected_advances, &reflected_labels)
            < self.ordering(&survivor.advances, &survivor.labels)
        {
            (reflected_advances, reflected_labels)
        } else {
            (survivor.advances.clone(), survivor.labels.clone())
        }
    }

    /// The survivors' distinct gauge classes, each its representative.
    #[allow(clippy::type_complexity)]
    pub fn gauge_classes(&self) -> Vec<(Vec<Option<u64>>, Vec<Option<usize>>)> {
        let mut classes: Vec<_> = self
            .survivors
            .iter()
            .map(|survivor| self.representative(survivor))
            .collect();
        classes.sort();
        classes.dedup();
        classes
    }

    /// **The fibre's members**: each complete gauge class's representative as a located transport.
    pub fn members(&self) -> Vec<LocatedTransport> {
        self.gauge_classes()
            .into_iter()
            .filter(|(advances, labels)| {
                advances.iter().all(Option::is_some)
                    && labels.iter().flatten().count() == self.classes
            })
            .filter_map(|(advances, labels)| {
                LocatedTransport::new(
                    self.helix.clone(),
                    advances.into_iter().map(|a| a.expect("every advance read")).collect(),
                    labels,
                )
                .ok()
            })
            .collect()
    }

    /// The survivors themselves (each transport and labels, unreduced by the reflection).
    #[allow(clippy::type_complexity)]
    pub fn survivors(&self) -> Vec<(Vec<Option<u64>>, Vec<Option<usize>>)> {
        self.survivors
            .iter()
            .map(|s| (s.advances.clone(), s.labels.clone()))
            .collect()
    }

    /// **The fibre at the read set's end** (module header).
    pub fn fibre(&self) -> TransportFibre {
        if self.survivors.is_empty() {
            return TransportFibre::Empty;
        }
        let classes = self.gauge_classes();
        let mut members = self.members();
        if classes.len() == 1 && members.len() == 1 {
            TransportFibre::One(members.remove(0))
        } else {
            TransportFibre::Plural {
                classes: classes.len(),
            }
        }
    }
}

/// **The located transport's ordering in a location's first-occurrence order**, for comparing two
/// located transports up to the reflection gauge: the representative a location would choose.
pub fn gauge_representative(
    location: &TransportLocation,
    transport: &LocatedTransport,
) -> LocatedTransport {
    let survivor = Survivor {
        advances: transport.advances.iter().map(|&a| Some(a)).collect(),
        labels: transport.labels.clone(),
        lifts: Vec::new(),
    };
    let (advances, labels) = location.representative(&survivor);
    LocatedTransport {
        helix: transport.helix.clone(),
        advances: advances.into_iter().map(|a| a.expect("every advance read")).collect(),
        labels,
    }
}

/// [definition] **The terrain's unicity count** `n_U` (the record's §0.4): the least `n` with
/// `|A|^(n−1) ≥ ⌈D^|A| · d!/(d − |A|)! / (2d)⌉`, `d` the receiving cells: the transport-and-label
/// classes under the dihedral gauge (orbits of at most `2d`) need distinct emission words after the
/// gauge-fixed first emission.
pub fn unicity_count(helix: &CarryHelix, classes: usize) -> u64 {
    let d = helix.cells();
    let mut keys = BigUint::from(helix.period()).pow(classes as u32);
    for taken in 0..classes as u64 {
        keys *= d - taken;
    }
    let orbit = BigUint::from(2 * d);
    let gauge_classes = (&keys + &orbit - BigUint::one()) / orbit;
    let base = BigUint::from(classes as u64);
    let mut words = BigUint::one();
    let mut n = 1;
    while words < gauge_classes {
        words *= &base;
        n += 1;
    }
    n
}

// -------------------------------------------------------------------------------------------
// the navigator's code

/// The permutation index (Lehmer rank) of labels that are a bijection of the classes.
fn label_rank(labels: &[Option<usize>]) -> Option<usize> {
    let m = labels.len();
    let mut left: Vec<usize> = (0..m).collect();
    let mut rank = 0usize;
    for (c, label) in labels.iter().enumerate() {
        let class = (*label)?;
        let digit = left.iter().position(|&l| l == class)?;
        left.remove(digit);
        rank = rank * (m - c) + digit;
    }
    Some(rank)
}

/// The labels of a permutation index.
fn label_unrank(mut rank: usize, m: usize) -> Vec<Option<usize>> {
    let mut digits = vec![0usize; m];
    for c in (0..m).rev() {
        digits[c] = rank % (m - c);
        rank /= m - c;
    }
    let mut left: Vec<usize> = (0..m).collect();
    digits.into_iter().map(|digit| Some(left.remove(digit))).collect()
}

fn factorial(m: usize) -> usize {
    (1..=m).product()
}

/// [definition] **The navigator's code's widths** (module header) over the declared shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CodeWidths {
    pub description: u64,
    pub labels: u64,
    pub key: u64,
    pub count: u64,
    pub position: u64,
    pub class: u64,
}

impl CodeWidths {
    /// The widths for a helix, `|A|` classes and `n` cells in all.
    pub fn of(helix: &CarryHelix, classes: usize, cells: usize) -> Self {
        Self {
            description: helix.cells() * bits(helix.period()),
            labels: bits(factorial(classes) as u64),
            key: bits(helix.period()),
            count: bits(cells as u64 + 1),
            position: bits(cells as u64),
            class: bits(classes.saturating_sub(1) as u64),
        }
    }
}

fn shape_refusal(passages: &[Vec<usize>], classes: usize, cells: u64) -> Result<(), CompressionError> {
    if classes as u64 != cells || classes > LABEL_CEILING || classes < 2 {
        return Err(helix_refusal(
            "the navigator's code ranks a bijection of at least two classes within the label ceiling",
        ));
    }
    if passages.iter().flatten().any(|&class| class >= classes) {
        return Err(CompressionError::SymbolOutside);
    }
    Ok(())
}

/// **The residual** (module header): the labels, each passage's key, the patch count and the
/// patches, for any fixed transport `advances` (one per class).
pub fn residual_code(
    helix: &CarryHelix,
    advances: &[u64],
    labels: &[Option<usize>],
    keys: &[u64],
    passages: &[Vec<usize>],
) -> Result<Vec<bool>, CompressionError> {
    let classes = advances.len();
    shape_refusal(passages, classes, helix.cells())?;
    if keys.len() != passages.len() {
        return Err(CompressionError::Extent {
            what: "a key per passage",
            expected: passages.len(),
            found: keys.len(),
        });
    }
    let rank = label_rank(labels).ok_or(helix_refusal("the code's labels are a bijection"))?;
    let total: usize = passages.iter().map(Vec::len).sum();
    let widths = CodeWidths::of(helix, classes, total);
    let mut code = Vec::new();
    write_index(&mut code, rank, widths.labels);
    for &key in keys {
        write_index(&mut code, (key % helix.period()) as usize, widths.key);
    }
    let mut patches = Vec::new();
    let mut offset = 0;
    for (passage, &key) in passages.iter().zip(keys) {
        for (k, class, predicted) in driven_patches(helix, advances, labels, passage, key) {
            let predicted = predicted.expect("a bijection labels every cell");
            let index = if class < predicted { class } else { class - 1 };
            patches.push((offset + k, index));
        }
        offset += passage.len();
    }
    write_index(&mut code, patches.len(), widths.count);
    for (position, index) in patches {
        write_index(&mut code, position, widths.position);
        write_index(&mut code, index, widths.class);
    }
    Ok(code)
}

/// **Read the residual back**: the passages of the declared lengths regenerated by stepping the
/// lift by each decoded class. Refused on a truncated or trailing code.
pub fn read_residual(
    helix: &CarryHelix,
    advances: &[u64],
    code: &mut impl Iterator<Item = bool>,
    lengths: &[usize],
) -> Result<Vec<Vec<usize>>, CompressionError> {
    let classes = advances.len();
    let total: usize = lengths.iter().sum();
    let widths = CodeWidths::of(helix, classes, total);
    let labels = label_unrank(read_index(code, widths.labels, factorial(classes))?, classes);
    let period = usize::try_from(helix.period()).expect("a period fits");
    let keys = lengths
        .iter()
        .map(|_| read_index(code, widths.key, period).map(|key| key as u64))
        .collect::<Result<Vec<_>, _>>()?;
    let count = read_index(code, widths.count, total + 1)?;
    let mut patches = Vec::with_capacity(count);
    for _ in 0..count {
        let position = read_index(code, widths.position, total.max(1))?;
        let index = read_index(code, widths.class, classes - 1)?;
        patches.push((position, index));
    }
    let mut patches = patches.into_iter().peekable();
    let mut offset = 0;
    let passages = lengths
        .iter()
        .zip(&keys)
        .map(|(&length, &key)| {
            let mut lift = key;
            let passage = (0..length)
                .map(|k| {
                    let predicted =
                        labels[helix.cell(lift) as usize].expect("a bijection labels every cell");
                    let class = match patches.peek() {
                        Some(&(position, index)) if position == offset + k => {
                            patches.next();
                            if index < predicted { index } else { index + 1 }
                        }
                        _ => predicted,
                    };
                    lift = (lift + advances[class]) % helix.period();
                    class
                })
                .collect();
            offset += length;
            passage
        })
        .collect();
    if code.next().is_some() {
        return Err(CompressionError::TrailingCode);
    }
    Ok(passages)
}

/// **The located navigator's code** (module header): the transport per receiving cell, then the
/// residual; keys are each passage's least key with the fewest patches.
pub fn located_code(
    located: &LocatedTransport,
    passages: &[Vec<usize>],
) -> Result<Vec<bool>, CompressionError> {
    let helix = &located.helix;
    shape_refusal(passages, located.classes(), helix.cells())?;
    let widths = CodeWidths::of(helix, located.classes(), 1);
    let mut code = Vec::new();
    for label in &located.labels {
        let class = label.ok_or(helix_refusal("the code's labels are a bijection"))?;
        write_index(&mut code, located.advances[class] as usize, widths.key);
    }
    let keys: Vec<u64> = passages
        .iter()
        .map(|passage| {
            (0..helix.period())
                .min_by_key(|&key| located.patches(passage, key))
                .expect("a helix has a lift")
        })
        .collect();
    code.extend(residual_code(helix, &located.advances, &located.labels, &keys, passages)?);
    Ok(code)
}

/// **Read the located navigator's code back** over the declared classes and passage lengths.
pub fn read_located(
    helix: &CarryHelix,
    classes: usize,
    code: &[bool],
    lengths: &[usize],
) -> Result<Vec<Vec<usize>>, CompressionError> {
    let widths = CodeWidths::of(helix, classes, 1);
    let mut bits = code.iter().copied();
    let period = usize::try_from(helix.period()).expect("a period fits");
    let per_cell = (0..helix.cells())
        .map(|_| read_index(&mut bits, widths.key, period).map(|a| a as u64))
        .collect::<Result<Vec<_>, _>>()?;
    // The residual's labels come next; the transport per class is read through them.
    let label_bits = CodeWidths::of(helix, classes, 1).labels;
    let rest: Vec<bool> = bits.collect();
    let labels = label_unrank(
        read_index(&mut rest.iter().copied(), label_bits, factorial(classes))?,
        classes,
    );
    let mut advances = vec![0; classes];
    for (cell, label) in labels.iter().enumerate() {
        advances[label.expect("a bijection")] = per_cell[cell];
    }
    read_residual(helix, &advances, &mut rest.into_iter(), lengths)
}

// -------------------------------------------------------------------------------------------
// repair through the located navigator

/// [definition] **A lift restriction** (module header): each cell's lift family at the fixed
/// point, the joint fibre (the keys whose orbit meets every intact cell), and each cell's class
/// family with its certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiftRestriction {
    families: Vec<Vec<u64>>,
    keys: Vec<u64>,
    classes: Vec<Vec<usize>>,
    certified: Vec<bool>,
    damaged: Vec<Option<usize>>,
    sweeps: usize,
}

impl LocatedTransport {
    /// **Restrict a damaged passage's lift families from both sides** (module header). Refused
    /// when a family empties (the navigator does not fit the passage) or a class lies outside the
    /// declared classes.
    pub fn restrict(&self, damaged: &[Option<usize>]) -> Result<LiftRestriction, CompressionError> {
        let period = self.helix.period();
        if let Some(&class) = damaged.iter().flatten().find(|&&c| c >= self.classes()) {
            return Err(CompressionError::IndexOutside {
                index: class,
                population: self.classes(),
            });
        }
        let admits = |t: usize, lift: u64| match damaged[t] {
            Some(class) => self.emit(lift) == Some(class),
            None => self.emit(lift).is_some(),
        };
        let mut families: Vec<Vec<u64>> = (0..damaged.len())
            .map(|t| (0..period).filter(|&l| admits(t, l)).collect())
            .collect();
        let mut sweeps = 0;
        loop {
            sweeps += 1;
            let mut changed = false;
            for t in 0..damaged.len().saturating_sub(1) {
                let image: Vec<u64> = families[t].iter().filter_map(|&l| self.step(l)).collect();
                let before = families[t + 1].len();
                families[t + 1].retain(|l| image.contains(l));
                changed |= families[t + 1].len() != before;
            }
            for t in (0..damaged.len().saturating_sub(1)).rev() {
                let (here, after) = families.split_at_mut(t + 1);
                let before = here[t].len();
                here[t].retain(|&l| self.step(l).is_some_and(|next| after[0].contains(&next)));
                changed |= here[t].len() != before;
            }
            if let Some(cell) = families.iter().position(Vec::is_empty) {
                return Err(CompressionError::Contradicted { cell });
            }
            if !changed {
                break;
            }
        }
        // The joint fibre: the keys whose orbit meets every intact cell.
        let orbit = |key: u64| -> Option<Vec<u64>> {
            let mut lift = key;
            let mut lifts = Vec::with_capacity(damaged.len());
            for t in 0..damaged.len() {
                if !admits(t, lift) {
                    return None;
                }
                lifts.push(lift);
                if t + 1 < damaged.len() {
                    lift = self.step(lift)?;
                }
            }
            Some(lifts)
        };
        let orbits: Vec<(u64, Vec<u64>)> = (0..period)
            .filter_map(|key| orbit(key).map(|lifts| (key, lifts)))
            .collect();
        let keys = orbits.iter().map(|(key, _)| *key).collect();
        let certified = (0..damaged.len())
            .map(|t| {
                let mut support: Vec<u64> = orbits.iter().map(|(_, lifts)| lifts[t]).collect();
                support.sort_unstable();
                support.dedup();
                support == families[t]
            })
            .collect();
        let classes = families
            .iter()
            .map(|family| {
                let mut classes: Vec<usize> = family.iter().filter_map(|&l| self.emit(l)).collect();
                classes.sort_unstable();
                classes.dedup();
                classes
            })
            .collect();
        Ok(LiftRestriction {
            families,
            keys,
            classes,
            certified,
            damaged: damaged.to_vec(),
            sweeps,
        })
    }
}

impl LiftRestriction {
    /// Each cell's lift family at the fixed point.
    pub fn families(&self) -> &[Vec<u64>] {
        &self.families
    }

    /// The joint fibre: the keys whose orbit meets every intact cell.
    pub fn keys(&self) -> &[u64] {
        &self.keys
    }

    /// Each cell's class family.
    pub fn classes(&self) -> &[Vec<usize>] {
        &self.classes
    }

    /// Whether each cell's family is the joint fibre's projection.
    pub fn certified(&self) -> &[bool] {
        &self.certified
    }

    /// The sweeps run to the fixed point.
    pub fn sweeps(&self) -> usize {
        self.sweeps
    }

    /// **The release** (module header): each erased cell decided at tolerance zero.
    pub fn release(&self) -> Result<Vec<CellRelease>, CompressionError> {
        (0..self.families.len())
            .map(|t| match self.damaged[t] {
                Some(class) => Ok(CellRelease::Intact(class)),
                None => decide(t, &self.classes[t], self.certified[t]),
            })
            .collect()
    }
}

/// [definition; agent-inferred] **A restriction through a fibre** (module header): every member
/// of a plural fibre restricts the passage; a member whose restriction empties a family is refused
/// by the passage and leaves; each cell's class family is the union of the members' families (the
/// joint fibre over the members and their keys), certified when every member's is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FibreRestriction {
    kept: usize,
    refused: usize,
    classes: Vec<Vec<usize>>,
    certified: Vec<bool>,
    damaged: Vec<Option<usize>>,
}

/// **Restrict a damaged passage through every member of a fibre** (the type's header). Refused when
/// the fibre is empty or every member is refused by the passage.
pub fn restrict_fibre(
    members: &[LocatedTransport],
    damaged: &[Option<usize>],
) -> Result<FibreRestriction, CompressionError> {
    let mut classes: Vec<Vec<usize>> = vec![Vec::new(); damaged.len()];
    let mut certified = vec![true; damaged.len()];
    let (mut kept, mut refused, mut refusal) = (0, 0, None);
    for member in members {
        match member.restrict(damaged) {
            Ok(restriction) => {
                kept += 1;
                for t in 0..damaged.len() {
                    classes[t].extend(&restriction.classes[t]);
                    certified[t] &= restriction.certified[t];
                }
            }
            Err(error @ CompressionError::Contradicted { .. }) => {
                refused += 1;
                refusal.get_or_insert(error);
            }
            Err(other) => return Err(other),
        }
    }
    if kept == 0 {
        return Err(refusal.unwrap_or(CompressionError::EmptyFamily { what: "fibre" }));
    }
    for family in &mut classes {
        family.sort_unstable();
        family.dedup();
    }
    Ok(FibreRestriction {
        kept,
        refused,
        classes,
        certified,
        damaged: damaged.to_vec(),
    })
}

impl FibreRestriction {
    /// The members kept and the members the passage refused.
    pub fn members(&self) -> (usize, usize) {
        (self.kept, self.refused)
    }

    /// Each cell's class family over the fibre.
    pub fn classes(&self) -> &[Vec<usize>] {
        &self.classes
    }

    /// Whether every kept member's family is its joint fibre's projection at each cell.
    pub fn certified(&self) -> &[bool] {
        &self.certified
    }

    /// **The release** (module header): each erased cell decided at tolerance zero on its class
    /// family over the fibre.
    pub fn release(&self) -> Result<Vec<CellRelease>, CompressionError> {
        (0..self.classes.len())
            .map(|t| match self.damaged[t] {
                Some(class) => Ok(CellRelease::Intact(class)),
                None => decide(t, &self.classes[t], self.certified[t]),
            })
            .collect()
    }
}

fn first_held(releases: &[CellRelease]) -> Option<(usize, Vec<usize>)> {
    releases.iter().enumerate().find_map(|(t, release)| match release {
        CellRelease::Held(family) => Some((t, family.clone())),
        _ => None,
    })
}

/// **The repair's residual** (module header): while a cell is held, the truth's index in the first
/// held family over the fibre in `⌈log₂ |F_t|⌉` bits, that cell pinned and the restriction re-run.
pub fn lift_residual(
    members: &[LocatedTransport],
    damaged: &[Option<usize>],
    truth: &[usize],
) -> Result<Vec<bool>, CompressionError> {
    let mut cells = damaged.to_vec();
    let mut code = Vec::new();
    while let Some((t, family)) = first_held(&restrict_fibre(members, &cells)?.release()?) {
        let index = family
            .iter()
            .position(|&class| class == truth[t])
            .ok_or(CompressionError::Contradicted { cell: t })?;
        write_index(&mut code, index, bits(family.len() as u64));
        cells[t] = Some(truth[t]);
    }
    Ok(code)
}

/// **Reopen a damaged passage** from its residual, by the same restriction through the fibre.
pub fn lift_reopen(
    members: &[LocatedTransport],
    damaged: &[Option<usize>],
    code: &[bool],
) -> Result<Vec<usize>, CompressionError> {
    let mut cells = damaged.to_vec();
    let mut bits_read = code.iter().copied();
    loop {
        let releases = restrict_fibre(members, &cells)?.release()?;
        match first_held(&releases) {
            Some((t, family)) => {
                let index = read_index(&mut bits_read, bits(family.len() as u64), family.len())?;
                cells[t] = Some(family[index]);
            }
            None => {
                if bits_read.next().is_some() {
                    return Err(CompressionError::TrailingCode);
                }
                return Ok(releases
                    .iter()
                    .map(|release| release.class().expect("no cell is held"))
                    .collect());
            }
        }
    }
}

#[cfg(test)]
mod tests;

//! **The field: closing rotor rings joined by pair contacts, and the lift point that carries them.**
//!
//! [definition] The HNN's complex `K` (design (a), "The one object"): rings are 0-cells, contacts
//! `a = (g→h)` are 1-cells, declared loops are 2-cells. Each part is declared here and checked once:
//!
//! - a [`Ring`] is a **closing rotor**: its navigator ([`Navigator::rotor`]) whose transport is the
//!   finite-order port map `P_g = (· + 1)` of its `d_g` nodes (`navigator::Transport::Map`, order
//!   exactly `d_g`), its key the declared initial configuration; its reflector `F_g`, an involution
//!   of `ℤ/d_g` (the keys' [`ReflectorMachine`] is built from the two, [`Ring::machine`]); its lock
//!   `N_g ⊂ ℤ/d_g` on the port chart `port_g(x) = code(x) mod d_g`;
//!   one screw generator with `d_g` node placements on its circle, node `k` at winding `n` sitting
//!   at `x_g(k, n) = placement_k + n·v_∥` (helix = circle + carry, `v_∥` the generator's axial
//!   advance). The period is combinatorial, so several nodes may share a placement; its storage
//!   admittance `Y_g`; its [`Parametron`] with unit weights; its declared
//!   initial configuration. There is no non-closing ring: a rotation transport has no form here;
//! - a [`Contact`] carries its channel (a node matching, so `U_a = ι_h ι_gᵀ` is a partial isometry
//!   with reverse `U_aᵀ`), its reference admittance `Y_a` and **one participation exponent `β_a`**,
//!   read at both ends. Its pair geometry is the two rings' screws at their phases
//!   ([`Contact::pair`]); it has no scalar conductance;
//! - the [`Field`] is the declared complex with its source rings `𝒮`, offsets `Δ`, the exterior
//!   chart's size `|A|` (read only by the capacity), the hop `h`, the exponent grain `L`, the
//!   admitted receivers with their landmark trees' address depths (Decision 28), the crib, and the
//!   carrier lattice `2^(−L_ℓ)ℤ` of
//!   every learned locus
//!   ([`FieldDeclaration::lattice_by_rule`]). [`Field::declare`] computes the capacity `n*` by
//!   counting and refuses a declared population shorter than it (guard 1), and declares the word's
//!   precisions by rule ([`Field::word_lattice`], [`crate::hnn::WordLattice::by_rule`], Decision 24):
//!   the certificate's target `2^(−D_c)`, the charts' lattice `L_c = 2D_c` and the transients'
//!   lattice `L_w`, from the finest receiver grain, the receiving fan-in, the widest local solve
//!   and the junction steps; [`Field::describe`] codes them. Its contacts are the
//!   blocks of its connection incidence `d_A` ([`Field::connection`]), and the rings and contacts
//!   joined through it are the read-only Holarchy chart [`Field::holon`], built from the one
//!   constitution;
//! - the [`Current`] is the lift point `λ ∈ ℤ^G` of the rings' joint clock torus: the only thing
//!   that persists between words besides the constitution and the open moments. It has no wave
//!   field (guard 16).
//!
//! [definition] **Selective stepping** ([`Field::selective_step`], design (a), "Stepping is
//! selective"): on each source cell `x`, ring `g` advances `c_g(x) = [port_g(x) ∈ N_g]` ticks, plus
//! one carry when its predecessor in the carry chain `0 → 1 → … → G−1` wraps. The last ring's
//! carry is the joint clock's carry-out, the aeon boundary. A ring whose lock no input fits and
//! that receives no carry keeps its configuration (Lean `HNN/Keys.selective_step_dormant`).
//!
//! [definition; agent-inferred] **The constitution's read face.** `Θ` is owned once by the
//! constitution (`hnn::constitution`, the learning side). The forward pass reads it only through
//! [`ConstitutionRead`], every learned operand carried as its factors so that the storage,
//! stiffness and dissipation forms and the element's passive part are PSD (resp. NSD) by
//! construction. Declared, unlearned values of campaign 1 (`Y_g`, `Y_a`, `β_a`, `h`, `L`) live on
//! the declaration. The source injection `I_g` is the identity in campaign 1, since `E_g` already
//! maps into ring `g`'s realified storage.
//!
//! | Lean | Rust |
//! |---|---|
//! | `HNN/Keys.selective_step_dormant`, `HNN/Moment.selective_position` | [`Field::selective_step`] |
//! | `Aeon/Clock/Winding.clockLift` | [`Field::parametric`] |
//! | `Holon/Complex` (`∂∘∂ = 0`) | [`Field::complex`] |
//! | `Holon/Generator.{mapRotor_order, map_pow_mod_order}` | [`Ring::navigator`], [`Ring::rotate`] |
//! | `Holon/Complex.{blockIncidence, block_cell_curvature, block_flat_closed}` | [`Field::connection`], consumed by [`Field::contrast`] |
//! | `Holarchy/Join.interconnect`, `Holon/Dirac.kirchhoff_isDirac`, `Holarchy/Join.Holarchy.parametric` | [`Field::holon`] (certified at the mount) |
//! | `HNN/Propagation.partialIsometry_transit` | [`Field::connection`]'s blocks `U_aᵀ`, read by [`Field::contrast`] and by the transit's channel selections ([`Contact::selection`]) |
//! | `Transport/HelicalPairInteraction.pairFeatureAt_gradient` | [`Contact::pair`] through [`PairContact`] |
//! | `HNN/Moment.moment_capacity` | [`Field::declare`] through [`crate::hnn::moment::capacity`] |

use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::aeon::ClockLift;
use crate::compression::ReflectorMachine;
use crate::geometry::RatVec3;
use crate::geometry::complex::{CellComplex, ConnectionIncidence};
use crate::geometry::screw::{ScrewAxis, ScrewGenerator, ScrewPair, SituatedScrew};
use crate::hnn::HnnError;
use crate::hnn::chart::WordLattice;
use crate::hnn::constitution::{Lattice, Locus, Steps};
use crate::hnn::landmark::Landmarks;
use crate::hnn::moment::{Capacity, PairPort, capacity};
use crate::holarchy::{Gluing, Holarchy};
use crate::holon::contact::PairContact;
use crate::holon::contact::menu::PortPermutation;
use crate::holon::dirac::DiracStructure;
use crate::holon::element::{ActiveRelation, ResistiveRelation};
use crate::holon::parametron::Parametron;
use crate::holon::{Holon, HolonError, PortCounts, PortHolon};
use crate::navigator::{Clock, Navigator};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::inertia::SymmetricForm;
use crate::ratio::linear::vector::lcm;
use crate::ratio::{Rat, integer, rat};

// -------------------------------------------------------------------------------------------
// the constitution's read face

/// [definition; agent-inferred] **What the forward pass reads of the constitution `Θ`.** The owner
/// (`hnn::constitution`) implements it; the word copies what it reads into its own operands at the
/// cut, so no word holds the constitution. Every matrix is exact; every square is a factor.
///
/// Ring `g`'s realified width is `2d_g`, contact `a`'s channel width is `k_a`, and `|A|` is the
/// field's exterior chart. It is `Sync`: the rings' and contacts' regions read it together, and
/// none writes it (`hnn::realization`).
pub trait ConstitutionRead: Sync {
    /// The standing `q_g ∈ ℚ^(2d_g)`, read only through the sheet classes of its contrast.
    fn standing(&self, ring: usize) -> &[Rat];
    /// The factor `f_g` (`2d_g × m`) of the element's passive part `W_s,g = −f_g f_gᵀ`.
    fn passive_factor(&self, ring: usize) -> &ExactRatMatrix;
    /// The contrast port `W_c,g` (`2d_g × 2d_g`), an active element relation.
    fn contrast_port(&self, ring: usize) -> &ExactRatMatrix;
    /// The skew slices `(u_ρ, v_ρ)`, `ρ < 2d_g`, with `A_ρ = u_ρ v_ρᵀ − v_ρ u_ρᵀ`.
    fn slices(&self, ring: usize) -> &[(Vec<Rat>, Vec<Rat>)];
    /// The source port `E_g` (`2d_g × |A|`) on a source ring; `None` elsewhere.
    fn source_port(&self, ring: usize) -> Option<&ExactRatMatrix>;
    /// The factored pair port `E_g^(δ)` at a declared offset on a source ring; `None` elsewhere.
    fn pair_port(&self, ring: usize, offset: usize) -> Option<&PairPort>;
    /// The factor `c_a` (`k_a × m`) of the contact's storage `C_a = c_a c_aᵀ`.
    fn contact_storage(&self, contact: usize) -> &ExactRatMatrix;
    /// The factor `b_a` (`k_a × m`) of the contact's stiffness `K_a = b_a b_aᵀ` (`K_a ⪰ 0` in
    /// campaign 1).
    fn contact_stiffness(&self, contact: usize) -> &ExactRatMatrix;
    /// The factor `F_a` (`k_a × m`) of the contact's dissipation `D_a = F_a F_aᵀ`.
    fn contact_dissipation(&self, contact: usize) -> &ExactRatMatrix;
    /// The receiving map `R` (`2|A| × 2d_R`) of a receiving ring; `None` elsewhere.
    fn receiving_map(&self, ring: usize) -> Option<&ExactRatMatrix>;
    /// **The receiving parametron's landmark tree** (Decision 28, `hnn::landmark`) of a receiving
    /// ring, whose face at each phase's causal address the receiving read adds to the wave at the
    /// grain (`hnn::receiving`); `None` elsewhere.
    fn landmarks(&self, ring: usize) -> Option<&Landmarks>;
}

// -------------------------------------------------------------------------------------------
// the declaration

/// [definition] **A ring as declared.** Every field is public data; [`Field::declare`] checks it.
/// There is no exponent on a ring: participation is one exponent per contact.
///
/// ```compile_fail,E0560
/// use holonics::hnn::RingDeclaration;
/// // A per-ring exponent is not a declarable value (design R2 C1).
/// fn per_ring(ring: RingDeclaration) -> RingDeclaration {
///     RingDeclaration { exponent: holonics::ratio::integer(2), ..ring }
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingDeclaration {
    /// `d_g`, at least 2: the rotor's period and the port chart's population.
    pub period: u64,
    /// The screw generator (axis and pitch) shared by the ring's nodes.
    pub screw: ScrewGenerator,
    /// The `d_g` node placements, rational points of the screw's circle.
    pub placements: Vec<RatVec3>,
    /// The lock `N_g ⊂ ℤ/d_g`: the port classes on which the ring steps.
    pub lock: Vec<u64>,
    /// The reflector `F_g`, an involution of `ℤ/d_g`, as its images.
    pub reflector: Vec<usize>,
    /// The storage-port admittance `Y_g > 0`.
    pub admittance: Rat,
    /// The initial configuration: the ring's phase class before any key is published.
    pub initial: u64,
}

/// [definition] **A contact as declared**: its ends `(from → to)`, its channel as a node matching,
/// its reference admittance `Y_a > 0` and its one participation exponent `β_a`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContactDeclaration {
    pub from: usize,
    pub to: usize,
    /// `(node of from, node of to)`: the partial matchings `ι_(a,from)`, `ι_(a,to)`, one complex
    /// node (two realified coordinates) per pair.
    pub channel: Vec<(usize, usize)>,
    pub admittance: Rat,
    pub exponent: Rat,
}

/// [definition] **An admitted receiver as declared**: its receiving ring, its aperture `A`, its
/// code tolerance `ε_bits` per cell, from which its grain `L_R = ⌈1/ε_bits⌉` is derived, and the
/// depth `D` of its landmark tree's address (Decision 28; `hnn::receiving::landmark_declaration`):
/// the receiving parametron's storage is the tree over the last `D` cells, and `D = 1` with the
/// root's split forced is Decision 27's region table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiverDeclaration {
    pub ring: usize,
    pub aperture: usize,
    pub tolerance: Rat,
    pub depth: usize,
}

/// [definition] **The crib as declared**: the `window` cells that open each aeon, read at `offset`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CribDeclaration {
    pub window: usize,
    pub offset: usize,
}

/// [definition] **A field as declared.** Rings are listed in carry order. Loops are declared as
/// ring cycles (each consecutive pair, and the last with the first, joined by a contact).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldDeclaration {
    pub rings: Vec<RingDeclaration>,
    pub contacts: Vec<ContactDeclaration>,
    pub loops: Vec<Vec<usize>>,
    /// The source rings `𝒮`: only they ingest.
    pub sources: Vec<usize>,
    /// The declared offsets `Δ` of the pair port.
    pub offsets: Vec<usize>,
    /// `|A|`, the exterior chart's size. It enters only the capacity `n*`, never the widths.
    pub alphabet: usize,
    /// The hop's duration `h > 0`.
    pub step: Rat,
    /// The exponent grain `L ≥ 1`: `s_a ∈ (1/L)ℤ`.
    pub exponent_grain: u64,
    pub receivers: Vec<ReceiverDeclaration>,
    pub crib: CribDeclaration,
    /// The declared population (the cut's length in cells), refused below `n*`.
    pub population: u64,
    /// The declared carrier lattice exponent `L_ℓ` of every learned locus (its entries live on
    /// `2^(−L_ℓ)ℤ`; `hnn::constitution`): exactly the field's learned loci, each once, and each at
    /// least the rule's ([`FieldDeclaration::lattice_by_rule`]), which [`Field::declare`] checks.
    pub lattice: BTreeMap<Locus, u32>,
}

/// The quarter turns of the unit circle `x² + y² = 1`, counterclockwise from `(1, 0)`: the only
/// rational rotations of finite order in the plane.
const QUARTER_TURNS: [(i64, i64); 4] = [(1, 0), (0, 1), (-1, 0), (0, -1)];

impl FieldDeclaration {
    /// [definition; agent-inferred] **Campaign 1's declared values** (design (d), "Declared values",
    /// R2 M14, R3 D2): UTF-8 bytes (`|A| = 256`); four closing rings of periods 5, 7, 11, 13 in that
    /// carry order; the 4-cycle `0–1–2–3–0` with its one 2-cell; channels matching node `i` of
    /// both ends for `i < min(d_g, d_h)`; `𝒮 = {0}`, `R = 2`, `A = 2`; locks `{0}` on rings 0–2 and
    /// `∅` on ring 3; reflectors `p ↦ −p mod d_g`; every ring at phase 0; one axis `e_z` through the
    /// origin, pitch 0, node `k` of ring `g` at the quarter turn `⌊4k/d_g⌋` of the unit circle
    /// ([`FieldDeclaration::quarter_turn`]); `β_a = 2`, `L = 1`; `h = 1`, `Y_g = Y_a = 2`; `L_R = 16`
    /// (tolerance 1/16 bit); the receiver's landmark tree at address depth `D = 4` (Decision 28, chosen
    /// on the development cells in the landmark receipt);
    /// `Δ = {1}`; the crib `W_crib = 64` at offset 1. The population is the cut's length. The carrier
    /// lattices follow [`FieldDeclaration::lattice_by_rule`]: `L = 9, 9, 10, 10` for the four rings'
    /// elements and standings, `10` for ring 2's receiving map, `9, 9, 10, 9` for the four channels,
    /// and `⌈log₂(32 · population)⌉` for ring 0's source ports (`22` on a cut of 2^17 cells, `23`
    /// on the notebook's pinned 171,754-byte cut). The word's precisions follow by rule at
    /// [`Field::declare`] (Decision 24): `L_R = 16`, `X_w = 22`, the widest solve `26` and
    /// `e_max = 4` give the target `2^(−19)`, `L_c = 38` and `L_w = 15`.
    pub fn campaign_one(population: u64) -> Self {
        let periods = [5u64, 7, 11, 13];
        let axis = ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero());
        let rings = periods
            .iter()
            .enumerate()
            .map(|(index, &period)| RingDeclaration {
                period,
                screw: axis.clone(),
                placements: (0..period)
                    .map(|node| Self::quarter_turn(node, period))
                    .collect(),
                lock: if index < 3 { vec![0] } else { Vec::new() },
                reflector: (0..period)
                    .map(|port| ((period - port) % period) as usize)
                    .collect(),
                admittance: integer(2),
                initial: 0,
            })
            .collect();
        let contacts = [(0usize, 1usize), (1, 2), (2, 3), (3, 0)]
            .iter()
            .map(|&(from, to)| ContactDeclaration {
                from,
                to,
                channel: (0..periods[from].min(periods[to]) as usize)
                    .map(|node| (node, node))
                    .collect(),
                admittance: integer(2),
                exponent: integer(2),
            })
            .collect();
        Self {
            rings,
            contacts,
            loops: vec![vec![0, 1, 2, 3]],
            sources: vec![0],
            offsets: vec![1],
            alphabet: 256,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 2,
                aperture: 2,
                tolerance: rat(1, 16),
                depth: 4,
            }],
            crib: CribDeclaration {
                window: 64,
                offset: 1,
            },
            population,
            lattice: BTreeMap::new(),
        }
        .by_lattice_rule()
    }

    /// [definition; agent-inferred] **The placement rule** (design (d), "Declared values", review
    /// C2): node `k` of a ring of period `d` sits at the quarter turn `⌊4k/d⌋` of the unit circle
    /// about `e_z`, its phase `k/d` in turns read at the rational rotations of finite order, which
    /// in the plane are exactly the quarter turns (design (a): "a rotation of finite order in the
    /// plane is rational only at quarter turns"). The period stays combinatorial, so several nodes
    /// share a quarter turn. Integer placements keep every quadrance an integer (`q_Q = 1`), and
    /// `Q ∈ {0, 2, 4}` on one circle: with the least lattice exponent `β_a = 2`, one contact
    /// attenuates by `1`, `1/4` or `1/16`, and the source-to-receiver path is open (at least the
    /// receiver's grain `1/16`) on 4,328 of campaign 1's 5,005 phase configurations (receipt:
    /// `cargo run --release -p holonics --example hnn_lattice_growth -- openness configurations`;
    /// `… openness uniform` and `… openness cut` read the windows of `n*` uniform bytes and of the
    /// notebook's pinned cut). The earlier
    /// sixteen points of `x² + y² = 65` put distinct nodes at `Q ≥ 4` apart and up to 260, which
    /// shielded the receiver below `2^(−10)` on about 96% of windows (review C2).
    pub fn quarter_turn(node: u64, period: u64) -> RatVec3 {
        let (x, y) = QUARTER_TURNS[((4 * node) / period.max(1)) as usize % 4];
        RatVec3::from_i64(x, y, 0)
    }

    /// The learned loci of the declaration, each with `X_ℓ`, the declared bound on the ℓ1 norm of
    /// the operand one read of the locus sums: its fan-in `w_ℓ` for unit-scale waves, and the
    /// population for a source ring's ports, whose operands are the moment's counts.
    fn learned_loci(&self) -> BTreeMap<Locus, u128> {
        let mut loci = BTreeMap::new();
        for (g, ring) in self.rings.iter().enumerate() {
            let width = 2 * ring.placements.len() as u128;
            loci.insert(Locus::Element(g), width);
            loci.insert(Locus::Standing(g), width);
        }
        for &g in &self.sources {
            // The counts of one phase (or one pair offset) sum to at most the cells ingested.
            let counts = u128::from(self.population).max(self.alphabet as u128);
            loci.insert(Locus::SourcePort(g), counts);
        }
        for receiver in &self.receivers {
            let width = self
                .rings
                .get(receiver.ring)
                .map_or(1, |ring| 2 * ring.placements.len() as u128);
            loci.insert(Locus::ReceivingMap(receiver.ring), width);
        }
        for (a, contact) in self.contacts.iter().enumerate() {
            loci.insert(Locus::Channel(a), 2 * contact.channel.len() as u128);
        }
        loci
    }

    /// [definition; agent-inferred] **The lattice rule** (design (d), "Declared values"): each
    /// learned locus `ℓ` takes `L_ℓ = ⌈log₂(2 L_R X_ℓ)⌉`, with `L_R = ⌈1/ε_bits⌉` the finest
    /// declared receiver grain and `X_ℓ` the declared bound on the ℓ1 norm of the operand one read
    /// of the locus sums: its fan-in for unit-scale waves (the ring width `2d_g` for its element
    /// and standing, the receiving ring's width for `R`, `k_a` for a channel), and the population
    /// for a source ring's ports, whose operands are the moment's counts. So on a locus the word
    /// reads **linearly**, the normal-law maps `E_g`, `R` and `W_c`, a carried remainder
    /// (`|r| ≤ 2^(−L_ℓ−1)`) moves one read by at most `X_ℓ 2^(−L_ℓ−1) ≤ 1/(4L_R)`, and the value
    /// the word reads, within one unit of the exact accumulation since the locus's founding, by at
    /// most `X_ℓ 2^(−L_ℓ) ≤ 1/(2L_R)`: below the receiver's grain (Lean
    /// `HNN/LatticeDeposit.{remainder_below_grain, within_one_unit_since_founding}`). [open] The
    /// factor loci enter the word quadratically or trilinearly (`C = ccᵀ`, `K = bbᵀ`, `D = FFᵀ`,
    /// `W_s = −ffᵀ`, the slices `uvᵀ − vuᵀ`, the pair port `e(a·x)(b·y)`): the rule bounds each
    /// factor entry the same way, not their product, and the bound on a read through them is the
    /// word-level certificate owed in #62 ("Step 4 (#73) owed: the word-level certificate"). The remainder
    /// is carried, never released by the aeon collapse, which releases only exact complements
    /// (Decision 22); each deposit releases only its tail below the refining precision `k_m`, and
    /// the tails of one entry sum below half a unit since the locus's founding
    /// (`release_bounded_since_founding`). Since `X_ℓ` is at least the locus's Gram width, a carried
    /// Gram stays positive definite, `H ⪰ (1 − 1/(2L_R)) I` (`carried_gram_posDef_rule`). The unit
    /// scale of the waves is an assumption the notebook measures at each boundary. Brandon may
    /// override the rule.
    pub fn lattice_by_rule(&self) -> BTreeMap<Locus, u32> {
        let grain: u128 = self
            .receivers
            .iter()
            .filter(|receiver| receiver.tolerance.is_positive())
            .filter_map(|receiver| {
                (Rat::one() / &receiver.tolerance)
                    .ceil()
                    .to_integer()
                    .to_u128()
            })
            .max()
            .unwrap_or(1);
        self.learned_loci()
            .into_iter()
            .map(|(locus, fan_in)| {
                let reach = 2u128.saturating_mul(grain).saturating_mul(fan_in.max(1));
                let exponent = if reach <= 1 {
                    0
                } else {
                    128 - (reach - 1).leading_zeros()
                };
                (locus, exponent)
            })
            .collect()
    }

    /// The declaration with its lattices set by [`FieldDeclaration::lattice_by_rule`].
    pub fn by_lattice_rule(mut self) -> Self {
        self.lattice = self.lattice_by_rule();
        self
    }
}

// -------------------------------------------------------------------------------------------
// the ring

/// [definition] **A closing rotor ring**, checked. See the module header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ring {
    period: u64,
    navigator: Navigator,
    reflector: PortPermutation,
    lock: Vec<bool>,
    screw: ScrewGenerator,
    placements: Vec<RatVec3>,
    carry: RatVec3,
    admittance: Rat,
    parametron: Parametron,
    initial: u64,
}

impl Ring {
    fn declare(index: usize, declared: &RingDeclaration) -> Result<Self, HnnError> {
        let period = declared.period;
        if period < 2 {
            return Err(HnnError::RingPeriod {
                ring: index,
                period,
            });
        }
        let d = usize::try_from(period).map_err(|_| HnnError::RingPeriod {
            ring: index,
            period,
        })?;
        if declared.placements.len() != d {
            return Err(HnnError::Shape {
                what: "ring placements",
                expected: d,
                found: declared.placements.len(),
            });
        }
        let ScrewAxis::Rotating {
            origin,
            direction,
            pitch,
        } = declared.screw.axis()
        else {
            return Err(HnnError::NoRingAxis { ring: index });
        };
        // The placements lie on one circle of the axis: one height along it and one nonzero radius
        // about it. The period is combinatorial (design (a)), so two nodes may share a placement.
        let height = |point: &RatVec3| point.subtract(&origin).dot(&direction);
        let radius = |point: &RatVec3| point.subtract(&origin).cross(&direction).norm_squared();
        let (first_height, first_radius) = (
            height(&declared.placements[0]),
            radius(&declared.placements[0]),
        );
        for (node, point) in declared.placements.iter().enumerate() {
            if height(point) != first_height
                || radius(point) != first_radius
                || first_radius.is_zero()
            {
                return Err(HnnError::NotOnCircle { ring: index, node });
            }
        }
        let mut lock = vec![false; d];
        for &notch in &declared.lock {
            if notch >= period {
                return Err(HnnError::Notch {
                    ring: index,
                    notch,
                    period,
                });
            }
            lock[notch as usize] = true;
        }
        if declared.initial >= period {
            return Err(HnnError::Initial {
                ring: index,
                initial: declared.initial,
            });
        }
        if !declared.admittance.is_positive() {
            return Err(HnnError::RingAdmittance {
                ring: index,
                admittance: declared.admittance.clone(),
            });
        }
        let reflector = PortPermutation::new(declared.reflector.clone())
            .map_err(|_| HnnError::Reflector { ring: index })?;
        if reflector.ports() != d || reflector.multiply(&reflector)? != PortPermutation::identity(d)
        {
            return Err(HnnError::Reflector { ring: index });
        }
        let navigator = Navigator::rotor(period, declared.initial, Rat::one())?;
        // The ring's Parametron with unit weights: branch i joins node i to node i + 1.
        let incidence = crate::ratio::linear::vector::matrix(d, d, |branch, node| {
            if node == branch {
                -Rat::one()
            } else if node == (branch + 1) % d {
                Rat::one()
            } else {
                Rat::zero()
            }
        })?;
        let parametron = Parametron::new(incidence, vec![Rat::one(); d], vec![Rat::one(); d])?;
        Ok(Self {
            period,
            navigator,
            reflector,
            lock,
            screw: declared.screw.clone(),
            placements: declared.placements.clone(),
            carry: direction.scale(&pitch),
            admittance: declared.admittance.clone(),
            parametron,
            initial: declared.initial,
        })
    }

    /// `d_g`.
    pub fn period(&self) -> u64 {
        self.period
    }

    /// The realified width `2d_g`.
    pub fn width(&self) -> usize {
        2 * self.placements.len()
    }

    /// **The ring's navigator**: the finite-order port map `P_g` (`Transport::Map`), its key the
    /// declared initial configuration, its clock a ring of period `d_g`, its lift at rest. The
    /// evolving phase class and winding are the lift point's ([`Current`]).
    pub fn navigator(&self) -> &Navigator {
        &self.navigator
    }

    /// The reflector `F_g`, an involution of the port chart.
    pub fn reflector(&self) -> &PortPermutation {
        &self.reflector
    }

    /// **The keys' reflector machine**: the navigator's rotor `P_g` with the reflector `F_g`
    /// (`compression::keys`), built where key location needs it.
    pub fn machine(&self) -> Result<ReflectorMachine, HnnError> {
        let rotor = self
            .navigator
            .map()
            .ok_or(HnnError::Shape {
                what: "a ring navigator's port map",
                expected: 1,
                found: 0,
            })?
            .clone();
        Ok(ReflectorMachine::new(rotor, self.reflector.clone())?)
    }

    /// **The ring's clock at a lift coordinate**: its navigator's clock advanced `λ_g` ticks, so
    /// its digit is the phase class and its overflow the winding.
    pub fn clock_at(&self, lift: &BigInt) -> Result<Clock, HnnError> {
        let ticks = lift.to_biguint().ok_or(HnnError::Shape {
            what: "a nonnegative lift coordinate",
            expected: 0,
            found: 1,
        })?;
        let mut clock = self.navigator.clock().clone();
        clock.advance(&ticks);
        Ok(clock)
    }

    /// The port class of an exterior code: `port_g(x) = code(x) mod d_g`.
    pub fn port(&self, code: usize) -> usize {
        code % self.placements.len()
    }

    /// Whether a port class fits the lock `N_g`.
    pub fn fits(&self, port: usize) -> bool {
        self.lock.get(port).copied().unwrap_or(false)
    }

    /// The notches of the lock, sorted.
    pub fn notches(&self) -> Vec<u64> {
        (0..self.period)
            .filter(|port| self.lock[*port as usize])
            .collect()
    }

    pub fn screw(&self) -> &ScrewGenerator {
        &self.screw
    }

    pub fn placements(&self) -> &[RatVec3] {
        &self.placements
    }

    /// The carry per winding: the generator's axial advance `v_∥ = pitch · ω`.
    pub fn winding_carry(&self) -> &RatVec3 {
        &self.carry
    }

    /// **Ring `g`'s point at lift `τ`**: `x_g(τ mod d_g, ⌊τ/d_g⌋) = placement + winding · v_∥`.
    pub fn point(&self, lift: &BigInt) -> RatVec3 {
        let (phase, winding) = phase_winding(lift, self.period);
        self.placements[phase as usize].add(&self.carry.scale(&Rat::from_integer(winding)))
    }

    /// The situated screw of the node at lift `τ`: the ring's generator at that point.
    pub fn situated(&self, lift: &BigInt) -> SituatedScrew {
        SituatedScrew::new(self.screw.clone(), self.point(lift))
    }

    pub fn admittance(&self) -> &Rat {
        &self.admittance
    }

    /// The reflector `F_g`'s image of a port.
    pub fn reflection(&self, port: usize) -> usize {
        self.reflector.images()[port % self.placements.len()]
    }

    pub fn parametron(&self) -> &Parametron {
        &self.parametron
    }

    pub fn initial(&self) -> u64 {
        self.initial
    }

    /// **`P_g^k` on the realified ring**: the navigator's map to the power `k`, read modulo its
    /// order (Lean `Holon/Generator.map_pow_mod_order`), carries node `i`'s two coordinates to node
    /// `P_g^k(i)`.
    pub fn rotate(&self, vector: &[Rat], k: &BigInt) -> Vec<Rat> {
        let (shift, _) = phase_winding(k, self.period);
        let power = self
            .navigator
            .map()
            .expect("a ring's navigator is its rotor map")
            .power(&BigUint::from(shift));
        let mut rotated = vec![Rat::zero(); vector.len()];
        for (node, target) in power.images().iter().enumerate() {
            rotated[2 * target] = vector[2 * node].clone();
            rotated[2 * target + 1] = vector[2 * node + 1].clone();
        }
        rotated
    }
}

/// `(τ mod d, ⌊τ/d⌋)` with floor semantics.
pub(crate) fn phase_winding(lift: &BigInt, period: u64) -> (u64, BigInt) {
    let d = BigInt::from(period);
    let mut phase = lift % &d;
    if phase.is_negative() {
        phase += &d;
    }
    let winding = (lift - &phase) / &d;
    (
        phase.to_u64().expect("a phase lies below its period"),
        winding,
    )
}

// -------------------------------------------------------------------------------------------
// the contact

/// Which end of a contact.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum End {
    From,
    To,
}

/// [definition] **A pair contact**, checked. See the module header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Contact {
    from: usize,
    to: usize,
    channel: Vec<(usize, usize)>,
    admittance: Rat,
    exponent: Rat,
}

impl Contact {
    fn declare(
        index: usize,
        declared: &ContactDeclaration,
        rings: &[Ring],
    ) -> Result<Self, HnnError> {
        for ring in [declared.from, declared.to] {
            if ring >= rings.len() {
                return Err(HnnError::RingOutside {
                    ring,
                    rings: rings.len(),
                });
            }
        }
        if declared.from == declared.to {
            return Err(HnnError::SelfContact {
                contact: index,
                ring: declared.from,
            });
        }
        let (from_nodes, to_nodes) = (
            rings[declared.from].placements.len(),
            rings[declared.to].placements.len(),
        );
        for (position, &(g, h)) in declared.channel.iter().enumerate() {
            let earlier = &declared.channel[..position];
            if g >= from_nodes || earlier.iter().any(|(other, _)| *other == g) {
                return Err(HnnError::Channel {
                    contact: index,
                    node: g,
                });
            }
            if h >= to_nodes || earlier.iter().any(|(_, other)| *other == h) {
                return Err(HnnError::Channel {
                    contact: index,
                    node: h,
                });
            }
        }
        if !declared.admittance.is_positive() {
            return Err(HnnError::Admittance {
                contact: index,
                admittance: declared.admittance.clone(),
            });
        }
        Ok(Self {
            from: declared.from,
            to: declared.to,
            channel: declared.channel.clone(),
            admittance: declared.admittance.clone(),
            exponent: declared.exponent.clone(),
        })
    }

    /// `(from, to)`.
    pub fn ends(&self) -> (usize, usize) {
        (self.from, self.to)
    }

    /// The ring at one end.
    pub fn ring(&self, end: End) -> usize {
        match end {
            End::From => self.from,
            End::To => self.to,
        }
    }

    /// The channel width `k_a`: two realified coordinates per matched node.
    pub fn width(&self) -> usize {
        2 * self.channel.len()
    }

    /// The node matching.
    pub fn channel(&self) -> &[(usize, usize)] {
        &self.channel
    }

    /// The realified coordinates the matching `ι_(a,end)` selects, in channel order.
    pub fn selection(&self, end: End) -> Vec<usize> {
        self.channel
            .iter()
            .flat_map(|&(g, h)| {
                let node = match end {
                    End::From => g,
                    End::To => h,
                };
                [2 * node, 2 * node + 1]
            })
            .collect()
    }

    /// `Y_a`.
    pub fn admittance(&self) -> &Rat {
        &self.admittance
    }

    /// `β_a`: one exponent per contact, read at both ends.
    pub fn exponent(&self) -> &Rat {
        &self.exponent
    }

    /// **The pair contact of the two rings' screws** at the lift point: `Q`, `J`, `DQ`, `D²Q` read
    /// by the existing owner at the two nodes the rings' phases and windings place.
    pub fn pair(&self, field: &Field, lift: &[BigInt]) -> PairContact {
        let (g, h) = (&field.rings[self.from], &field.rings[self.to]);
        PairContact::of(ScrewPair::new(
            g.situated(&lift[self.from]),
            h.situated(&lift[self.to]),
        ))
    }
}

// -------------------------------------------------------------------------------------------
// the field

/// What one cell's selective step did: each ring's ticks, and whether the joint clock carried out.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SelectiveStep {
    pub ticks: Vec<u8>,
    pub carry_out: bool,
}

/// [definition] **The HNN field**, declared and checked. See the module header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
    rings: Vec<Ring>,
    contacts: Vec<Contact>,
    incident: Vec<Vec<usize>>,
    loops: Vec<Vec<usize>>,
    complex: CellComplex,
    connection: ConnectionIncidence,
    sources: Vec<usize>,
    offsets: Vec<usize>,
    alphabet: usize,
    step: Rat,
    exponent_grain: u64,
    quadrance_denominator: BigInt,
    receivers: Vec<ReceiverDeclaration>,
    crib: CribDeclaration,
    population: u64,
    capacity: Capacity,
    distances: Vec<Vec<Option<usize>>>,
    lattices: BTreeMap<Locus, Lattice>,
    /// The word's declared precisions by rule ([`WordLattice::by_rule`]); `None` only for the
    /// exact law's own tests (`Field::with_exact_word`).
    word: Option<WordLattice>,
}

impl Field {
    /// **Declare a field**: every ring and contact checked, the complex built with `∂∘∂ = 0`, one
    /// exponent per contact on its lattice `(2q_Q/L)ℤ`, every ring reached from a source ring, and
    /// the capacity `n*` counted, refusing a population shorter than it.
    ///
    /// The ring count and widths are fixed without the exterior alphabet, which enters only `n*`
    /// (guard 9).
    pub fn declare(declared: FieldDeclaration) -> Result<Self, HnnError> {
        if declared.rings.is_empty() {
            return Err(HnnError::Shape {
                what: "rings",
                expected: 1,
                found: 0,
            });
        }
        if !declared.step.is_positive() || declared.exponent_grain == 0 || declared.alphabet == 0 {
            return Err(HnnError::NonpositiveDeclaration);
        }
        let rings = declared
            .rings
            .iter()
            .enumerate()
            .map(|(index, ring)| Ring::declare(index, ring))
            .collect::<Result<Vec<_>, _>>()?;
        let contacts = declared
            .contacts
            .iter()
            .enumerate()
            .map(|(index, contact)| Contact::declare(index, contact, &rings))
            .collect::<Result<Vec<_>, _>>()?;
        let mut incident = vec![Vec::new(); rings.len()];
        for (index, contact) in contacts.iter().enumerate() {
            incident[contact.from].push(index);
            incident[contact.to].push(index);
        }
        // Every quadrance lies in (1/q_Q)ℤ with q_Q the square of the placements' and carries'
        // common denominator; the exponent lattice is (2 q_Q / L)ℤ.
        let mut denominator = BigInt::one();
        for ring in &rings {
            for point in ring.placements.iter().chain([&ring.carry]) {
                for coordinate in [&point.x, &point.y, &point.z] {
                    denominator = lcm(&denominator, coordinate.denom());
                }
            }
        }
        let quadrance_denominator = &denominator * &denominator;
        let lattice = Rat::from_integer(BigInt::from(2) * &quadrance_denominator)
            / Rat::from_integer(BigInt::from(declared.exponent_grain));
        for (index, contact) in contacts.iter().enumerate() {
            if !(&contact.exponent / &lattice).is_integer() {
                return Err(HnnError::ExponentLattice {
                    contact: index,
                    exponent: Box::new(contact.exponent.clone()),
                    lattice: Box::new(lattice),
                });
            }
        }
        let loop_cells = declared
            .loops
            .iter()
            .enumerate()
            .map(|(index, cycle)| loop_contacts(index, cycle, &contacts))
            .collect::<Result<Vec<_>, _>>()?;
        let complex = build_complex(rings.len(), &contacts, &loop_cells)?;
        let connection = build_connection(&rings, &contacts)?;
        let loops = declared.loops.clone();
        if declared.sources.is_empty() {
            return Err(HnnError::NoSource);
        }
        for &ring in declared
            .sources
            .iter()
            .chain(declared.receivers.iter().map(|r| &r.ring))
        {
            if ring >= rings.len() {
                return Err(HnnError::RingOutside {
                    ring,
                    rings: rings.len(),
                });
            }
        }
        for &offset in &declared.offsets {
            if offset == 0 {
                return Err(HnnError::Offset { offset });
            }
        }
        if declared.crib.offset == 0 {
            return Err(HnnError::Offset {
                offset: declared.crib.offset,
            });
        }
        let learned = declared.learned_loci();
        if let Some(locus) = learned
            .keys()
            .find(|locus| !declared.lattice.contains_key(locus))
            .or_else(|| {
                declared
                    .lattice
                    .keys()
                    .find(|locus| !learned.contains_key(locus))
            })
        {
            return Err(HnnError::Lattice { locus: *locus });
        }
        // The certificates the constitution cites since a locus's founding (the carried Gram's
        // positivity and a read's bound below the receiver's grain) need `2 L_R X_ℓ ≤ 2^(L_ℓ)`: a
        // lattice coarser than the rule's is refused (a finer one keeps both).
        let rule = declared.lattice_by_rule();
        for (locus, &exponent) in &declared.lattice {
            if let Some(&least) = rule.get(locus)
                && exponent < least
            {
                return Err(HnnError::LatticeBelowRule {
                    locus: *locus,
                    declared: exponent,
                    rule: least,
                });
            }
        }
        let lattices: BTreeMap<Locus, Lattice> = declared
            .lattice
            .iter()
            .map(|(locus, exponent)| (*locus, Lattice::new(*exponent)))
            .collect();
        let distances = hop_distances(rings.len(), &contacts);
        for ring in 0..rings.len() {
            if declared
                .sources
                .iter()
                .all(|source| distances[*source][ring].is_none())
            {
                return Err(HnnError::Unreached { ring });
            }
        }
        let mut sources = declared.sources.clone();
        sources.sort_unstable();
        sources.dedup();
        let mut offsets = declared.offsets.clone();
        offsets.sort_unstable();
        offsets.dedup();
        let periods: Vec<u64> = rings.iter().map(Ring::period).collect();
        let capacity = capacity(&periods, &sources, declared.alphabet, &offsets)?;
        let word = Some(word_by_rule(
            &rings,
            &contacts,
            &sources,
            &distances,
            &declared.receivers,
        ));
        if declared.population < capacity.n_star() {
            return Err(HnnError::BelowCapacity {
                population: declared.population,
                n_star: capacity.n_star(),
            });
        }
        Ok(Self {
            rings,
            contacts,
            incident,
            loops,
            complex,
            connection,
            sources,
            offsets,
            alphabet: declared.alphabet,
            step: declared.step,
            exponent_grain: declared.exponent_grain,
            quadrance_denominator,
            receivers: declared.receivers,
            crib: declared.crib,
            population: declared.population,
            capacity,
            distances,
            lattices,
            word,
        })
    }

    /// **The word's declared precisions** (Decision 24; [`WordLattice::by_rule`]): the charts'
    /// lattice `L_c`, the certificate's target `2^(−D_c)` and the transients' lattice `L_w`. `None`
    /// is the exact law, which only the law's own tests declare (`Field::with_exact_word`).
    pub fn word_lattice(&self) -> Option<&WordLattice> {
        self.word.as_ref()
    }

    /// **The field with its word executed by the exact law**: every inverse exact and every
    /// transient unsplit, the law the lattice word's certificates are read against. Only the law's
    /// own tests declare it; every declared field carries the rule's lattices.
    #[cfg(test)]
    pub(crate) fn with_exact_word(mut self) -> Self {
        self.word = None;
        self
    }

    /// The declared carrier lattice of a learned locus; `None` for a declared locus (a junction or
    /// a conductance), which no deposit reaches.
    pub fn lattice(&self, locus: Locus) -> Option<Lattice> {
        self.lattices.get(&locus).copied()
    }

    /// Every learned locus's declared lattice.
    pub fn lattices(&self) -> &BTreeMap<Locus, Lattice> {
        &self.lattices
    }

    pub fn rings(&self) -> &[Ring] {
        &self.rings
    }

    /// Ring `g`, at an index the field issued (a contact's end, a source, a receiver, a locus):
    /// every such index is checked at [`Field::declare`]. A caller's own index reads
    /// [`Field::rings`] with `get`, which refuses by `None`.
    pub fn ring(&self, ring: usize) -> &Ring {
        &self.rings[ring]
    }

    pub fn contacts(&self) -> &[Contact] {
        &self.contacts
    }

    /// Contact `a`, at an index the field issued (a ring's incidence, a locus): checked at
    /// [`Field::declare`]. A caller's own index reads [`Field::contacts`] with `get`.
    pub fn contact(&self, contact: usize) -> &Contact {
        &self.contacts[contact]
    }

    /// The contacts meeting a ring, in declaration order.
    pub fn incident(&self, ring: usize) -> &[usize] {
        &self.incident[ring]
    }

    /// The declared loops, as ring cycles.
    pub fn loops(&self) -> &[Vec<usize>] {
        &self.loops
    }

    /// The complex `K`: rings, contacts and loops with `∂∘∂ = 0`.
    pub fn complex(&self) -> &CellComplex {
        &self.complex
    }

    pub fn sources(&self) -> &[usize] {
        &self.sources
    }

    pub fn is_source(&self, ring: usize) -> bool {
        self.sources.contains(&ring)
    }

    pub fn offsets(&self) -> &[usize] {
        &self.offsets
    }

    /// `|A|`.
    pub fn alphabet(&self) -> usize {
        self.alphabet
    }

    /// `h`.
    pub fn step(&self) -> &Rat {
        &self.step
    }

    /// `L`.
    pub fn exponent_grain(&self) -> u64 {
        self.exponent_grain
    }

    /// `q_Q`: every quadrance lies in `(1/q_Q)ℤ`.
    pub fn quadrance_denominator(&self) -> &BigInt {
        &self.quadrance_denominator
    }

    pub fn receivers(&self) -> &[ReceiverDeclaration] {
        &self.receivers
    }

    pub fn crib(&self) -> CribDeclaration {
        self.crib
    }

    pub fn population(&self) -> u64 {
        self.population
    }

    /// The capacity crossover `n*` and its certificate.
    pub fn capacity(&self) -> &Capacity {
        &self.capacity
    }

    /// The contact-hop distance between two rings, when joined.
    pub fn distance(&self, from: usize, to: usize) -> Option<usize> {
        self.distances[from][to]
    }

    /// The front's first epoch at a ring: `min_(g∈𝒮) dist(g, ring)`.
    pub fn first_epoch(&self, ring: usize) -> Option<usize> {
        self.sources
            .iter()
            .filter_map(|source| self.distances[*source][ring])
            .min()
    }

    /// **The joint clock torus** whose lift point is the [`Current`]: one circle per ring, of its
    /// period.
    pub fn parametric(&self) -> ClockLift {
        ClockLift::new(
            self.rings
                .iter()
                .map(|ring| BigUint::from(ring.period))
                .collect(),
        )
        .expect("every declared period is at least 2")
    }

    /// **One cell's selective step on a lift point**, in carry order: ring `g` advances
    /// `[port_g(x) ∈ N_g]` plus its predecessor's carry; the last ring's carry is the carry-out.
    /// Lean `HNN/Moment.selective_position`.
    pub fn selective_step(
        &self,
        lift: &mut [BigInt],
        code: usize,
    ) -> Result<SelectiveStep, HnnError> {
        if code >= self.alphabet {
            return Err(HnnError::CellOutside {
                code,
                alphabet: self.alphabet,
            });
        }
        if lift.len() != self.rings.len() {
            return Err(HnnError::Shape {
                what: "lift point",
                expected: self.rings.len(),
                found: lift.len(),
            });
        }
        let mut ticks = Vec::with_capacity(self.rings.len());
        let mut carry = 0u8;
        for (ring, tau) in self.rings.iter().zip(lift.iter_mut()) {
            let advance = u8::from(ring.fits(ring.port(code))) + carry;
            let (phase, _) = phase_winding(tau, ring.period);
            *tau += advance;
            carry = u8::from(phase + u64::from(advance) >= ring.period);
            ticks.push(advance);
        }
        Ok(SelectiveStep {
            ticks,
            carry_out: carry == 1,
        })
    }

    /// [definition] **The field's block connection incidence `d_A`** (design (a), "The one object";
    /// addition 2, review F4), built once at the declaration: ring `g` is a vertex carrying its
    /// realified nodes `ℚ^(2d_g)`, and contact `a = (g→h)` an edge whose transport is the partial
    /// isometry `T_a = U_aᵀ = ι_(a,g) ι_(a,h)ᵀ` from ring `h`'s nodes to ring `g`'s, so
    /// `(d_A q)_a = U_aᵀ q_h − q_g` (Lean `Holon/Complex.blockIncidence`). [agent-inferred] The
    /// design writes the block at the contact's `to` end, `U_a q_g − q_h`; the owner's orientation
    /// reads it at the `from` end, which agrees with [`Field::complex`]'s `∂₁` at the identity
    /// matching. Its underlying complex is the field's 1-skeleton, so `∂∘∂ = 0` is kept; a declared
    /// loop whose channels carry every node of its base ring is flat, and its covariant face
    /// coboundary composes with `d_A` to zero (`block_flat_closed`). Its consumer is the contrast
    /// map ([`Field::contrast`]), which reads its blocks.
    pub fn connection(&self) -> &ConnectionIncidence {
        &self.connection
    }

    /// [definition] **The contrast map at a ring** (design (a), "Sheet classes"), read from the
    /// blocks of the connection incidence [`Field::connection`]: for a vector `x_g` on every ring,
    ///
    /// ```text
    /// (M x)_r = Σ_(a: s a = r) T_a x_(t a) + Σ_(a: t a = r) T_aᵀ x_(s a) − x_r ,   T_a = U_aᵀ
    /// ```
    ///
    /// ring `r`'s own row blocks of `d_A` read forward and its column blocks transposed, so that
    /// `M q` is the standing contrast `Δ_r = Σ_(a∋r) U_(r←a) q_(other end) − q_r`. [definition] `M`
    /// is symmetric (its off-diagonal blocks are `T_a` at `(s a, t a)` and `T_aᵀ` at
    /// `(t a, s a)`, its diagonal `−I`), so its transpose, which carries the class covectors back to
    /// `q` (design (a), "The standing moves only by deposition"), is the same map: the one owner of
    /// both. Refused on a vector field of the wrong shape.
    pub fn contrast(&self, ring: usize, values: &[&[Rat]]) -> Result<Vec<Rat>, HnnError> {
        if ring >= self.rings.len() {
            return Err(HnnError::RingOutside {
                ring,
                rings: self.rings.len(),
            });
        }
        if values.len() != self.rings.len() {
            return Err(HnnError::Shape {
                what: "a vector on every ring",
                expected: self.rings.len(),
                found: values.len(),
            });
        }
        for (g, value) in values.iter().enumerate() {
            if value.len() != self.rings[g].width() {
                return Err(HnnError::Shape {
                    what: "a ring's realified vector",
                    expected: self.rings[g].width(),
                    found: value.len(),
                });
            }
        }
        let mut contrast: Vec<Rat> = values[ring].iter().map(|x| -x).collect();
        let (sources, targets) = (self.connection.sources(), self.connection.targets());
        for &a in &self.incident[ring] {
            let block = self.connection.transport(a).ok_or(HnnError::Shape {
                what: "a contact's block of the connection incidence",
                expected: self.contacts.len(),
                found: a,
            })?;
            let carried = if sources[a] == ring {
                block.apply(values[targets[a]])?
            } else {
                block.transpose()?.apply(values[sources[a]])?
            };
            for (x, y) in contrast.iter_mut().zip(carried) {
                *x += y;
            }
        }
        Ok(contrast)
    }

    /// **The standing contrast** `Δ_r` of ring `r` at a constitution: the contrast map
    /// ([`Field::contrast`]) on the standings `q`. Its sheet classes `σ_ρ = sign Δ_r[ρ]`
    /// (`sign 0 = +1`) are the element's lock classes.
    pub fn standing_contrast(
        &self,
        constitution: &impl ConstitutionRead,
        ring: usize,
    ) -> Result<Vec<Rat>, HnnError> {
        let standings: Vec<&[Rat]> = (0..self.rings.len())
            .map(|g| constitution.standing(g))
            .collect();
        self.contrast(ring, &standings)
    }

    /// The declared loops that are oriented walks of contacts, each with its base ring: the cells
    /// of [`ConnectionIncidence::face_coboundary`] (the flatness test's reading).
    #[cfg(test)]
    pub(crate) fn loop_walks(&self) -> Vec<(Vec<usize>, usize)> {
        self.loops
            .iter()
            .enumerate()
            .filter_map(|(index, cycle)| {
                let cells = loop_contacts(index, cycle, &self.contacts).ok()?;
                cells
                    .iter()
                    .all(|(_, along)| *along)
                    .then(|| (cells.iter().map(|(a, _)| *a).collect(), cycle[0]))
            })
            .collect()
    }

    /// [definition] **The HNN as a Holarchy: a read-only chart built from the field and the one
    /// constitution** (design (c), `Field::holon()`; review F2), block by block (guard 14):
    ///
    /// ```text
    /// ring g     x_g ∈ ℚ^(2d_g),  storage ½|x_g|²,  ẋ_g = (Ω_g − R_g + W_c,g) x_g + B_g f_g,  e_g = B_gᵀ x_g
    ///            Ω_g = Σ_ρ σ_ρ A_ρ (the skew slices at the sheet classes),  R_g = f fᵀ = −W_s,g,  W_c,g active
    ///            B_g = [ι_(a,from)] at each contact leaving g,  [−ι_(a,to)] at each contact entering g
    /// contact a  (u_a, p_a),  storage ½uᵀK_a u + ½pᵀC_a⁻¹p,  u̇ = w,  ṗ = −K_a u − D_a w + e_(a,from) + e_(a,to)
    ///            (w = C_a⁻¹p; both end ports carry the flow w)
    /// ```
    ///
    /// Each ring is its own Holon (storage, resistive, external and active ports; one external
    /// block of `k_a` ports per contact end it carries, in contact order) and each contact its own
    /// medium (a `k_a`-port block at each end), every one certified Dirac on its own. The rings
    /// are joined side by side (no shared port), the contacts likewise, and the two wholes are
    /// interconnected at every contact end, the equal-effort, opposite-flow join
    /// (`holarchy::{Holarchy, Gluing}`) whose nine checks read the shared ports one by one. The
    /// contact's force is the channel difference `ι_(a,g)ᵀ x_g − ι_(a,h)ᵀ x_h` of the block incidence
    /// [`Field::connection`], `(d_A x)_a = U_aᵀ x_h − x_g` read on the channel; its rate leaves ring
    /// `g`'s channel and enters ring `h`'s. The whole is the one Holarchy of the field (storage: the
    /// rings in order, then each contact's `(u_a, p_a)`), assembled only when read
    /// ([`Holarchy::whole`]). The rings carry their navigators. Every element relation is read from
    /// the constitution, so the chart is never a second owner of `Θ`; a deposit is seen by building
    /// the chart again. [agent-inferred] The chart is the continuous Holon whose tick the word takes
    /// in wave variables; the word's junction Swing and midpoint two-port are its scattering form,
    /// and the chart claims no more. A singular contact storage `C_a` is refused: its momentum chart
    /// needs `C_a⁻¹`.
    ///
    /// Its consumer is the mount ([`crate::hnn::Reference::mount_with`]): the resident's
    /// declaration certifies the field at the mounted constitution a Holarchy that glues, refused
    /// with its typed defect, and keeps the Holarchy's parametric orientation
    /// ([`Holarchy::parametric`], equal to [`Field::parametric`]) as the complex of every aeon the
    /// resident reads. The mount costs what the blocks cost: no dense whole is assembled. The chart
    /// glues at ports, with no glued cell complex, so a receiver's `view` and `count` of its regions
    /// are a declared absence at the aeon boundary.
    pub fn holon(&self, constitution: &impl ConstitutionRead) -> Result<Holarchy, HnnError> {
        // Each ring's contact ends, in contact order.
        let ends: Vec<Vec<(usize, End)>> = (0..self.rings.len())
            .map(|g| {
                self.contacts
                    .iter()
                    .enumerate()
                    .filter_map(|(a, contact)| {
                        if contact.from == g {
                            Some((a, End::From))
                        } else if contact.to == g {
                            Some((a, End::To))
                        } else {
                            None
                        }
                    })
                    .collect()
            })
            .collect();
        let rings = (0..self.rings.len())
            .map(|g| self.ring_holon(constitution, g, &ends[g]))
            .collect::<Result<Vec<_>, _>>()?;
        let contacts = (0..self.contacts.len())
            .map(|a| self.contact_holon(constitution, a))
            .collect::<Result<Vec<_>, _>>()?;
        // The contact ends' external ports on the contacts' side: `from` then `to`, per contact.
        let mut contact_port = Vec::with_capacity(self.contacts.len());
        let mut offset = 0;
        for contact in &self.contacts {
            contact_port.push(offset);
            offset += 2 * contact.width();
        }
        let mut shared = Vec::new();
        let mut ring_port = 0;
        for incident in &ends {
            for &(a, end) in incident {
                let k = self.contacts[a].width();
                let at = contact_port[a] + if end == End::From { 0 } else { k };
                shared.extend((0..k).map(|j| (ring_port + j, at + j)));
                ring_port += k;
            }
        }
        let glued = |defect| HnnError::Holon(HolonError::Gluing(Box::new(defect)));
        side_by_side(rings)?
            .interconnect(&side_by_side(contacts)?, &Gluing::at_ports(shared)?)
            .map_err(glued)
    }

    /// Ring `g`'s own Holon: storage `σ = 2d_g`, resistive `σ`, one external block per contact end
    /// in `ends`, active `σ`, on the kernel form
    /// `f_S + B_g f_P + Ω e_S + e_R + e_A = 0; f_R − e_S = 0; e_P − B_gᵀ e_S = 0; f_A − e_S = 0`,
    /// certified Dirac on its own `3σ + Σ k_a` ports; it carries the ring's navigator.
    fn ring_holon(
        &self,
        constitution: &impl ConstitutionRead,
        g: usize,
        ends: &[(usize, End)],
    ) -> Result<Holon, HnnError> {
        let ring = &self.rings[g];
        let operands = crate::hnn::propagation::ring_operands(self, constitution, g)?;
        let sigma = ring.width();
        let ports: usize = ends.iter().map(|(a, _)| self.contacts[*a].width()).sum();
        let mut omega = vec![vec![Rat::zero(); sigma]; sigma];
        let mut resistance = vec![vec![Rat::zero(); sigma]; sigma];
        let mut active = vec![vec![Rat::zero(); sigma]; sigma];
        for i in 0..sigma {
            for j in 0..sigma {
                let passive = operands.passive().get(i, j)?.clone();
                omega[i][j] = operands.element().get(i, j)? - &passive;
                resistance[i][j] = -passive;
                active[i][j] = operands.contrast().get(i, j)?.clone();
            }
        }
        // B_g: +1 at (ι_from's node coordinate, port) for a contact leaving g, −1 at ι_to's for
        // one entering it.
        let mut input = vec![vec![Rat::zero(); ports]; sigma];
        let mut port = 0;
        for &(a, end) in ends {
            let sign = if end == End::From {
                Rat::one()
            } else {
                -Rat::one()
            };
            for (j, coordinate) in self.contacts[a].selection(end).into_iter().enumerate() {
                input[coordinate][port + j] = sign.clone();
            }
            port += self.contacts[a].width();
        }
        let n = 3 * sigma + ports;
        let kind = |i: usize| -> (u8, usize) {
            if i < sigma {
                (0, i)
            } else if i < 2 * sigma {
                (1, i - sigma)
            } else if i < 2 * sigma + ports {
                (2, i - 2 * sigma)
            } else {
                (3, i - 2 * sigma - ports)
            }
        };
        let unit = |a: usize, b: usize| if a == b { Rat::one() } else { Rat::zero() };
        let flow = crate::ratio::linear::vector::matrix(n, n, |row, column| {
            match (kind(row), kind(column)) {
                ((0, i), (0, j)) | ((1, i), (1, j)) | ((3, i), (3, j)) => unit(i, j),
                ((0, i), (2, k)) => input[i][k].clone(),
                _ => Rat::zero(),
            }
        })?;
        let effort = crate::ratio::linear::vector::matrix(n, n, |row, column| {
            match (kind(row), kind(column)) {
                ((0, i), (0, j)) => omega[i][j].clone(),
                ((0, i), (1, j)) | ((0, i), (3, j)) => unit(i, j),
                ((1, i), (0, j)) | ((3, i), (0, j)) => -unit(i, j),
                ((2, k), (0, i)) => -input[i][k].clone(),
                ((2, k), (2, l)) => unit(k, l),
                _ => Rat::zero(),
            }
        })?;
        let port_holon = PortHolon::new(
            DiracStructure::kernel_form(&flow, &effort)?,
            PortCounts {
                storage: sigma,
                resistive: sigma,
                external: ports,
                active: sigma,
            },
            SymmetricForm::from_rows(
                (0..sigma)
                    .map(|i| (0..sigma).map(|j| unit(i, j)).collect())
                    .collect(),
            )
            .map_err(HolonError::from)?,
            ResistiveRelation::new(ExactRatMatrix::shaped(sigma, sigma, resistance)?)?,
        )?;
        Ok(Holon::new(port_holon)?
            .with_active(ActiveRelation::new(ExactRatMatrix::shaped(
                sigma, sigma, active,
            )?)?)?
            .with_navigator(ring.navigator().clone()))
    }

    /// Contact `a`'s own Holon: the medium on `(u_a, p_a)` with storage `(K_a, C_a⁻¹)`,
    /// dissipation `D_a` on `p_a`, and two `k_a`-port blocks, its `from` end then its `to` end, each
    /// driving `ṗ_a` and each carrying the flow `w = C_a⁻¹ p_a`.
    fn contact_holon(
        &self,
        constitution: &impl ConstitutionRead,
        a: usize,
    ) -> Result<Holon, HnnError> {
        let k = self.contacts[a].width();
        let stiffness = crate::hnn::propagation::gram(constitution.contact_stiffness(a))?;
        let dissipation = crate::hnn::propagation::gram(constitution.contact_dissipation(a))?;
        let compliance =
            crate::hnn::propagation::gram(constitution.contact_storage(a))?.inverse()?;
        let mut omega = vec![vec![Rat::zero(); 2 * k]; 2 * k];
        let mut resistance = vec![vec![Rat::zero(); 2 * k]; 2 * k];
        let mut storage = vec![vec![Rat::zero(); 2 * k]; 2 * k];
        let mut input = vec![vec![Rat::zero(); 2 * k]; 2 * k];
        for i in 0..k {
            omega[i][k + i] = Rat::one();
            omega[k + i][i] = -Rat::one();
            input[k + i][i] = Rat::one();
            input[k + i][k + i] = Rat::one();
            for j in 0..k {
                storage[i][j] = stiffness.get(i, j)?.clone();
                storage[k + i][k + j] = compliance.get(i, j)?.clone();
                resistance[k + i][k + j] = dissipation.get(i, j)?.clone();
            }
        }
        Ok(Holon::new(PortHolon::medium(
            &ExactRatMatrix::shaped(2 * k, 2 * k, omega)?,
            &ExactRatMatrix::shaped(2 * k, 2 * k, resistance)?,
            SymmetricForm::from_rows(storage).map_err(HolonError::from)?,
            &ExactRatMatrix::shaped(2 * k, 2 * k, input)?,
            false,
        )?)?)
    }

    /// **The field's exact self-delimiting code**: every declared value, each receiver's tree depth
    /// `D` (Decision 28), the word's precisions (`L_c`, `D_c`, `L_w`; none for the exact law),
    /// the recorded `n*`, the gauge convention, the sign generator's rule, the receiving law's code
    /// ([`RECEIVING_LAW`]) with the tree's Krichevsky–Trofimov prior `α`, and the constitution's declared values (the
    /// steps `γ_U` and `η_x`, the budget `B_Θ`) with the pending capacity, as Elias-gamma naturals,
    /// zig-zag integers and rationals as (numerator, denominator). It is the one exact code of the
    /// declaration (guard 13), and `Kt` pays for every part of it (design (f), review D3).
    pub fn describe(&self, steps: &Steps, budget: u64, pending_capacity: usize) -> Vec<bool> {
        let mut code = Vec::new();
        natural(&mut code, self.rings.len() as u64);
        for ring in &self.rings {
            natural(&mut code, ring.period);
            naturals(&mut code, &ring.notches());
            let reflector: Vec<u64> = (0..ring.placements.len())
                .map(|port| ring.reflection(port) as u64)
                .collect();
            naturals(&mut code, &reflector);
            for vector in [ring.screw.angular(), ring.screw.advance()] {
                vector3(&mut code, vector);
            }
            for placement in &ring.placements {
                vector3(&mut code, placement);
            }
            rational(&mut code, &ring.admittance);
            natural(&mut code, ring.initial);
        }
        natural(&mut code, self.contacts.len() as u64);
        for contact in &self.contacts {
            natural(&mut code, contact.from as u64);
            natural(&mut code, contact.to as u64);
            natural(&mut code, contact.channel.len() as u64);
            for &(g, h) in &contact.channel {
                natural(&mut code, g as u64);
                natural(&mut code, h as u64);
            }
            rational(&mut code, &contact.admittance);
            rational(&mut code, &contact.exponent);
        }
        natural(&mut code, self.loops.len() as u64);
        for cycle in &self.loops {
            naturals(
                &mut code,
                &cycle.iter().map(|c| *c as u64).collect::<Vec<_>>(),
            );
        }
        naturals(
            &mut code,
            &self.sources.iter().map(|s| *s as u64).collect::<Vec<_>>(),
        );
        naturals(
            &mut code,
            &self.offsets.iter().map(|o| *o as u64).collect::<Vec<_>>(),
        );
        natural(&mut code, self.alphabet as u64);
        rational(&mut code, &self.step);
        natural(&mut code, self.exponent_grain);
        natural(&mut code, self.receivers.len() as u64);
        for receiver in &self.receivers {
            natural(&mut code, receiver.ring as u64);
            natural(&mut code, receiver.aperture as u64);
            rational(&mut code, &receiver.tolerance);
            natural(&mut code, receiver.depth as u64);
        }
        natural(&mut code, self.crib.window as u64);
        natural(&mut code, self.crib.offset as u64);
        natural(&mut code, self.population);
        natural(&mut code, self.lattices.len() as u64);
        for (locus, lattice) in &self.lattices {
            let (kind, index) = match *locus {
                Locus::Element(g) => (0, g),
                Locus::Junction(g) => (1, g),
                Locus::Channel(a) => (2, a),
                Locus::Conductance(a) => (3, a),
                Locus::SourcePort(g) => (4, g),
                Locus::Standing(g) => (5, g),
                Locus::ReceivingMap(g) => (6, g),
            };
            natural(&mut code, kind);
            natural(&mut code, index as u64);
            natural(&mut code, u64::from(lattice.exponent()));
        }
        // The word's precisions (Decision 24): `L_c`, `D_c`, `L_w`; none for the exact law.
        match &self.word {
            Some(word) => naturals(
                &mut code,
                &[
                    u64::from(word.chart_exponent()),
                    u64::from(word.target_exponent()),
                    u64::from(word.transient_exponent()),
                ],
            ),
            None => naturals(&mut code, &[]),
        }
        natural(&mut code, self.capacity.n_star());
        // The gauge convention (design R3 K2): 0 names "S_g(p_0) = 0 at the least visited port".
        natural(&mut code, 0);
        // The sign generator's rule (design (d)): 0 names "the low bit of SplitMix64 over
        // (0, ℓ, i, j)" (`constitution::declared_sign`).
        natural(&mut code, 0);
        // The receiving law (Decision 28) and the tree's Krichevsky–Trofimov prior `α = 1/2`.
        natural(&mut code, RECEIVING_LAW);
        rational(&mut code, &rat(1, 2));
        // The constitution's declared values and the resident's pending capacity.
        rational(&mut code, &steps.proxy);
        rational(&mut code, &steps.factor);
        natural(&mut code, budget);
        natural(&mut code, pending_capacity as u64);
        code
    }
}

/// [definition; agent-inferred] **The receiving law's code in the description** (Decision 28): 3,
/// "the receiving face is the grain of the receiving parametron's landmark tree (the `Digits`
/// emission, Krichevsky–Trofimov masses with `α` coded beside it, context-tree weighting over the
/// per-cell causal address of depth `D`, coded with each receiver, and the executed dyadic face)
/// plus the wave `R P_R^(τ_R) v_R`, `R` opening at zero and moving by the prox step on its reached
/// covectors, every comparison scored and then deposited" (`hnn::receiving`, `hnn::landmark`).
/// Code 2 was Decision 27's region class masses with `R` opening at the sign generator times ½;
/// code 1 Decision 26's exogenous normal law on the target code face with the standing read; and
/// campaign 1's first law (the face on the change alone) carried none. A feature-law change takes
/// the next code and starts a fresh constitution: an old statistic cannot be re-read through new
/// features without the samples retention forbids.
pub const RECEIVING_LAW: u64 = 3;

/// **The word's precisions by rule** ([`WordLattice::by_rule`]): the finest receiver grain
/// `L_R = ⌈1/ε_bits⌉`, the widest receiving fan-in `X_w = 2d_R`, the widest local solve (a ring's
/// `2d_g` or a channel's `k_a`) and the most junction steps `e_max = e_0 + A` of an admitted
/// receiver.
fn word_by_rule(
    rings: &[Ring],
    contacts: &[Contact],
    sources: &[usize],
    distances: &[Vec<Option<usize>>],
    receivers: &[ReceiverDeclaration],
) -> WordLattice {
    let grain = receivers
        .iter()
        .filter(|receiver| receiver.tolerance.is_positive())
        .filter_map(|receiver| receiver.tolerance.recip().ceil().to_integer().to_u64())
        .max()
        .unwrap_or(1);
    let fan_in = receivers
        .iter()
        .filter_map(|receiver| rings.get(receiver.ring))
        .map(|ring| ring.width() as u64)
        .max()
        .unwrap_or(1);
    let width = rings
        .iter()
        .map(Ring::width)
        .chain(contacts.iter().map(Contact::width))
        .max()
        .unwrap_or(1) as u64;
    let steps = receivers
        .iter()
        .filter_map(|receiver| {
            sources
                .iter()
                .filter_map(|source| distances[*source][receiver.ring])
                .min()
                .map(|first| (first + receiver.aperture) as u64)
        })
        .max()
        .unwrap_or(1);
    WordLattice::by_rule(grain, fan_in, width, steps)
}

/// Holons joined side by side, the first leftmost, sharing no port: each join's whole again a
/// Holon whose port Holon is assembled only when read.
fn side_by_side(holons: Vec<Holon>) -> Result<Holon, HnnError> {
    let mut holons = holons.into_iter();
    let Some(first) = holons.next() else {
        // None: the Holon on no ports.
        let none = ExactRatMatrix::zero(0, 0)?;
        return Ok(Holon::new(PortHolon::medium(
            &none,
            &none,
            SymmetricForm::from_rows(Vec::new()).map_err(HolonError::from)?,
            &none,
            false,
        )?)?);
    };
    let apart = Gluing::at_ports(Vec::new())?;
    holons.try_fold(first, |joined, next| {
        Ok(joined
            .interconnect(&next, &apart)
            .map_err(|defect| HnnError::Holon(HolonError::Gluing(Box::new(defect))))?
            .whole()
            .clone())
    })
}

/// The contacts a declared ring cycle traverses, each signed `+1` along `from → to` and `−1`
/// against it.
fn loop_contacts(
    index: usize,
    cycle: &[usize],
    contacts: &[Contact],
) -> Result<Vec<(usize, bool)>, HnnError> {
    if cycle.len() < 2 {
        return Err(HnnError::Loop { index });
    }
    (0..cycle.len())
        .map(|position| {
            let (g, h) = (cycle[position], cycle[(position + 1) % cycle.len()]);
            contacts
                .iter()
                .enumerate()
                .find_map(|(a, contact)| match (contact.from, contact.to) {
                    (from, to) if (from, to) == (g, h) => Some((a, true)),
                    (from, to) if (from, to) == (h, g) => Some((a, false)),
                    _ => None,
                })
                .ok_or(HnnError::Loop { index })
        })
        .collect()
}

/// The complex: `∂₁` with `−1` at each contact's `from` and `+1` at its `to`; `∂₂` with each loop's
/// contacts signed by the direction its cycle traverses them, so `∂₁∂₂ = 0` telescopes.
fn build_complex(
    rings: usize,
    contacts: &[Contact],
    loops: &[Vec<(usize, bool)>],
) -> Result<CellComplex, HnnError> {
    let boundary_one = crate::ratio::linear::vector::matrix(rings, contacts.len(), |ring, a| {
        if contacts[a].from == ring {
            -Rat::one()
        } else if contacts[a].to == ring {
            Rat::one()
        } else {
            Rat::zero()
        }
    })?;
    if loops.is_empty() {
        return Ok(CellComplex::new(
            vec![rings, contacts.len()],
            vec![boundary_one],
        )?);
    }
    let mut boundary_two = vec![vec![Rat::zero(); loops.len()]; contacts.len()];
    for (column, cycle) in loops.iter().enumerate() {
        for &(a, along) in cycle {
            if along {
                boundary_two[a][column] += Rat::one();
            } else {
                boundary_two[a][column] -= Rat::one();
            }
        }
    }
    let boundary_two = ExactRatMatrix::shaped(contacts.len(), loops.len(), boundary_two)?;
    Ok(CellComplex::new(
        vec![rings, contacts.len(), loops.len()],
        vec![boundary_one, boundary_two],
    )?)
}

/// The block connection incidence of the declared rings and contacts ([`Field::connection`]): each
/// contact's block the 0/1 matrix of `U_aᵀ = ι_(a,from) ι_(a,to)ᵀ`, `2d_from × 2d_to`.
fn build_connection(rings: &[Ring], contacts: &[Contact]) -> Result<ConnectionIncidence, HnnError> {
    let dimensions: Vec<usize> = rings.iter().map(Ring::width).collect();
    let transports = contacts
        .iter()
        .map(|contact| {
            let (rows, columns) = (dimensions[contact.from], dimensions[contact.to]);
            let pairs: Vec<(usize, usize)> = contact
                .selection(End::From)
                .into_iter()
                .zip(contact.selection(End::To))
                .collect();
            crate::ratio::linear::vector::matrix(rows, columns, |row, column| {
                if pairs.contains(&(row, column)) {
                    Rat::one()
                } else {
                    Rat::zero()
                }
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(ConnectionIncidence::blocks(
        dimensions,
        contacts.iter().map(|contact| contact.from).collect(),
        contacts.iter().map(|contact| contact.to).collect(),
        transports,
    )?)
}

/// Breadth-first contact-hop distances between every pair of rings.
fn hop_distances(rings: usize, contacts: &[Contact]) -> Vec<Vec<Option<usize>>> {
    (0..rings)
        .map(|start| {
            let mut distance = vec![None; rings];
            distance[start] = Some(0);
            let mut frontier = vec![start];
            let mut hops = 0;
            while !frontier.is_empty() {
                hops += 1;
                let mut next = Vec::new();
                for &ring in &frontier {
                    for contact in contacts {
                        for (here, there) in
                            [(contact.from, contact.to), (contact.to, contact.from)]
                        {
                            if here == ring && distance[there].is_none() {
                                distance[there] = Some(hops);
                                next.push(there);
                            }
                        }
                    }
                }
                frontier = next;
            }
            distance
        })
        .collect()
}

// -------------------------------------------------------------------------------------------
// the code

/// Elias gamma of `n + 1`: self-delimiting.
fn natural(code: &mut Vec<bool>, n: u64) {
    natural_big(code, &BigUint::from(n));
}

fn natural_big(code: &mut Vec<bool>, n: &BigUint) {
    let value = n + BigUint::one();
    let bits = value.bits();
    code.extend(std::iter::repeat_n(false, (bits - 1) as usize));
    for place in (0..bits).rev() {
        code.push(value.bit(place));
    }
}

fn naturals(code: &mut Vec<bool>, values: &[u64]) {
    natural(code, values.len() as u64);
    for value in values {
        natural(code, *value);
    }
}

/// Zig-zag: `z ≥ 0 ↦ 2z`, `z < 0 ↦ −2z − 1`.
fn integer_code(code: &mut Vec<bool>, z: &BigInt) {
    let two = BigInt::from(2);
    let folded = if z.is_negative() {
        (-z * &two - BigInt::one()).to_biguint()
    } else {
        (z * &two).to_biguint()
    };
    natural_big(code, &folded.expect("a folded integer is nonnegative"));
}

fn rational(code: &mut Vec<bool>, value: &Rat) {
    integer_code(code, value.numer());
    natural_big(
        code,
        &(value.denom() - BigInt::one())
            .to_biguint()
            .expect("a reduced denominator is positive"),
    );
}

fn vector3(code: &mut Vec<bool>, vector: &RatVec3) {
    for coordinate in [&vector.x, &vector.y, &vector.z] {
        rational(code, coordinate);
    }
}

// -------------------------------------------------------------------------------------------
// the current

/// [definition] **The current: the lift point `λ ∈ ℤ^G`** of the rings' joint clock torus, the
/// one owner of every ring's phase class and winding (design (a), review C9). It has no wave or
/// contact-state field, so no change outlives its word (guard 16). The guarantee is structural,
/// the type's own fields; the doctest fails because the field does not exist (`E0609`):
///
/// ```compile_fail,E0609
/// // A current carries no waves: the change lives only in a word.
/// fn carried_change(current: &holonics::hnn::Current) {
///     let _ = &current.waves;
/// }
/// ```
///
/// ```compile_fail,E0609
/// // Nor any contact state.
/// fn carried_contacts(current: &holonics::hnn::Current) {
///     let _ = &current.contacts;
/// }
/// ```
///
/// It has no lifetime parameter (guard 2):
///
/// ```compile_fail,E0107
/// fn borrowed(current: holonics::hnn::Current<'static>) {}
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Current {
    lift: Vec<BigInt>,
}

impl Current {
    /// Every ring at its declared initial configuration, winding zero.
    pub fn at_rest(field: &Field) -> Self {
        Self {
            lift: field
                .rings
                .iter()
                .map(|ring| BigInt::from(ring.initial))
                .collect(),
        }
    }

    /// A declared lift point: one nonnegative coordinate per ring.
    pub fn at(field: &Field, lift: Vec<BigInt>) -> Result<Self, HnnError> {
        if lift.len() != field.rings.len() {
            return Err(HnnError::Shape {
                what: "lift point",
                expected: field.rings.len(),
                found: lift.len(),
            });
        }
        if let Some(ring) = lift.iter().position(Signed::is_negative) {
            return Err(HnnError::NegativeLift { ring });
        }
        Ok(Self { lift })
    }

    /// `λ`.
    pub fn lift(&self) -> &[BigInt] {
        &self.lift
    }

    /// Ring `g`'s lift coordinate with its period, refused outside the field.
    fn coordinate(&self, field: &Field, ring: usize) -> Result<(&BigInt, u64), HnnError> {
        match (self.lift.get(ring), field.rings.get(ring)) {
            (Some(lift), Some(declared)) => Ok((lift, declared.period)),
            _ => Err(HnnError::RingOutside {
                ring,
                rings: field.rings.len().min(self.lift.len()),
            }),
        }
    }

    /// Ring `g`'s phase class `λ_g mod d_g`; refused outside the field.
    pub fn phase(&self, field: &Field, ring: usize) -> Result<u64, HnnError> {
        let (lift, period) = self.coordinate(field, ring)?;
        Ok(phase_winding(lift, period).0)
    }

    /// Ring `g`'s winding `⌊λ_g / d_g⌋`; refused outside the field.
    pub fn winding(&self, field: &Field, ring: usize) -> Result<BigInt, HnnError> {
        let (lift, period) = self.coordinate(field, ring)?;
        Ok(phase_winding(lift, period).1)
    }

    /// One cell's selective step of the lift point ([`Field::selective_step`]).
    pub fn step(&mut self, field: &Field, code: usize) -> Result<SelectiveStep, HnnError> {
        field.selective_step(&mut self.lift, code)
    }

    /// **Re-key one ring**: set its phase class, keeping its winding (design (d), R3 K1; Lean
    /// `HNN/Keys.rekey_keeps_winding`). Returns the jump `new − old` in the ring's phase classes, as
    /// a reading.
    pub fn rekey(&mut self, field: &Field, ring: usize, phase: u64) -> Result<i64, HnnError> {
        let (_, period) = self.coordinate(field, ring)?;
        if phase >= period {
            return Err(HnnError::Initial {
                ring,
                initial: phase,
            });
        }
        let (old, winding) = phase_winding(&self.lift[ring], period);
        self.lift[ring] = winding * BigInt::from(period) + BigInt::from(phase);
        Ok(i64::try_from(phase).unwrap_or(i64::MAX) - i64::try_from(old).unwrap_or(i64::MAX))
    }
}

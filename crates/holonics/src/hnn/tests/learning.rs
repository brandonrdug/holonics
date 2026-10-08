//! Fields, constitutions and cuts for the learning half's laws: the six-ring path of the retired
//! [`release.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/release.py), a small chain for the return's exactness,
//! and generic exact constitutions (control charts).

use crate::hnn::tests::support::encoded;
use super::support::{Draw, contact, ring};
use crate::hnn::constitution::{Constitution, Reach};
use crate::hnn::field::{
    ContactDeclaration, CribDeclaration, Current, Field, FieldDeclaration, ReceiverDeclaration,
};
use crate::hnn::moment::{PairPort, SourceMoment};
use crate::hnn::receiving::ReceivingPhases;
use crate::ratio::{Rat, integer, rat};

/// A generous budget for the laws' tests: the budget itself is tested on its own.
pub(super) const OPEN_BUDGET: u64 = 1 << 40;

/// The test fields declare `2^16` cells, well within the receiving tree's declaration: at `|A| = 4`,
/// `D = 2` it is refused only from 1,712,317 = 233·7349 cells, where a lattice product itself passes 128 bits
/// (the carrier past `u128` rebases, campaign 2: `compression::landmark::context`'s header).
///
/// **The six-ring path of the retired [`release.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/release.py)**: rings of period 2 (realified width 4) joined `(g, g+1)` on
/// node 0 (channel width 2), exponents 0 (so `G_a = Y_a`), source ring 0, receiving ring 2 with
/// the declared aperture, `|A| = 2`, junction admittances `Y_g` and contact admittances `Y_a`.
pub(super) fn path_with(aperture: usize, junctions: &[Rat], contacts: &[Rat]) -> Field {
    let mut rings: Vec<_> = (0..6).map(|_| ring(2, vec![0])).collect();
    for (declared, admittance) in rings.iter_mut().zip(junctions) {
        declared.admittance = admittance.clone();
    }
    let contacts: Vec<ContactDeclaration> = (0..5)
        .map(|g| {
            let mut declared = contact(g, g + 1, 1, 0);
            declared.admittance = contacts[g].clone();
            declared
        })
        .collect();
    Field::declare(
        FieldDeclaration {
            rings,
            contacts,
            loops: Vec::new(),
            sources: vec![0],
            offsets: vec![1],
            alphabet: 2,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 2,
                aperture,
                tolerance: rat(1, 16),
                depth: 2,
                prior: crate::compression::landmark::context::StopPrior::half(),
                mass: 1,
                base: crate::compression::landmark::context::BaseMeasure::Even,
                receiving_prior: 0,
            }],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 16,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

/// The six-ring path with every admittance 2.
pub(super) fn six_path(aperture: usize) -> Field {
    path_with(aperture, &vec![integer(2); 6], &vec![integer(2); 5])
}

/// **A small chain**: rings of periods 4, 3, 2 joined `0–1–2` on their common nodes, exponents 2
/// and 0, source ring 0, receiving ring 2 with aperture 2, `|A| = 4`, `Δ = {1}`; the first contact's
/// admittance as declared. [agent-inferred, October 5; THE_MACHINE guard 9] The source ring's
/// period was 2, which held the four classes only through the residue chart `c mod 2`; it is 4, the
/// least period on which they inject, so every declared test word keeps its classes, and its lock is
/// `{0, 2}`, so each class fits the source ring as it did under the fold (the even classes).
pub(super) fn chain_with(first_admittance: Rat) -> Field {
    chain_declared(first_admittance, 1 << 16, vec![1])
}

/// **The exposure's chain**: the chain with no pair offset (`Δ = ∅`), declared over a population of
/// `population` cells (an exposure's cut is exactly its field's population). Without the offset
/// counts its capacity is `n* = 28` cells (the moment's capacity law: `N(27) ≥ 4^27`,
/// `N(28) < 4^28`; with `Δ = {1}` it is read from the same law, `Field::capacity`), the smallest cut on which the
/// exposure's protocol runs its aeons, keys and budget stop. Its receiver's tree reads the active
/// suffix address, which the resident keeps beside the tree whether or not the moment keeps earlier
/// cells for its offset counts (the landmark tree).
pub(super) fn chain_of(population: u64) -> Field {
    chain_declared(integer(2), population, Vec::new())
}

fn chain_declared(first_admittance: Rat, population: u64, offsets: Vec<usize>) -> Field {
    let mut declared = chain_declaration(population);
    declared.contacts[0].admittance = first_admittance;
    declared.offsets = offsets;
    Field::declare(declared.by_lattice_rule()).unwrap()
}

/// **The chain control's declaration** over a population of `population` cells (`Δ = {1}`, carrier
/// lattices by rule): the fixture of the declaration's own laws. Its capacity is `n* = 134 = 2·67`
/// (`71` on the folded chain before October 5).
pub(super) fn chain_declaration(population: u64) -> FieldDeclaration {
    FieldDeclaration {
        rings: vec![ring(4, vec![0, 2]), ring(3, vec![0]), ring(2, vec![])],
        contacts: vec![contact(0, 1, 2, 2), contact(1, 2, 2, 0)],
        loops: Vec::new(),
        sources: vec![0],
        offsets: vec![1],
        alphabet: 4,
        step: integer(1),
        exponent_grain: 1,
        receivers: vec![ReceiverDeclaration {
            ring: 2,
            aperture: 2,
            tolerance: rat(1, 16),
            depth: 2,
            prior: crate::compression::landmark::context::StopPrior::half(),
            mass: 1,
            base: crate::compression::landmark::context::BaseMeasure::Even,
            receiving_prior: 0,
        }],
        crib: CribDeclaration {
            window: 16,
            offset: 1,
        },
        population,
        lattice: Default::default(),
    }
    .by_lattice_rule()
}

pub(crate) fn chain() -> Field {
    chain_with(integer(2))
}

/// [agent-inferred, October 5; THE_MACHINE guard 9] **The two-class chain**: the chain's former
/// geometry, rings of periods 2, 3, 2 with locks `{0}`, `{0}`, `∅` joined on the same channels and
/// read by the same receiver, reading the two classes its period-2 source ring holds without a fold
/// (`Δ = {1}`, carrier lattices by rule). It is the smallest fold-free fixture of the chain's
/// laws: the claims below that need neither four classes nor a wider source ring run on it, at the
/// configurations and in the carrier the folded chain ran them in.
pub(super) fn chain_two_declaration(population: u64) -> FieldDeclaration {
    let mut declared = chain_declaration(population);
    declared.rings[0] = ring(2, vec![0]);
    declared.alphabet = 2;
    declared.lattice = Default::default();
    declared.by_lattice_rule()
}

/// The two-class chain over a population of `2^16` cells.
pub(super) fn chain_two() -> Field {
    Field::declare(chain_two_declaration(1 << 16)).unwrap()
}

/// The two-class chain with no pair offset, over `population` cells (the exposure's chain).
pub(super) fn chain_two_of(population: u64) -> Field {
    let mut declared = chain_two_declaration(population);
    declared.offsets = Vec::new();
    Field::declare(declared.by_lattice_rule()).unwrap()
}

/// **A hand-built deposit's reach** on the chain (its receiver ring 2 read at ticks 1 and 2, the
/// moment entering once at the open, one phase, every locus of the chain in its diamond): the
/// certified step's reading of an epoch a compare did not compose.
pub(super) fn chain_reach() -> Reach {
    Reach {
        receiver: 2,
        stations: vec![1, 2],
        entries: vec![0],
        phases: 1,
        loci: crate::hnn::retention::loci(&chain()).into_iter().collect(),
    }
}

/// **A generic exact constitution** on a field: every locus carries drawn half-integers (`½ℤ`, on
/// every lattice `L ≥ 1`, so a deposit's denominators stay the updates' own): the passive factor,
/// the contrast port, generic slices, a mixed standing, the source and receiving maps, nonzero
/// pair-port outputs, and generic channel factors.
pub(crate) fn generic(field: &Field, seed: u64) -> Constitution {
    generic_within(field, seed, OPEN_BUDGET)
}

/// [`generic`] under the constitution budget `budget`.
pub(crate) fn generic_within(field: &Field, seed: u64, budget: u64) -> Constitution {
    let mut draw = Draw::new(seed);
    let a = field.alphabet();
    let mut theta = Constitution::initial(field, budget).unwrap();
    for g in 0..field.rings().len() {
        let n = field.ring(g).width();
        theta = theta
            .with_element(
                g,
                draw.half_matrix(n, n),
                draw.half_matrix(n, n),
                (0..n)
                    .map(|_| (draw.half_vector(n), draw.half_vector(n)))
                    .collect(),
            )
            .unwrap();
        let standing = Some(draw.half_vector(n));
        let source = field.is_source(g).then(|| draw.half_matrix(n, a));
        let receiving = field
            .receivers()
            .iter()
            .any(|r| r.ring == g)
            .then(|| draw.half_matrix(2 * a, n));
        theta = theta.with_ports(g, standing, source, receiving).unwrap();
        if field.is_source(g) {
            for &offset in field.offsets() {
                let pair = PairPort::new(
                    (0..n).map(|_| draw.half_vector(n)).collect(),
                    (0..n).map(|_| draw.half_vector(a)).collect(),
                    (0..n).map(|_| draw.half_vector(a)).collect(),
                )
                .unwrap();
                theta = theta.with_pair(g, offset, pair).unwrap();
            }
        }
    }
    for (index, contact) in field.contacts().iter().enumerate() {
        let k = contact.width();
        theta = theta
            .with_channel(
                index,
                draw.half_matrix(k, k),
                draw.half_matrix(k, k),
                draw.half_matrix(k, k),
            )
            .unwrap();
    }
    theta
}

/// A moment of `cells` drawn codes ingested from rest (past any carry-out: the moment's own law
/// continues; only the resident waits for the boundary).
pub(crate) fn moment(field: &Field, seed: u64, cells: usize) -> (Current, SourceMoment) {
    let mut draw = Draw::new(seed);
    let codes: Vec<usize> = (0..cells).map(|_| draw.below(super::support::classes(&field))).collect();
    let mut current = Current::at_rest(field);
    let mut open = SourceMoment::open(field, &current);
    let mut fed = 0;
    while fed < codes.len() {
        fed += open
            .ingest(field, &mut current, &encoded(field, &codes[fed..]))
            .unwrap()
            .cells;
    }
    (current, open)
}

/// The declared receiver's phases at a constitution.
pub(crate) fn phases(field: &Field, theta: &Constitution, current: &Current) -> ReceivingPhases {
    ReceivingPhases::declare(field, theta, current, &field.receivers()[0]).unwrap()
}

/// `⟨a, b⟩` over lists of vectors.
pub(super) fn pairing(a: &[Vec<Rat>], b: &[Vec<Rat>]) -> Rat {
    a.iter()
        .zip(b)
        .map(|(x, y)| x.iter().zip(y).map(|(p, q)| p * q).sum::<Rat>())
        .sum()
}

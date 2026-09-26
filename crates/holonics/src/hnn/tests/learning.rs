//! Fields, constitutions and cuts for the learning half's laws: the six-ring path of `release.py`,
//! a small chain for the return's exactness, and generic exact constitutions (control charts).

use super::support::{Draw, contact, ring};
use crate::hnn::constitution::{Constitution, Steps};
use crate::hnn::field::{
    ContactDeclaration, CribDeclaration, Current, Field, FieldDeclaration, ReceiverDeclaration,
};
use crate::hnn::masses::Regions;
use crate::hnn::moment::{PairPort, SourceMoment};
use crate::hnn::receiving::ReceivingPhases;
use crate::ratio::{Rat, integer, rat};

/// A generous budget for the laws' tests: the budget itself is tested on its own.
pub(super) const OPEN_BUDGET: u64 = 1 << 40;

/// **The six-ring path of `release.py`**: rings of period 2 (realified width 4) joined `(g, g+1)` on
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
                regions: Regions::PrecedingCell,
            }],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 20,
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

/// **A small chain**: rings of periods 2, 3, 2 joined `0–1–2` on their common nodes, exponents 2
/// and 0, source ring 0, receiving ring 2 with aperture 2, `|A| = 4`, `Δ = {1}`; the first contact's
/// admittance as declared.
pub(super) fn chain_with(first_admittance: Rat) -> Field {
    chain_declared(first_admittance, 1 << 20, vec![1])
}

/// **The exposure's chain**: the chain with no pair offset (`Δ = ∅`), declared over a population of
/// `population` cells (an exposure's cut is exactly its field's population). Without the offset
/// counts its capacity is `n* = 17` cells (`71` with `Δ = {1}`), the smallest cut on which the
/// exposure's protocol runs its aeons, keys and budget stop. With no retained window its receiver's
/// region is the whole (Decision 27: the preceding cell needs a window).
pub(super) fn chain_of(population: u64) -> Field {
    chain_declared(integer(2), population, Vec::new())
}

fn chain_declared(first_admittance: Rat, population: u64, offsets: Vec<usize>) -> Field {
    let mut declared = chain_declaration(population);
    declared.contacts[0].admittance = first_admittance;
    if offsets.is_empty() {
        declared.receivers[0].regions = Regions::Whole;
    }
    declared.offsets = offsets;
    Field::declare(declared.by_lattice_rule()).unwrap()
}

/// **The chain control's declaration** over a population of `population` cells (`Δ = {1}`, carrier
/// lattices by rule): the fixture of the declaration's own laws. Its capacity is `n* = 71`.
pub(super) fn chain_declaration(population: u64) -> FieldDeclaration {
    FieldDeclaration {
        rings: vec![ring(2, vec![0]), ring(3, vec![0]), ring(2, vec![])],
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
            regions: Regions::PrecedingCell,
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

pub(super) fn chain() -> Field {
    chain_with(integer(2))
}

/// **A generic exact constitution** on a field: every locus carries drawn half-integers (`½ℤ`, on
/// every lattice `L ≥ 1`, so a deposit's denominators stay the updates' own): the passive factor,
/// the contrast port, generic slices, a mixed standing, the source and receiving maps, nonzero
/// pair-port outputs, and generic channel factors.
pub(super) fn generic(field: &Field, seed: u64) -> Constitution {
    let mut draw = Draw::new(seed);
    let a = field.alphabet();
    let mut theta = Constitution::initial(field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
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
pub(super) fn moment(field: &Field, seed: u64, cells: usize) -> (Current, SourceMoment) {
    let mut draw = Draw::new(seed);
    let codes: Vec<usize> = (0..cells).map(|_| draw.below(field.alphabet())).collect();
    let mut current = Current::at_rest(field);
    let mut open = SourceMoment::open(field, &current);
    let mut fed = 0;
    while fed < codes.len() {
        fed += open
            .ingest(field, &mut current, &codes[fed..])
            .unwrap()
            .cells;
    }
    (current, open)
}

/// The declared receiver's phases at a constitution.
pub(super) fn phases(field: &Field, theta: &Constitution, current: &Current) -> ReceivingPhases {
    ReceivingPhases::declare(field, theta, current, &field.receivers()[0]).unwrap()
}

/// `⟨a, b⟩` over lists of vectors.
pub(super) fn pairing(a: &[Vec<Rat>], b: &[Vec<Rat>]) -> Rat {
    a.iter()
        .zip(b)
        .map(|(x, y)| x.iter().zip(y).map(|(p, q)| p * q).sum::<Rat>())
        .sum()
}

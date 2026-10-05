//! The population at a port (`receiver::population::port`): its face, weights and code are the
//! population's own (the same telescope and bounds as `Population` over families that carry their
//! faces), an enclosed face encloses the code, and a zero face is exact death.

use num_traits::{One, Zero};

use super::port::PortPopulation;
use crate::compression::landmark::context::code_length;
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::{Rat, rat};
use crate::receiver::population::{
    Declaration, Family, Likelihood, Population, PopulationError, Posterior, Readout,
};

/// A family whose face at each cell is scripted: `faces[t][c]`, exact.
struct Scripted {
    faces: Vec<Vec<Rat>>,
    at: usize,
    likelihood: Rat,
}

impl Scripted {
    fn new(faces: Vec<Vec<Rat>>) -> Self {
        Self {
            faces,
            at: 0,
            likelihood: Rat::one(),
        }
    }
}

impl super::Sealed for Scripted {}

impl Family for Scripted {
    fn label(&self) -> String {
        "scripted".to_string()
    }
    fn alphabet(&self) -> usize {
        self.faces[0].len()
    }
    fn description(&self) -> u64 {
        1
    }
    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        Ok(self.faces[self.at].clone())
    }
    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let face = self.faces[self.at][cell].clone();
        self.likelihood *= &face;
        self.at += 1;
        Ok(face)
    }
    fn likelihood(&self) -> Likelihood {
        Likelihood::Exact(self.likelihood.clone())
    }
    fn readout(&self) -> Readout {
        Readout::Keys(super::KeyReadout {
            spaces: Vec::new(),
            survivors: Vec::new(),
            masses: Vec::new(),
            dormant: Vec::new(),
        })
    }
    fn declaration(&self) -> Declaration {
        Declaration::new("scripted", Vec::new())
    }
}

fn point(x: Rat) -> ExactInterval {
    ExactInterval::point(x)
}

/// Two families' scripted faces over a two-class alphabet, three cells, dyadic throughout; the
/// received class is 0 at every cell.
fn script() -> (Vec<Vec<Rat>>, Vec<Vec<Rat>>) {
    let a = vec![
        vec![rat(3, 4), rat(1, 4)],
        vec![rat(5, 16), rat(11, 16)],
        vec![rat(7, 16), rat(9, 16)],
    ];
    let b = vec![
        vec![rat(1, 4), rat(3, 4)],
        vec![rat(9, 16), rat(7, 16)],
        vec![rat(15, 16), rat(1, 16)],
    ];
    (a, b)
}

/// **The population at a port is the population** (Lean
/// `Compression/Landmark/Context/Population.population_mixture`): at every cell its face of each
/// class, its weights and, over the passage, its code are exactly those of `Population` over two
/// families carrying the same faces (one law, `weigh` and the telescope's bounds); on dyadic faces
/// every bound is exact, so the weights are the exact posteriors `π_f L_f/Σ_g π_g L_g`
/// (`1/2, 3/4, 5/8` here) and the passage's product is `½ L_a + ½ L_b = 15/128`.
#[test]
fn the_population_at_a_port_is_the_population() {
    let (a, b) = script();
    let mut port = PortPopulation::new(&[1, 1]).unwrap();
    let mut population = Population::new(vec![
        Box::new(Scripted::new(a.clone())),
        Box::new(Scripted::new(b.clone())),
    ])
    .unwrap();
    let weights = [rat(1, 2), rat(3, 4), rat(5, 8)];
    let (mut la, mut lb) = (Rat::one(), Rat::one());
    for t in 0..3 {
        let faces = population.face().unwrap();
        for class in 0..2 {
            let port_face = port
                .face_of(&[point(a[t][class].clone()), point(b[t][class].clone())])
                .unwrap();
            assert_eq!(port_face, faces[class], "cell {t}, class {class}");
        }
        assert_eq!(port.weight(0).unwrap(), point(weights[t].clone()));
        let w = &la / (&la + &lb);
        assert_eq!(w, weights[t]);
        let q = &w * &a[t][0] + (Rat::one() - &w) * &b[t][0];
        assert_eq!(faces[0], point(q.clone()));
        let code = port
            .code_of(&[point(a[t][0].clone()), point(b[t][0].clone())])
            .unwrap();
        let exact = code_length(&q).unwrap();
        assert!(code.lower <= exact.lower && exact.upper <= code.upper);
        assert_eq!(
            port.receive(&[point(a[t][0].clone()), point(b[t][0].clone())])
                .unwrap(),
            Vec::<usize>::new()
        );
        population.receive(0).unwrap();
        la *= &a[t][0];
        lb *= &b[t][0];
    }
    assert_eq!(port.code().unwrap(), population.code().unwrap());
    let telescope = (&la + &lb) / Rat::from_integer(2.into());
    assert_eq!(telescope, rat(15, 128));
    let exact = code_length(&telescope).unwrap();
    let code = port.code().unwrap();
    assert!(code.lower <= exact.lower && exact.upper <= code.upper);
    assert_eq!(port.cells(), 3);
    assert_eq!(port.prior(0), Some(&rat(1, 2)));
    let alone = port.family_code(0).unwrap().unwrap();
    let exact_a = code_length(&la).unwrap();
    assert!(alone.lower <= exact_a.lower && exact_a.upper <= alone.upper);
}

/// **An enclosed face encloses the code** (Lean `Population.population_mixture_enclosed`): a
/// family read through `[lo, hi]` carries its likelihood between the products of the endpoints, so
/// the population's code encloses the code of every face the enclosure admits: the population read
/// at `lo` alone and at `hi` alone code within it.
#[test]
fn an_enclosed_face_encloses_the_code() {
    let (lo, hi) = (rat(1, 4), rat(5, 16));
    let enclosed = ExactInterval::new(lo.clone(), hi.clone()).unwrap();
    let tree = rat(1, 2);
    let mut port = PortPopulation::new(&[1, 1]).unwrap();
    let mut low = port.clone();
    let mut high = port.clone();
    for _ in 0..3 {
        let faces = [point(tree.clone()), enclosed.clone()];
        let code = port.code_of(&faces).unwrap();
        for (edge, value) in [(&mut low, &lo), (&mut high, &hi)] {
            let at = edge
                .code_of(&[point(tree.clone()), point(value.clone())])
                .unwrap();
            assert!(code.lower <= at.lower && at.upper <= code.upper);
            edge.receive(&[point(tree.clone()), point(value.clone())])
                .unwrap();
        }
        port.receive(&faces).unwrap();
    }
    let code = port.code().unwrap();
    for edge in [&low, &high] {
        let at = edge.code().unwrap();
        assert!(code.lower <= at.lower && at.upper <= code.upper);
    }
}

/// **A zero face is exact death, never a positive floor** (Lean
/// `HolonicAdjointNormalization.replicator_eq_zero_iff`): a family whose face of the received class
/// is exactly zero dies there, its weight exactly zero, its posterior `Dead` and its code none, and
/// the survivor's weight is exactly one; an enclosure that reaches zero without being zero kills
/// nothing; a cell every living family gives zero is refused with nothing moved.
#[test]
fn a_zero_face_is_exact_death() {
    let mut port = PortPopulation::new(&[1, 1]).unwrap();
    port.receive(&[point(rat(3, 4)), point(rat(1, 4))]).unwrap();
    let undecided = ExactInterval::new(Rat::zero(), rat(1, 8)).unwrap();
    assert_eq!(
        port.receive(&[point(rat(1, 2)), undecided]).unwrap(),
        Vec::<usize>::new()
    );
    assert_eq!(port.died(1), None);
    assert_eq!(
        port.family_code(1).unwrap(),
        None,
        "an undecided likelihood's code is unbounded"
    );
    let dying = port
        .receive(&[point(rat(1, 2)), point(Rat::zero())])
        .unwrap();
    assert_eq!(dying, vec![1]);
    assert_eq!(port.died(1), Some(2));
    assert_eq!(port.weight(1).unwrap(), point(Rat::zero()));
    assert_eq!(port.weight(0).unwrap(), point(Rat::one()));
    assert_eq!(port.posterior(1).unwrap(), Posterior::Dead);
    assert_eq!(port.family_code(1).unwrap(), None);
    // The survivor's face is the population's: its weight is one.
    assert_eq!(
        port.face_of(&[point(rat(3, 8)), point(rat(1, 2))]).unwrap(),
        point(rat(3, 8))
    );
    let before = port.clone();
    assert!(matches!(
        port.receive(&[point(Rat::zero()), point(rat(1, 2))]),
        Err(PopulationError::Extinct { cell: 3 })
    ));
    assert_eq!(port, before, "a refused cell moves nothing");
}

/// **Refusals**: a face per declared family, each an enclosure within the unit interval, and
/// descriptions within Kraft's sum.
#[test]
fn the_port_refuses_faces_outside_its_contract() {
    let port = PortPopulation::new(&[1, 1]).unwrap();
    assert!(port.face_of(&[point(rat(1, 2))]).is_err());
    assert!(port.face_of(&[point(rat(1, 2)), point(rat(3, 2))]).is_err());
    assert!(PortPopulation::new(&[0, 1]).is_err());
    assert!(PortPopulation::new(&[]).is_err());
    assert_eq!(
        PortPopulation::new(&[1, 2]).unwrap().prior(0),
        Some(&rat(2, 3))
    );
}

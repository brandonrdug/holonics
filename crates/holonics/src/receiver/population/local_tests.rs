//! The local mixture's laws checked exactly on small fixtures: every rung's face normalized; the
//! opening rung (`d = 0`) the population's whole-passage Bayes, face by face and in its telescope;
//! each rung exact node-local Bayes against the mixture stepped in ℚ context by context, with the
//! declared bound `∏ q ≥ ∏_c max_f π_f L_f(c)` exact; a family winning where it is closest; the
//! floor keeping a dormant member within the certified drift; death at zero likelihood; a chosen
//! rung reading as if it had made every face; the refusals; and the standing's codec refusal.

use std::collections::HashMap;

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::tests::Fixed;
use super::*;
use crate::compression::landmark::context::{
    Capacity, LandmarkDeclaration, LetterFamily, StopPrior, ratio_code_length,
};
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::{Rat, rat};

/// A family whose face is read from the previous cell: row `x` after cell `x`, the last row at the
/// opening.
#[derive(Clone)]
struct Previous {
    rows: Vec<Vec<Rat>>,
    last: usize,
    likelihood: Rat,
    description: u64,
}

impl Previous {
    fn new(rows: Vec<Vec<Rat>>, description: u64) -> Self {
        let last = rows.len() - 1;
        Self {
            rows,
            last,
            likelihood: Rat::one(),
            description,
        }
    }
}

impl Family for Previous {
    fn label(&self) -> String {
        "previous cell".to_string()
    }
    fn alphabet(&self) -> usize {
        self.rows[0].len()
    }
    fn description(&self) -> u64 {
        self.description
    }
    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        Ok(self.rows[self.last].clone())
    }
    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let face = self.rows[self.last][cell].clone();
        self.likelihood *= &face;
        self.last = cell;
        Ok(face)
    }
    fn likelihood(&self) -> Likelihood {
        Likelihood::Exact(self.likelihood.clone())
    }
    fn readout(&self) -> Readout<'_> {
        Readout::Keys(KeyReadout {
            spaces: Vec::new(),
            survivors: Vec::new(),
            masses: Vec::new(),
            dormant: Vec::new(),
        })
    }
    fn declaration(&self) -> Declaration {
        Declaration::new("previous cell", Vec::new())
    }
}

/// Three members on three classes, dyadic faces with odd numerators at most 3: a fixed face, and
/// two previous-cell readers that are each closest after different cells.
fn members() -> Vec<Previous> {
    let q = |a: i64, b: i64| rat(a, b);
    vec![
        Previous::new(
            vec![
                vec![q(1, 2), q(1, 4), q(1, 4)],
                vec![q(1, 2), q(1, 4), q(1, 4)],
                vec![q(1, 2), q(1, 4), q(1, 4)],
                vec![q(1, 2), q(1, 4), q(1, 4)],
            ],
            2,
        ),
        Previous::new(
            vec![
                vec![q(1, 8), q(3, 4), q(1, 8)],
                vec![q(1, 4), q(1, 4), q(1, 2)],
                vec![q(3, 4), q(1, 8), q(1, 8)],
                vec![q(1, 4), q(1, 2), q(1, 4)],
            ],
            2,
        ),
        Previous::new(
            vec![
                vec![q(1, 4), q(1, 4), q(1, 2)],
                vec![q(1, 8), q(1, 8), q(3, 4)],
                vec![q(1, 4), q(1, 2), q(1, 4)],
                vec![q(1, 4), q(1, 4), q(1, 2)],
            ],
            2,
        ),
    ]
}

fn boxed(members: &[Previous]) -> Vec<Box<dyn Family>> {
    members
        .iter()
        .cloned()
        .map(|member| Box::new(member) as Box<dyn Family>)
        .collect()
}

/// A passage whose transitions follow member 1 after cells 0 and 2 and member 2 after cell 1.
const PASSAGE: [usize; 24] = [
    0, 1, 2, 0, 1, 2, 0, 1, 1, 2, 0, 1, 2, 2, 0, 1, 2, 0, 0, 1, 2, 0, 1, 2,
];

/// Each cell's face vector, and each context's `(Σ_f π_f L_f(c), max_f π_f L_f(c))`.
type ExactLocal = (Vec<Vec<Rat>>, Vec<(Rat, Rat)>);

/// The node-local Bayes mixture stepped in ℚ at depth `d`: each cell's face vector before it, and
/// at the end each context's exact `(Σ_f π_f L_f(c), max_f π_f L_f(c))`.
fn exact_local(members: &[Previous], passage: &[usize], depth: usize) -> ExactLocal {
    let mut members = members.to_vec();
    let kraft: Rat = members
        .iter()
        .map(|member| Rat::new(BigInt::one(), BigInt::one() << member.description as usize))
        .sum();
    let priors: Vec<Rat> = members
        .iter()
        .map(|member| {
            Rat::new(BigInt::one(), BigInt::one() << member.description as usize) / &kraft
        })
        .collect();
    let mut contexts: HashMap<Vec<usize>, Vec<Rat>> = HashMap::new();
    let mut faces = Vec::new();
    for (t, &cell) in passage.iter().enumerate() {
        let context: Vec<usize> = (0..depth)
            .map(|back| t.checked_sub(back + 1).map_or(usize::MAX, |at| passage[at]))
            .collect();
        let weights = contexts.entry(context).or_insert_with(|| priors.clone());
        let member_faces: Vec<Vec<Rat>> = members
            .iter()
            .map(|member| member.face().unwrap())
            .collect();
        let total: Rat = weights.iter().sum();
        faces.push(
            (0..3)
                .map(|class| {
                    weights
                        .iter()
                        .zip(&member_faces)
                        .map(|(weight, face)| weight * &face[class])
                        .sum::<Rat>()
                        / &total
                })
                .collect(),
        );
        for (weight, member) in weights.iter_mut().zip(&mut members) {
            *weight *= member.receive(cell).unwrap();
        }
    }
    let totals = contexts
        .values()
        .map(|weights| {
            let most = weights.iter().max().unwrap().clone();
            (weights.iter().sum(), most)
        })
        .collect();
    (faces, totals)
}

/// Every rung's face is a normalized distribution given the past, before every cell, and the face
/// it scores a cell with is its face's class.
#[test]
fn every_rung_face_is_normalized() {
    let mut mixture = LocalMixture::new(boxed(&members()), &[0, 1, 2], 0, 2).unwrap();
    for &cell in &PASSAGE {
        let before: Vec<Vec<Rat>> = (0..3).map(|rung| mixture.face_of(rung).unwrap()).collect();
        for face in &before {
            assert_eq!(face.iter().sum::<Rat>(), Rat::one());
            assert!(face.iter().all(|class| !class.is_negative()));
        }
        assert_eq!(mixture.face().unwrap(), before[0]);
        let scored = mixture.receive(cell).unwrap();
        assert_eq!(scored, before[0][cell]);
        for (rung, face) in before.iter().enumerate() {
            assert_eq!(mixture.rung_face(rung).unwrap(), &face[cell]);
        }
    }
}

/// Lean `Population.local_of_constant`: the opening rung is the population's whole-passage Bayes,
/// face by face (inside the population's enclosed face) and in its telescope
/// `∏ q_t = Σ_f π_f L_f`; on this exact chart no rounding or floor moves it.
#[test]
fn the_opening_rung_is_whole_passage_bayes() {
    let members = members();
    let mut mixture = LocalMixture::new(boxed(&members), &[0], 0, 0).unwrap();
    let mut population = Population::new(boxed(&members)).unwrap();
    let (exact, totals) = exact_local(&members, &PASSAGE, 0);
    let mut product = Rat::one();
    for (t, &cell) in PASSAGE.iter().enumerate() {
        let face = mixture.face().unwrap();
        assert_eq!(face, exact[t]);
        for (class, enclosure) in population.face().unwrap().iter().enumerate() {
            assert!(enclosure.lower <= face[class] && face[class] <= enclosure.upper);
        }
        product *= mixture.receive(cell).unwrap();
        population.receive(cell).unwrap();
    }
    // Three members named by 2 bits each: M = 3/4, π_f = 1/3.
    let whole: Rat = population
        .families()
        .map(|family| {
            let Likelihood::Exact(likelihood) = family.likelihood() else {
                panic!("an exact likelihood")
            };
            rat(1, 3) * likelihood
        })
        .sum();
    assert_eq!(product, whole);
    assert_eq!(totals, vec![(whole, totals[0].1.clone())]);
    let receipt = mixture.receipt(0).unwrap();
    assert_eq!((receipt.roundings, receipt.floors), (0, 0));
    assert_eq!(receipt.drift, Rat::zero());
    let code = population.code().unwrap();
    assert!(code.lower <= receipt.code.upper && receipt.code.lower <= code.upper);
}

/// Lean `Population.{local_telescope, local_mixture_code}`: at `d = 1` and `d = 2` every face is
/// node-local Bayes stepped in ℚ, the faces telescope to the product of the contexts' totals, and
/// the code lies within the declared bound, exactly: `∏ q_t ≥ ∏_c max_f π_f L_f(c)`.
#[test]
fn the_ladder_is_exact_bayes_in_each_context() {
    let members = members();
    let mut mixture = LocalMixture::new(boxed(&members), &[0, 1, 2], 0, 2).unwrap();
    let exact: Vec<ExactLocal> = (0..3)
        .map(|depth| exact_local(&members, &PASSAGE, depth))
        .collect();
    let mut products = vec![Rat::one(); 3];
    for (t, &cell) in PASSAGE.iter().enumerate() {
        for (rung, (faces, _)) in exact.iter().enumerate() {
            assert_eq!(mixture.face_of(rung).unwrap(), faces[t]);
        }
        mixture.receive(cell).unwrap();
        for (rung, product) in products.iter_mut().enumerate() {
            *product *= mixture.rung_face(rung).unwrap();
        }
    }
    for (rung, (_, totals)) in exact.iter().enumerate() {
        let telescope: Rat = totals.iter().map(|(total, _)| total).product();
        let bound: Rat = totals.iter().map(|(_, most)| most).product();
        assert_eq!(products[rung], telescope);
        assert!(products[rung] >= bound);
        let receipt = mixture.receipt(rung).unwrap();
        assert_eq!(receipt.drift, Rat::zero());
        assert_eq!(receipt.contexts, totals.len());
        assert_eq!(receipt.cells, PASSAGE.len() as u64);
        assert!(receipt.code.lower <= receipt.bound.upper);
    }
    assert!(
        products[1] > products[0],
        "a family wins where it is closest"
    );
}

/// A chosen rung reads as if it had made every face: the ladder's rung and the same rung declared
/// alone give the same faces at every cell, and after the choice the mixture scores with it.
#[test]
fn a_chosen_rung_reads_as_if_it_made_every_face() {
    let members = members();
    let mut ladder = LocalMixture::new(boxed(&members), &[0, 1, 2], 0, 2).unwrap();
    let mut alone = LocalMixture::new(boxed(&members), &[1], 0, 0).unwrap();
    for (t, &cell) in PASSAGE.iter().enumerate() {
        if t == PASSAGE.len() / 2 {
            ladder.choose(1).unwrap();
        }
        let scored = ladder.receive(cell).unwrap();
        let single = alone.receive(cell).unwrap();
        assert_eq!(ladder.rung_face(1).unwrap(), &single);
        if t >= PASSAGE.len() / 2 {
            assert_eq!(scored, single);
        }
    }
    assert_eq!(ladder.chosen(), 1);
    assert!(ladder.choose(3).is_err());
}

/// The floor keeps a member that falls behind dormant in its context, never dead: it returns when
/// it wins at the price of a return, `K + log₂ M` bits, so the code lies within the switching path's
/// (member 0 then member 1) and, over the whole passage, below every single member's plus `log₂ M`,
/// which no static mixture reaches.
#[test]
fn the_floor_keeps_a_dormant_member() {
    let members: Vec<Box<dyn Family>> = vec![
        Box::new(Fixed::new(vec![rat(3, 4), rat(1, 4)], 1)),
        Box::new(Fixed::new(vec![rat(1, 4), rat(3, 4)], 1)),
    ];
    let mut mixture = LocalMixture::new(members, &[0], 0, 0).unwrap();
    for _ in 0..200 {
        mixture.receive(0).unwrap();
    }
    let mut last = Rat::zero();
    for _ in 0..200 {
        last = mixture.receive(1).unwrap();
    }
    let receipt = mixture.receipt(0).unwrap();
    assert!(receipt.floors > 0);
    assert!(receipt.drift > Rat::zero());
    assert!(receipt.code.lower <= &receipt.bound.upper + &receipt.drift);
    // The dormant member returned: after its run the face is within a bit of its own.
    assert!(last > rat(3, 8));
    assert!(mixture.died(0).is_none() && mixture.died(1).is_none());
    // The switching path: −log₂ π_0 + code_0(first 200) + (K + log₂ M) + code_1(last 200) + drift,
    // each run's code 200·log₂(4/3), π = 1/2 and M = 2.
    let run = ratio_code_length(
        &num_bigint::BigUint::from(4u8).pow(200),
        &num_bigint::BigUint::from(3u8).pow(200),
    )
    .map(|code| ExactInterval {
        lower: -code.upper,
        upper: -code.lower,
    })
    .unwrap();
    let path = &(&run.upper + &run.upper) + Rat::from_integer(BigInt::from(1 + 64 + 1));
    assert!(receipt.code.upper <= &path + &receipt.drift);
    // Below every single member plus log₂ M over the whole passage.
    assert!(receipt.code.upper < receipt.bound.lower);
}

/// A face with an odd denominator rounds the chart down: every face stays exactly normalized, and
/// the code stays within the declared bound plus the certified drift.
#[test]
fn an_odd_face_rounds_within_the_drift() {
    let members: Vec<Box<dyn Family>> = vec![
        Box::new(Fixed::new(vec![rat(1, 3), rat(2, 3)], 1)),
        Box::new(Fixed::new(vec![rat(2, 3), rat(1, 3)], 1)),
    ];
    let mut mixture = LocalMixture::new(members, &[0, 1], 1, 1).unwrap();
    for t in 0..120usize {
        for rung in 0..2 {
            assert_eq!(
                mixture.face_of(rung).unwrap().iter().sum::<Rat>(),
                Rat::one()
            );
        }
        mixture.receive((t * t / 7) % 2).unwrap();
    }
    for rung in 0..2 {
        let receipt = mixture.receipt(rung).unwrap();
        assert!(receipt.roundings > 0 && receipt.drift > Rat::zero());
        assert!(receipt.code.lower <= &receipt.bound.upper + &receipt.drift);
    }
}

/// A member dies exactly at zero likelihood: it is read no more, the faces stay normalized over
/// the living, and the bound is read over the members alive.
#[test]
fn a_member_dies_at_zero_likelihood() {
    let members: Vec<Box<dyn Family>> = vec![
        Box::new(Fixed::new(vec![rat(1, 1), rat(0, 1)], 1)),
        Box::new(Fixed::new(vec![rat(1, 2), rat(1, 2)], 1)),
    ];
    let mut mixture = LocalMixture::new(members, &[0, 1], 1, 1).unwrap();
    mixture.receive(0).unwrap();
    mixture.receive(1).unwrap();
    assert_eq!(mixture.died(0), Some(1));
    assert_eq!(mixture.member_faces()[0], Some(Rat::zero()));
    mixture.receive(0).unwrap();
    assert_eq!(mixture.member_faces()[0], None);
    for rung in 0..2 {
        assert_eq!(mixture.face_of(rung).unwrap(), vec![rat(1, 2), rat(1, 2)]);
        let receipt = mixture.receipt(rung).unwrap();
        assert!(receipt.code.lower <= &receipt.bound.upper + &receipt.drift);
    }
    // Every living member gives zero: the mixture's face is zero, and then it is extinct.
    let members: Vec<Box<dyn Family>> = vec![Box::new(Fixed::new(vec![rat(1, 1), rat(0, 1)], 0))];
    let mut lone = LocalMixture::new(members, &[0], 0, 0).unwrap();
    assert_eq!(lone.receive(1).unwrap(), Rat::zero());
    assert!(matches!(
        lone.receive(0),
        Err(PopulationError::Extinct { .. })
    ));
}

/// The declared refusals: no member, two alphabets, a Kraft sum past one, an empty or repeated
/// ladder, an address past 64 bits, an undeclared rung, and a cell outside the alphabet.
#[test]
fn the_local_mixture_refuses_what_it_does_not_declare() {
    let two = || -> Box<dyn Family> { Box::new(Fixed::new(vec![rat(1, 2), rat(1, 2)], 1)) };
    assert!(LocalMixture::new(Vec::new(), &[0], 0, 0).is_err());
    assert!(
        LocalMixture::new(
            vec![two(), Box::new(Fixed::new(vec![rat(1, 1)], 1))],
            &[0],
            0,
            0
        )
        .is_err()
    );
    let whole = || -> Box<dyn Family> { Box::new(Fixed::new(vec![rat(1, 2), rat(1, 2)], 0)) };
    assert!(LocalMixture::new(vec![whole(), whole()], &[0], 0, 0).is_err());
    assert!(LocalMixture::new(vec![two()], &[], 0, 0).is_err());
    assert!(LocalMixture::new(vec![two()], &[1, 1], 0, 0).is_err());
    assert!(LocalMixture::new(vec![two()], &[41], 0, 0).is_err());
    assert!(LocalMixture::new(vec![two()], &[40], 0, 0).is_ok());
    assert!(LocalMixture::new(vec![two()], &[0, 1], 2, 0).is_err());
    let mut mixture = LocalMixture::new(vec![two(), two()], &[0], 0, 0).unwrap();
    assert!(matches!(
        mixture.receive(2),
        Err(PopulationError::CellOutside { .. })
    ));
    assert!(mixture.admits(&[0, 1, 2]).is_err());
}

/// The standing streams its members' native checkpoints and the chosen rung's weights; a member
/// without a codec is refused.
#[test]
fn the_standing_streams_the_members_and_the_chosen_rung() {
    let mut fixed = LocalMixture::new(boxed(&members()), &[0], 0, 0).unwrap();
    fixed.receive(0).unwrap();
    assert!(fixed.write_standing(&mut Vec::new()).is_err());
    let tree = |depth| LandmarkDeclaration {
        alphabet: 3,
        depth,
        forced: 0,
        population: 64,
        grain: 16,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
    };
    let members: Vec<Box<dyn Family>> = vec![
        Box::new(TreeFamily::new(tree(1), 1).unwrap()),
        Box::new(TreeFamily::new(tree(3), 1).unwrap()),
    ];
    let mut mixture = LocalMixture::new(members, &[0, 1], 1, 1).unwrap();
    for &cell in &PASSAGE {
        mixture.receive(cell).unwrap();
    }
    let mut first = Vec::new();
    let written = mixture.write_standing(&mut first).unwrap();
    let mut again = Vec::new();
    mixture.write_standing(&mut again).unwrap();
    assert_eq!(first, again);
    let members_bytes: usize = mixture
        .members()
        .map(|member| member.tree_checkpoint().unwrap().len())
        .sum();
    assert_eq!(written, members_bytes as u64);
    // The tag and six words, each member's death, tag and length, the address, the likelihood's
    // bounds, and four contexts (the opening's pad and the three cells) of two weights after the
    // table's count.
    let contexts = mixture.receipt(1).unwrap().contexts;
    assert_eq!(contexts, 4);
    assert_eq!(
        first.len(),
        8 + 5 * 8
            + 2 * (8 + 1 + 8)
            + members_bytes
            + 8
            + 8
            + 4 * 24
            + 16
            + 8
            + contexts * (8 + 2 * 16)
    );
}

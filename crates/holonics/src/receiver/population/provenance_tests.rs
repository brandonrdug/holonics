use super::provenance::MissingProducerTerm;
use crate::ratio::Rat;
use crate::receiver::population::{
    Declaration, Family, KeyReadout, Likelihood, Population as EggPopulation, PopulationError,
    Readout,
};
use num_traits::One;

struct Fixed {
    label: &'static str,
    probabilities: Vec<Rat>,
    likelihood: Rat,
}

impl Fixed {
    fn new(label: &'static str, probabilities: Vec<Rat>) -> Self {
        Self {
            label,
            probabilities,
            likelihood: Rat::one(),
        }
    }
}

impl Family for Fixed {
    fn label(&self) -> String {
        self.label.to_string()
    }
    fn alphabet(&self) -> usize {
        self.probabilities.len()
    }
    fn description(&self) -> u64 {
        1
    }
    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        Ok(self.probabilities.clone())
    }
    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let probability = self.probabilities[cell].clone();
        self.likelihood *= &probability;
        Ok(probability)
    }
    fn likelihood(&self) -> Likelihood {
        Likelihood::Exact(self.likelihood.clone())
    }
    fn readout(&self) -> Readout<'_> {
        Readout::Keys(KeyReadout {
            spaces: vec![1],
            survivors: vec![vec![Vec::new()]],
            masses: vec![],
            dormant: vec![],
        })
    }
    fn declaration(&self) -> Declaration {
        Declaration::new("fixed fixture", vec![])
    }
}

fn rat(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}

#[test]
fn contributions_and_population_face_enclose_the_same_exact_mixture() {
    let population = EggPopulation::new(vec![
        Box::new(Fixed::new("left", vec![rat(1, 3), rat(2, 3)])),
        Box::new(Fixed::new("right", vec![rat(3, 4), rat(1, 4)])),
    ])
    .unwrap();
    let face = population.face().unwrap()[0].clone();
    let contributions = population.face_contributors(0).unwrap();
    assert_eq!(contributions.len(), 2);
    let lower = contributions
        .iter()
        .map(|entry| entry.contribution.lower.clone())
        .sum::<Rat>();
    let upper = contributions
        .iter()
        .map(|entry| entry.contribution.upper.clone())
        .sum::<Rat>();
    let exact_mixture = rat(13, 24);
    assert!(lower <= exact_mixture && exact_mixture <= upper);
    assert!(face.lower <= exact_mixture && exact_mixture <= face.upper);
    assert!(
        contributions
            .iter()
            .all(|entry| entry.key_readout.is_some())
    );
    assert_eq!(
        contributions[0].missing_producer_terms,
        [
            MissingProducerTerm::KeyToContributionRelation,
            MissingProducerTerm::CausalSourceRelation,
        ]
    );
}

#[test]
fn dead_family_and_living_zero_face_are_distinguished() {
    let mut population = EggPopulation::new(vec![
        Box::new(Fixed::new("survivor", vec![rat(1, 1), rat(0, 1)])),
        Box::new(Fixed::new("dies", vec![rat(0, 1), rat(1, 1)])),
    ])
    .unwrap();
    population.receive(0).unwrap();
    let contributions = population.face_contributors(1).unwrap();
    assert_eq!(contributions[0].died_at, None);
    assert_eq!(contributions[0].contribution.lower, rat(0, 1));
    assert_eq!(contributions[0].contribution.upper, rat(0, 1));
    assert_eq!(contributions[1].died_at, Some(0));
    assert_eq!(contributions[1].contribution.lower, rat(0, 1));
    assert_eq!(contributions[1].contribution.upper, rat(0, 1));
}

use super::family_release::{FamilyReleaseError, select_family_class};
use super::sampling::SamplingError;
use super::{Family, Likelihood, Population, PopulationError, Readout};
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;
use num_bigint::BigInt;
use num_traits::{One, Zero};

fn q(n: i64, d: i64) -> Rat {
    Rat::new(BigInt::from(n), BigInt::from(d))
}

struct Fixed {
    face: Vec<Rat>,
    likelihood: Rat,
    description: u64,
}

impl Fixed {
    fn new(face: Vec<Rat>, description: u64) -> Self {
        Self {
            face,
            likelihood: Rat::one(),
            description,
        }
    }
}

impl Family for Fixed {
    fn label(&self) -> String {
        "fixed".into()
    }
    fn alphabet(&self) -> usize {
        self.face.len()
    }
    fn description(&self) -> u64 {
        self.description
    }
    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        Ok(self.face.clone())
    }
    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let p = self.face[cell].clone();
        self.likelihood *= &p;
        Ok(p)
    }
    fn likelihood(&self) -> Likelihood {
        Likelihood::Exact(self.likelihood.clone())
    }
    fn readout(&self) -> Readout<'_> {
        Readout::Keys(super::KeyReadout {
            spaces: vec![1],
            survivors: vec![vec![Vec::new()]],
            masses: Vec::new(),
            dormant: Vec::new(),
        })
    }
    fn declaration(&self) -> super::Declaration {
        super::Declaration::new("fixed", vec![self.description])
    }
}

#[test]
fn point_mass_family_choice_is_certified() {
    let mut population =
        Population::new(vec![Box::new(Fixed::new(vec![Rat::one(), Rat::zero()], 0))]).unwrap();
    population.receive(0).unwrap();
    let face = population.family_posterior_face().unwrap();
    assert_eq!(face, vec![ExactInterval::point(Rat::one())]);
    assert_eq!(population.select_family(&q(1, 2)).unwrap().class, 0);
}

#[test]
fn posterior_bounds_use_the_two_families_charged_mixture() {
    let population = Population::new(vec![
        Box::new(Fixed::new(vec![q(1, 1), q(0, 1)], 1)),
        Box::new(Fixed::new(vec![q(0, 1), q(1, 1)], 2)),
    ])
    .unwrap();
    let posterior = population.family_posterior_face().unwrap();
    assert_eq!(posterior.len(), 2);
    assert!(posterior[0].lower <= q(2, 3) && posterior[0].upper >= q(2, 3));
    assert!(posterior[1].lower <= q(1, 3) && posterior[1].upper >= q(1, 3));
}

#[test]
fn exact_family_class_selection_validates_and_returns_crossing_bounds() {
    let selected = select_family_class(&[q(1, 4), q(3, 4)], &q(1, 4)).unwrap();
    assert_eq!(selected.class, 1);
    assert_eq!(selected.prior_upper, q(1, 4));
    assert_eq!(selected.through_lower, Rat::one());
    assert!(matches!(
        select_family_class(&[q(-1, 4), q(5, 4)], &q(0, 1)),
        Err(FamilyReleaseError::NegativeMass { .. })
    ));
    assert!(matches!(
        select_family_class(&[q(1, 4), q(1, 4)], &q(0, 1)),
        Err(FamilyReleaseError::NotNormalized { .. })
    ));
}

#[test]
fn interval_posterior_refuses_unresolved_family_crossing() {
    let face = [
        ExactInterval::new(q(0, 1), q(3, 4)).unwrap(),
        ExactInterval::new(q(1, 4), Rat::one()).unwrap(),
    ];
    assert!(matches!(
        super::sampling::select_class(&face, &q(1, 2)),
        Err(SamplingError::UnresolvedFibre { .. })
    ));

    let population = Population::new(vec![
        Box::new(Fixed::new(vec![Rat::one(), Rat::zero()], 1)),
        Box::new(Fixed::new(vec![Rat::zero(), Rat::one()], 2)),
    ])
    .unwrap();
    assert!(matches!(
        population.select_family(&q(2, 3)),
        Err(FamilyReleaseError::Sampling(
            SamplingError::UnresolvedFibre { .. }
        ))
    ));
}

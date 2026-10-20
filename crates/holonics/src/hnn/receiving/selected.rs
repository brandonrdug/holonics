//! Versioned receiving-law selection for paired coarse-grain and retained-fibre reads.
//!
//! This module selects how the same receiving operands are scored. It does not publish an epoch,
//! deposit a return, alter a clock, or change the source word. In particular, full-fibre scoring
//! preserves each exact `ReceivingRead` and the producing population at that chronological cut.

use super::{ReceivingRead, ReceivingStep, RetainedFibreReceiver, score_at};
use crate::compression::landmark::context::LandmarkFace;
use crate::hnn::HnnError;
use crate::hnn::ratio::Face;
use crate::hnn::ratio::Faces;
use crate::hnn::receiving::cells::ScoredFaceReading;
use crate::hnn::receiving::cells::diagnostic::RetainedScoredFaceReading;
use crate::ratio::Rat;
use crate::ratio::algebraic::{ExactInterval, log2_enclosure_at};
use crate::receiver::population::PortPopulation;
use crate::receiver::population::port::ComparedFace;
use num_traits::{One, Zero};
use std::fmt;
use std::str::FromStr;

/// Stable identity of a receiving scorer. The `V1` suffix is part of the serialized identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum ReceivingLaw {
    /// The established grain-face scorer (`receiving::score_at`).
    CoarseGrainV1,
    /// The exact retained-fibre receiver over the same wave and tree operands.
    RetainedFibreV1,
}

impl ReceivingLaw {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CoarseGrainV1 => "coarse-grain-v1",
            Self::RetainedFibreV1 => "retained-fibre-v1",
        }
    }

    pub fn parse(identity: &str) -> Result<Self, ParseReceivingLawError> {
        identity.parse()
    }
}

impl fmt::Display for ReceivingLaw {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

impl FromStr for ReceivingLaw {
    type Err = ParseReceivingLawError;

    fn from_str(identity: &str) -> Result<Self, Self::Err> {
        match identity {
            "coarse-grain-v1" => Ok(Self::CoarseGrainV1),
            "retained-fibre-v1" => Ok(Self::RetainedFibreV1),
            _ => Err(ParseReceivingLawError),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ParseReceivingLawError;

impl fmt::Display for ParseReceivingLawError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("unknown versioned receiving-law identity")
    }
}

impl std::error::Error for ParseReceivingLawError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SelectedFaceReading {
    Coarse(ScoredFaceReading),
    Retained(RetainedScoredFaceReading),
}

impl SelectedFaceReading {
    /// An explicitly coarse diagnostic view of the producing operands.
    ///
    /// For a retained read this re-reads the exact saved `ReceivingRead` at its declared grain;
    /// it does not replace or relabel the retained-fibre score.
    pub fn coarse_operands(&self) -> Result<ScoredFaceReading, HnnError> {
        match self {
            Self::Coarse(reading) => Ok(reading.clone()),
            Self::Retained(reading) => Ok(ScoredFaceReading {
                population: reading.population.clone(),
                tree_probabilities: reading.tree_probabilities.clone(),
                combined: Face::of_read(&reading.read, reading.receiver.source_grain())?,
            }),
        }
    }
}

/// Chronological scores and immutable producing-cut reads from one selected law.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SelectedScored {
    pub law: ReceivingLaw,
    pub producing_population: PortPopulation,
    pub final_population: PortPopulation,
    pub model: Vec<ExactInterval>,
    pub tree: Vec<ExactInterval>,
    pub steps: Vec<ReceivingStep>,
    pub face_readings: Vec<SelectedFaceReading>,
}

/// Score the actual wave operands in `Faces.logits` against the supplied tree faces.
///
/// All phase shapes and targets are admitted before either scorer starts. The coarse branch is a
/// literal call to the existing `score_at`; the retained branch builds the same combined read
/// used by the continuation receiver and advances only a local population clone, one phase at a
/// time. The retained branch declares the existing full-fibre receiver at the common tree grain.
pub fn score_at_law(
    law: ReceivingLaw,
    population: &PortPopulation,
    ring: usize,
    combined: &Faces,
    trees: &[LandmarkFace],
    targets: &[usize],
    bits: u32,
) -> Result<SelectedScored, HnnError> {
    let owned_receiver = if law == ReceivingLaw::RetainedFibreV1 {
        let grain = trees
            .first()
            .map(|tree| tree.grain)
            .ok_or(HnnError::Unadmitted {
                reason: "retained-fibre scoring has at least one declared producing grain",
            })?;
        Some(RetainedFibreReceiver::declare(grain)?)
    } else {
        None
    };
    let receiver = owned_receiver.as_ref();
    preflight(law, combined, trees, targets, bits, receiver)?;
    match law {
        ReceivingLaw::CoarseGrainV1 => {
            let scored = score_at(population, ring, combined, trees, targets, bits)?;
            let mut final_population = population.clone();
            for step in &scored.steps {
                final_population
                    .receive(&step.faces())
                    .map_err(super::population_refusal)?;
            }
            Ok(SelectedScored {
                law,
                producing_population: population.clone(),
                final_population,
                model: scored.model,
                tree: scored.tree,
                steps: scored.steps,
                face_readings: scored
                    .face_readings
                    .into_iter()
                    .map(SelectedFaceReading::Coarse)
                    .collect(),
            })
        }
        ReceivingLaw::RetainedFibreV1 => {
            let receiver = receiver.expect("preflight requires the retained receiver");
            score_retained(population, ring, combined, trees, targets, bits, receiver)
        }
    }
}

fn preflight(
    law: ReceivingLaw,
    combined: &Faces,
    trees: &[LandmarkFace],
    targets: &[usize],
    bits: u32,
    receiver: Option<&RetainedFibreReceiver>,
) -> Result<(), HnnError> {
    if combined.faces.len() != trees.len()
        || combined.logits.len() != trees.len()
        || targets.len() != trees.len()
    {
        return Err(HnnError::Shape {
            what: "one wave, combined face, tree face and target per receiving phase",
            expected: trees.len(),
            found: targets
                .len()
                .min(combined.faces.len())
                .min(combined.logits.len()),
        });
    }
    if bits == 0 {
        return Err(HnnError::Unadmitted {
            reason: "a selected receiving score has positive reading precision",
        });
    }
    if law == ReceivingLaw::RetainedFibreV1 && receiver.is_none() {
        return Err(HnnError::Unadmitted {
            reason: "retained-fibre scoring has its declared continuation receiver",
        });
    }
    let expected_grain = receiver.map(RetainedFibreReceiver::source_grain);
    for ((face, wave), (tree, target)) in combined
        .faces
        .iter()
        .zip(&combined.logits)
        .zip(trees.iter().zip(targets))
    {
        let classes = tree.probabilities.len();
        if classes == 0
            || tree.exponents.len() != classes
            || wave.len() != classes.saturating_mul(2)
            || face.grain() != tree.grain
        {
            return Err(HnnError::Shape {
                what: "a receiving phase has matching tree, wave and combined-face grain",
                expected: classes.saturating_mul(2),
                found: wave.len(),
            });
        }
        if *target >= classes {
            return Err(HnnError::CellOutside {
                code: *target,
                alphabet: classes,
            });
        }
        if tree
            .probabilities
            .iter()
            .any(|probability| probability <= &Rat::zero())
            || tree.probabilities.iter().cloned().sum::<Rat>() != Rat::one()
        {
            return Err(HnnError::Unadmitted {
                reason: "a selected receiving tree face is a positive normalized partition",
            });
        }
        if law == ReceivingLaw::RetainedFibreV1 && expected_grain != Some(tree.grain) {
            return Err(HnnError::Unadmitted {
                reason: "the retained receiver grain matches every producing tree face",
            });
        }
    }
    Ok(())
}

fn score_retained(
    population: &PortPopulation,
    ring: usize,
    combined: &Faces,
    trees: &[LandmarkFace],
    targets: &[usize],
    bits: u32,
    receiver: &RetainedFibreReceiver,
) -> Result<SelectedScored, HnnError> {
    score_retained_producing(
        population, ring, combined, trees, targets, bits, receiver, false,
    )
    .map(|p| p.0)
}

fn score_retained_producing(
    population: &PortPopulation,
    ring: usize,
    combined: &Faces,
    trees: &[LandmarkFace],
    targets: &[usize],
    bits: u32,
    receiver: &RetainedFibreReceiver,
    retain_observations: bool,
) -> Result<
    (
        SelectedScored,
        Vec<super::single_grain::ProducedFibreObservation>,
    ),
    HnnError,
> {
    #[cfg(test)]
    super::reuse_work::score();
    let mut observations = Vec::with_capacity(if retain_observations {
        targets.len()
    } else {
        0
    });
    let mut local = population.clone();
    let mut scored = SelectedScored {
        law: ReceivingLaw::RetainedFibreV1,
        producing_population: population.clone(),
        final_population: population.clone(),
        model: Vec::with_capacity(targets.len()),
        tree: Vec::with_capacity(targets.len()),
        steps: Vec::with_capacity(targets.len()),
        face_readings: Vec::with_capacity(targets.len()),
    };
    for ((wave, tree), &target) in combined.logits.iter().zip(trees).zip(targets) {
        let read = ReceivingRead::combined(wave.clone(), tree, tree.grain)?;
        let reading = RetainedScoredFaceReading {
            population: local.clone(),
            tree_probabilities: tree.probabilities.clone(),
            read,
            receiver: receiver.clone(),
        };
        let observation = if retain_observations {
            Some(super::single_grain::ProducedFibreObservation::at(
                receiver,
                &reading.read,
                bits,
            )?)
        } else {
            None
        };
        // The uncached reference retains its original allocation/lifetime behavior: no
        // producer cache is built merely to discard it. Both arms share the exact normalizer.
        let combined_mass = match &observation {
            Some(observation) => observation.masses().get(target).cloned(),
            None => reading.combined_masses_at(bits)?.get(target).cloned(),
        }
        .ok_or(HnnError::CellOutside {
            code: target,
            alphabet: tree.probabilities.len(),
        })?;
        let tree_mass = tree.probabilities[target].clone();
        let log = log2_enclosure_at(&tree_mass, bits)?;
        scored
            .tree
            .push(ExactInterval::new(-log.upper, -log.lower)?);
        let step = ReceivingStep {
            ring,
            tree: tree_mass,
            combined: combined_mass,
        };
        scored.model.push(
            local
                .code_of_at(&step.faces(), bits)
                .map_err(super::population_refusal)?,
        );
        local
            .receive(&step.faces())
            .map_err(super::population_refusal)?;
        scored.steps.push(step);
        if let Some(observation) = observation {
            observations.push(observation);
        }
        scored
            .face_readings
            .push(SelectedFaceReading::Retained(reading));
    }
    scored.final_population = local;
    Ok((scored, observations))
}

/// Private actual producer: no caller can attach enclosures to a publicly constructed score.
/// All identities are kept for this one bounded computation, then dropped before publication.
pub(super) struct ProducedRetainedSection {
    population: PortPopulation,
    ring: usize,
    combined: Faces,
    trees: Vec<LandmarkFace>,
    targets: Vec<usize>,
    bits: u32,
    scored: SelectedScored,
    observations: Vec<super::single_grain::ProducedFibreObservation>,
}
impl ProducedRetainedSection {
    pub(super) fn at(
        population: &PortPopulation,
        ring: usize,
        combined: &Faces,
        trees: &[LandmarkFace],
        targets: &[usize],
        bits: u32,
    ) -> Result<Self, HnnError> {
        let receiver = RetainedFibreReceiver::declare(
            trees
                .first()
                .ok_or(HnnError::Unadmitted {
                    reason: "a producing section has a tree grain",
                })?
                .grain,
        )?;
        preflight(
            ReceivingLaw::RetainedFibreV1,
            combined,
            trees,
            targets,
            bits,
            Some(&receiver),
        )?;
        let (scored, observations) = score_retained_producing(
            population, ring, combined, trees, targets, bits, &receiver, true,
        )?;
        Ok(Self {
            population: population.clone(),
            ring,
            combined: combined.clone(),
            trees: trees.to_vec(),
            targets: targets.to_vec(),
            bits,
            scored,
            observations,
        })
    }
    pub(super) fn validate(
        &self,
        population: &PortPopulation,
        ring: usize,
        combined: &Faces,
        trees: &[LandmarkFace],
        targets: &[usize],
    ) -> Result<(), HnnError> {
        if &self.population != population
            || self.ring != ring
            || &self.combined != combined
            || self.trees != trees
            || self.targets != targets
            || self.scored.law != ReceivingLaw::RetainedFibreV1
        {
            return Err(HnnError::Unadmitted {
                reason: "immutable section observation matches law/population/ring/source/tree/target order",
            });
        }
        Ok(())
    }
    pub(super) fn scored(&self) -> &SelectedScored {
        &self.scored
    }
    pub(super) fn observations_at(
        &self,
        bits: u32,
    ) -> Result<Vec<super::single_grain::ProducedFibreObservation>, HnnError> {
        self.observations
            .iter()
            .zip(&self.scored.face_readings)
            .map(|(o, r)| {
                let SelectedFaceReading::Retained(r) = r else {
                    return Err(HnnError::Unadmitted {
                        reason: "private retained producer has retained readings",
                    });
                };
                o.read_at(&r.receiver, &r.read, bits)
            })
            .collect()
    }
    pub(super) fn bits(&self) -> u32 {
        self.bits
    }
}

/// One selected-law score and return, owned by the actual native section operands.
/// Only combined positive weights/masses are reused; mixture p is read at EACH chronological population.
pub(crate) fn prepare_retained_section(
    population: &PortPopulation,
    ring: usize,
    combined: &Faces,
    trees: &[LandmarkFace],
    targets: &[usize],
    bits: u32,
) -> Result<(SelectedScored, super::RetainedSectionReturn), HnnError> {
    let producer = ProducedRetainedSection::at(population, ring, combined, trees, targets, bits)?;
    let returned = super::RetainedSectionReturn::at_produced(
        population, ring, combined, trees, targets, &producer,
    )?;
    Ok((producer.scored, returned))
}

/// The result of a correlated finite comparison of two whole selected sections.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SelectedComparedScoresAt {
    pub change: ExactInterval,
    pub before: SelectedScored,
    pub after: SelectedScored,
}

/// Compare two scored sections under one declared law and one frozen producing population.
///
/// The target vector identifies the chronological cells represented by the paired face readings.
/// Full-fibre comparison uses the correlated `PortPopulation::code_change_at` calculation;
/// coarse comparison uses the same machinery with its existing grain-face readings.
fn compare_scored_at_law(
    law: ReceivingLaw,
    before: &SelectedScored,
    after: &SelectedScored,
    targets: &[usize],
    bits: u32,
) -> Result<SelectedComparedScoresAt, HnnError> {
    if before.law != law || after.law != law {
        return Err(HnnError::Unadmitted {
            reason: "finite section comparison uses the same declared receiving law",
        });
    }
    if before.producing_population != after.producing_population
        || before.face_readings.len() != after.face_readings.len()
        || before.face_readings.len() != targets.len()
    {
        return Err(HnnError::Shape {
            what: "paired selected sections share a frozen population and phase shape",
            expected: before.face_readings.len(),
            found: after.face_readings.len().min(targets.len()),
        });
    }
    if bits == 0 {
        return Err(HnnError::Unadmitted {
            reason: "a selected finite section comparison has positive reading precision",
        });
    }
    let mut window = Vec::with_capacity(targets.len());
    for ((old, new), &target) in before
        .face_readings
        .iter()
        .zip(&after.face_readings)
        .zip(targets)
    {
        let row = match (law, old, new) {
            (
                ReceivingLaw::RetainedFibreV1,
                SelectedFaceReading::Retained(old),
                SelectedFaceReading::Retained(new),
            ) => full_section_row(old, new, target, bits)?,
            _ => {
                return Err(HnnError::Unadmitted {
                    reason: "selected section operands retain their declared receiving law",
                });
            }
        };
        window.push(row);
    }
    let change = before
        .producing_population
        .code_change_at(&window, bits)
        .map_err(super::population_refusal)?;
    Ok(SelectedComparedScoresAt {
        change,
        before: before.clone(),
        after: after.clone(),
    })
}

/// Score and compare two actual candidate inputs under one selected receiving law.
///
/// Every face mass is re-read from the supplied `Faces.logits` and tree operands. No caller can
/// supply precomputed mass intervals or borrow a prior candidate's read as this candidate's.
#[allow(clippy::too_many_arguments)]
pub fn compare_scores_at_law(
    law: ReceivingLaw,
    population: &PortPopulation,
    ring: usize,
    before: &Faces,
    before_trees: &[LandmarkFace],
    after: &Faces,
    after_trees: &[LandmarkFace],
    targets: &[usize],
    bits: u32,
) -> Result<SelectedComparedScoresAt, HnnError> {
    let receiver = if law == ReceivingLaw::RetainedFibreV1 {
        let grain = before_trees
            .first()
            .map(|tree| tree.grain)
            .ok_or(HnnError::Unadmitted {
                reason: "a retained-fibre comparison has at least one declared producing grain",
            })?;
        Some(RetainedFibreReceiver::declare(grain)?)
    } else {
        None
    };
    // Both candidate inputs pass shape/grain admission before either candidate is scored.
    preflight(law, before, before_trees, targets, bits, receiver.as_ref())?;
    preflight(law, after, after_trees, targets, bits, receiver.as_ref())?;
    if law == ReceivingLaw::CoarseGrainV1 {
        let compared = super::compare_scores_at(
            population,
            ring,
            before,
            before_trees,
            after,
            after_trees,
            targets,
            bits,
        )?;
        return Ok(SelectedComparedScoresAt {
            change: compared.change,
            before: select_coarse(population, compared.before)?,
            after: select_coarse(population, compared.after)?,
        });
    }
    let before_scored = score_at_law(law, population, ring, before, before_trees, targets, bits)?;
    let after_scored = score_at_law(law, population, ring, after, after_trees, targets, bits)?;
    compare_scored_at_law(law, &before_scored, &after_scored, targets, bits)
}

fn select_coarse(
    population: &PortPopulation,
    scored: super::Scored,
) -> Result<SelectedScored, HnnError> {
    let mut final_population = population.clone();
    for step in &scored.steps {
        final_population
            .receive(&step.faces())
            .map_err(super::population_refusal)?;
    }
    Ok(SelectedScored {
        law: ReceivingLaw::CoarseGrainV1,
        producing_population: population.clone(),
        final_population,
        model: scored.model,
        tree: scored.tree,
        steps: scored.steps,
        face_readings: scored
            .face_readings
            .into_iter()
            .map(SelectedFaceReading::Coarse)
            .collect(),
    })
}

fn full_section_row(
    old: &RetainedScoredFaceReading,
    new: &RetainedScoredFaceReading,
    target: usize,
    bits: u32,
) -> Result<Vec<ComparedFace>, HnnError> {
    if old.receiver != new.receiver
        || old.tree_probabilities.len() != new.tree_probabilities.len()
        || old.read.cells.len() != old.tree_probabilities.len()
        || new.read.cells.len() != new.tree_probabilities.len()
        || old.read.logits.len() != old.tree_probabilities.len().saturating_mul(2)
        || new.read.logits.len() != new.tree_probabilities.len().saturating_mul(2)
        || target >= old.tree_probabilities.len()
        || !normalized_positive(&old.tree_probabilities)
        || !normalized_positive(&new.tree_probabilities)
    {
        return Err(HnnError::Shape {
            what: "paired full-fibre section operands have matched valid class shapes",
            expected: old.tree_probabilities.len(),
            found: new.tree_probabilities.len(),
        });
    }
    let old_mass = old
        .combined_masses_at(bits)?
        .get(target)
        .cloned()
        .ok_or(HnnError::Shape {
            what: "full-fibre target mass exists",
            expected: old.tree_probabilities.len(),
            found: 0,
        })?;
    let new_mass = new
        .combined_masses_at(bits)?
        .get(target)
        .cloned()
        .ok_or(HnnError::Shape {
            what: "full-fibre target mass exists",
            expected: new.tree_probabilities.len(),
            found: 0,
        })?;
    let old_tree = ExactInterval::point(old.tree_probabilities[target].clone());
    let new_tree = ExactInterval::point(new.tree_probabilities[target].clone());
    let tree = if old.tree_probabilities[target] == new.tree_probabilities[target] {
        ComparedFace::Shared(old_tree)
    } else {
        ComparedFace::Changed {
            before: old_tree,
            after: new_tree,
        }
    };
    let combined = if same_normalized_full_fibre_expression(old, new) {
        ComparedFace::Shared(old_mass)
    } else {
        ComparedFace::Changed {
            before: old_mass,
            after: new_mass,
        }
    };
    Ok(vec![tree, combined])
}

/// Establish exact identity of normalized full-fibre masses from their rational operands.
/// A common real-logit shift multiplies every unnormalized class weight by the same positive
/// factor; imaginary phase coordinates do not enter these masses. This predicate never inspects
/// coarse cells or interval endpoint equality. The caller has already forced both canonical reads
/// through `RetainedFibreReceiver::masses_at`.
fn same_normalized_full_fibre_expression(
    old: &RetainedScoredFaceReading,
    new: &RetainedScoredFaceReading,
) -> bool {
    if old.receiver != new.receiver
        || old.tree_probabilities != new.tree_probabilities
        || old.read.logits.len() != new.read.logits.len()
        || old.read.logits.len() != old.tree_probabilities.len().saturating_mul(2)
    {
        return false;
    }
    let mut common_shift: Option<Rat> = None;
    for class in 0..old.tree_probabilities.len() {
        let delta = &new.read.logits[2 * class] - &old.read.logits[2 * class];
        match &common_shift {
            Some(expected) if expected != &delta => return false,
            None => common_shift = Some(delta),
            _ => {}
        }
    }
    true
}

fn normalized_positive(probabilities: &[Rat]) -> bool {
    !probabilities.is_empty()
        && probabilities
            .iter()
            .all(|probability| probability > &Rat::zero())
        && probabilities.iter().cloned().sum::<Rat>() == Rat::one()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::receiving::receiving_population;
    use crate::ratio::{integer, rat};
    use num_bigint::BigInt;
    use num_traits::Signed;

    fn tree_half(grain: u64) -> LandmarkFace {
        LandmarkFace {
            grain,
            probabilities: vec![rat(1, 2), rat(1, 2)],
            exponents: vec![BigInt::from(-4), BigInt::from(-4)],
        }
    }

    fn faces(waves: &[Vec<Rat>], trees: &[LandmarkFace]) -> Faces {
        let reads: Vec<_> = waves
            .iter()
            .zip(trees)
            .map(|(wave, tree)| ReceivingRead::combined(wave.clone(), tree, tree.grain).unwrap())
            .collect();
        Faces::of_reads(&reads, trees[0].grain).unwrap()
    }

    fn zero_wave() -> Vec<Rat> {
        vec![integer(0), integer(0), integer(0), integer(0)]
    }

    #[test]
    fn versioned_law_identity_is_stable_and_rejects_unknown_tags() {
        for law in [ReceivingLaw::CoarseGrainV1, ReceivingLaw::RetainedFibreV1] {
            assert_eq!(ReceivingLaw::parse(law.as_str()).unwrap(), law);
            assert_eq!(law.to_string(), law.as_str());
        }
        assert_eq!(ReceivingLaw::CoarseGrainV1.as_str(), "coarse-grain-v1");
        assert!(ReceivingLaw::parse("retained-fibre").is_err());
    }

    #[test]
    fn retained_zero_wave_matches_tree_and_keeps_equal_family_evidence() {
        let tree = tree_half(4);
        let input = faces(&[zero_wave()], &[tree.clone()]);
        let population = receiving_population();
        let scored = score_at_law(
            ReceivingLaw::RetainedFibreV1,
            &population,
            0,
            &input,
            &[tree.clone()],
            &[0],
            48,
        )
        .unwrap();
        let SelectedFaceReading::Retained(reading) = &scored.face_readings[0] else {
            panic!("retained law must retain the full-fibre reading");
        };
        assert_eq!(
            reading.combined_masses_at(48).unwrap()[0],
            ExactInterval::point(rat(1, 2))
        );
        assert_eq!(scored.steps[0].combined, ExactInterval::point(rat(1, 2)));
        assert_eq!(scored.steps[0].tree, rat(1, 2));
        assert_eq!(scored.producing_population, population);
    }

    #[test]
    fn coarse_law_is_literal_existing_score_at_parity() {
        let tree = tree_half(4);
        let input = faces(
            &[vec![rat(1, 8), integer(0), rat(-1, 8), integer(0)]],
            &[tree.clone()],
        );
        let population = receiving_population();
        let legacy = score_at(&population, 2, &input, &[tree.clone()], &[1], 64).unwrap();
        let selected = score_at_law(
            ReceivingLaw::CoarseGrainV1,
            &population,
            2,
            &input,
            &[tree.clone()],
            &[1],
            64,
        )
        .unwrap();
        assert_eq!(selected.model, legacy.model);
        assert_eq!(selected.tree, legacy.tree);
        assert_eq!(selected.steps, legacy.steps);
        assert_eq!(
            selected.final_population,
            population_after(&population, &legacy.steps)
        );

        let alternate = faces(&[zero_wave()], &[tree.clone()]);
        let legacy_comparison = super::super::compare_scores_at(
            &population,
            2,
            &input,
            &[tree.clone()],
            &alternate,
            &[tree.clone()],
            &[1],
            64,
        )
        .unwrap();
        let selected_comparison = compare_scores_at_law(
            ReceivingLaw::CoarseGrainV1,
            &population,
            2,
            &input,
            &[tree.clone()],
            &alternate,
            &[tree.clone()],
            &[1],
            64,
        )
        .unwrap();
        assert_eq!(selected_comparison.change, legacy_comparison.change);
        assert_eq!(
            selected_comparison.before.model,
            legacy_comparison.before.model
        );
        assert_eq!(
            selected_comparison.after.model,
            legacy_comparison.after.model
        );
    }

    fn population_after(population: &PortPopulation, steps: &[ReceivingStep]) -> PortPopulation {
        let mut result = population.clone();
        for step in steps {
            result.receive(&step.faces()).unwrap();
        }
        result
    }

    #[test]
    fn retained_common_real_shift_preserves_normalized_class_masses() {
        let tree = tree_half(4);
        let zero = faces(&[zero_wave()], &[tree.clone()]);
        let shifted = faces(
            &[vec![integer(3), integer(0), integer(3), integer(0)]],
            &[tree.clone()],
        );
        let population = receiving_population();
        let a = score_at_law(
            ReceivingLaw::RetainedFibreV1,
            &population,
            0,
            &zero,
            &[tree.clone()],
            &[0],
            48,
        )
        .unwrap();
        let b = score_at_law(
            ReceivingLaw::RetainedFibreV1,
            &population,
            0,
            &shifted,
            &[tree],
            &[0],
            48,
        )
        .unwrap();
        let SelectedFaceReading::Retained(a_read) = &a.face_readings[0] else {
            panic!()
        };
        let SelectedFaceReading::Retained(b_read) = &b.face_readings[0] else {
            panic!()
        };
        assert_eq!(
            a_read.combined_masses_at(48).unwrap(),
            b_read.combined_masses_at(48).unwrap()
        );
    }

    #[test]
    fn full_fibre_comparison_cancels_exact_rational_common_real_shift() {
        let tree = tree_half(4);
        let before = faces(&[zero_wave()], &[tree.clone()]);
        let after = faces(
            &[vec![rat(1, 8), rat(1, 4), rat(1, 8), rat(-1, 2)]],
            &[tree.clone()],
        );
        let comparison = compare_scores_at_law(
            ReceivingLaw::RetainedFibreV1,
            &receiving_population(),
            0,
            &before,
            &[tree.clone()],
            &after,
            &[tree],
            &[0],
            64,
        )
        .unwrap();
        assert_eq!(comparison.change, ExactInterval::point(integer(0)));
    }

    #[test]
    fn full_fibre_reads_keep_chronological_producing_populations() {
        let tree = tree_half(4);
        let trees = vec![tree.clone(), tree];
        let input = faces(&[zero_wave(), zero_wave()], &trees);
        let population = receiving_population();
        let scored = score_at_law(
            ReceivingLaw::RetainedFibreV1,
            &population,
            0,
            &input,
            &trees,
            &[0, 1],
            48,
        )
        .unwrap();
        let SelectedFaceReading::Retained(first) = &scored.face_readings[0] else {
            panic!()
        };
        let SelectedFaceReading::Retained(second) = &scored.face_readings[1] else {
            panic!()
        };
        assert_eq!(first.population, population);
        assert_eq!(
            second.population,
            population_after(&population, &scored.steps[..1])
        );
        assert_eq!(
            scored.final_population,
            population_after(&population, &scored.steps)
        );
    }

    #[test]
    fn complete_section_comparison_does_not_let_one_cell_gain_mask_a_loss() {
        let tree = tree_half(4);
        let trees = vec![tree.clone(), tree];
        let before = faces(&[zero_wave(), zero_wave()], &trees);
        let after = faces(
            &[
                vec![integer(1), integer(0), integer(-1), integer(0)],
                vec![integer(-1), integer(0), integer(1), integer(0)],
            ],
            &trees,
        );
        let population = receiving_population();
        let comparison = compare_scores_at_law(
            ReceivingLaw::RetainedFibreV1,
            &population,
            0,
            &before,
            &trees,
            &after,
            &trees,
            &[0, 0],
            96,
        )
        .unwrap();
        assert!(comparison.change.lower.is_positive());
        assert_eq!(comparison.before.law, ReceivingLaw::RetainedFibreV1);
        assert_eq!(comparison.after.law, ReceivingLaw::RetainedFibreV1);
    }

    #[test]
    fn full_section_gain_allows_candidate_chronology_to_change_later_population() {
        let tree = tree_half(4);
        let trees = vec![tree.clone(), tree];
        let before = faces(&[zero_wave(), zero_wave()], &trees);
        let after = faces(
            &[
                vec![integer(1), integer(0), integer(-1), integer(0)],
                vec![integer(1), integer(0), integer(-1), integer(0)],
            ],
            &trees,
        );
        let population = receiving_population();
        let comparison = compare_scores_at_law(
            ReceivingLaw::RetainedFibreV1,
            &population,
            0,
            &before,
            &trees,
            &after,
            &trees,
            &[0, 0],
            96,
        )
        .unwrap();
        let SelectedFaceReading::Retained(before_second) = &comparison.before.face_readings[1]
        else {
            panic!()
        };
        let SelectedFaceReading::Retained(after_second) = &comparison.after.face_readings[1] else {
            panic!()
        };
        assert_ne!(before_second.population, after_second.population);
        assert!(comparison.change.upper.is_negative());
    }

    #[test]
    fn invalid_later_phase_refuses_before_scoring_and_inputs_stay_immutable() {
        let tree = tree_half(4);
        let trees = vec![tree.clone(), tree.clone()];
        let good = faces(&[zero_wave(), zero_wave()], &trees);
        let mut bad = good.clone();
        bad.logits[1] = vec![integer(0)];
        let before_bad = bad.clone();
        let population = receiving_population();
        let before_population = population.clone();
        assert!(
            score_at_law(
                ReceivingLaw::RetainedFibreV1,
                &population,
                0,
                &bad,
                &trees,
                &[0, 0],
                48,
            )
            .is_err()
        );
        assert!(
            compare_scores_at_law(
                ReceivingLaw::RetainedFibreV1,
                &population,
                0,
                &good,
                &trees,
                &bad,
                &trees,
                &[0, 0],
                48,
            )
            .is_err()
        );
        assert_eq!(bad, before_bad);
        assert_eq!(population, before_population);
    }

    #[test]
    fn retained_score_exposes_only_an_explicit_coarse_diagnostic_view() {
        let tree = tree_half(4);
        let input = faces(&[zero_wave()], &[tree.clone()]);
        let scored = score_at_law(
            ReceivingLaw::RetainedFibreV1,
            &receiving_population(),
            0,
            &input,
            &[tree],
            &[0],
            48,
        )
        .unwrap();
        let coarse_view = scored.face_readings[0].coarse_operands().unwrap();
        assert_eq!(coarse_view.combined.grain(), 4);
        assert_eq!(coarse_view.tree_probabilities, vec![rat(1, 2), rat(1, 2)]);
    }
}

//! Exact comparison and two absolute score passes over the same receiving operands.
//!
//! The comparison first reads all target masses and the population's coupled code change,
//! exactly as the epoch comparison does. Each absolute score then starts from its own clone of
//! that same population. Target masses already read here are reused; neither a caller-supplied
//! enclosure nor a retained cache can enter this operation. Produced phase excess remains the
//! ratio owner's separate term; sharing a class mass does not identify the produced phases.

use super::*;
use crate::receiver::population::port::ComparedFace;

/// The class-code part of one comparison demand, with the complete absolute score receipts.
/// `change` is the correlated code-change enclosure, not subtraction of the absolute endpoints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComparedScoresAt {
    pub change: ExactInterval,
    pub before: Scored,
    pub after: Scored,
}

/// Read the coupled comparison before either absolute score, reusing only exact native readings.
/// Each absolute pass receives its own earlier targets in order. No population is changed here.
/// `bits` belongs to the caller's existing demand ladder; no demand is added or skipped.
#[allow(clippy::too_many_arguments)]
pub fn compare_scores_at(
    population: &PortPopulation,
    ring: usize,
    before: &Faces,
    before_trees: &[LandmarkFace],
    after: &Faces,
    after_trees: &[LandmarkFace],
    targets: &[usize],
    bits: u32,
) -> Result<ComparedScoresAt, HnnError> {
    let mut window = Vec::with_capacity(targets.len());
    let mut before_masses = Vec::with_capacity(targets.len());
    let mut after_masses = Vec::with_capacity(targets.len());
    for ((((before, after), before_tree), after_tree), &target) in before
        .faces
        .iter()
        .zip(&after.faces)
        .zip(before_trees)
        .zip(after_trees)
        .zip(targets)
    {
        let before_mass = face_enclosure_at(before, target, bits)?;
        // This is exactly the existing epoch predicate. Fibres and produced phases do not
        // enter a class mass; every class's carry and phase, and the grain, do enter it.
        let same_class_face = before.grain() == after.grain()
            && before.cells().len() == after.cells().len()
            && before
                .cells()
                .iter()
                .zip(after.cells())
                .all(|(a, b)| a.carry == b.carry && a.phase == b.phase);
        let after_mass = if same_class_face {
            before_mass.clone()
        } else {
            face_enclosure_at(after, target, bits)?
        };
        let wave = if same_class_face {
            ComparedFace::Shared(before_mass.clone())
        } else {
            ComparedFace::Changed {
                before: before_mass.clone(),
                after: after_mass.clone(),
            }
        };
        let target_mass = |tree: &LandmarkFace| {
            tree.probabilities
                .get(target)
                .cloned()
                .ok_or(HnnError::CellOutside {
                    code: target,
                    alphabet: tree.probabilities.len(),
                })
        };
        let before_tree_mass = target_mass(before_tree)?;
        let after_tree_mass = target_mass(after_tree)?;
        let tree = if before_tree_mass == after_tree_mass {
            ComparedFace::Shared(ExactInterval::point(before_tree_mass))
        } else {
            ComparedFace::Changed {
                before: ExactInterval::point(before_tree_mass),
                after: ExactInterval::point(after_tree_mass),
            }
        };
        window.push(vec![tree, wave]);
        before_masses.push(before_mass);
        after_masses.push(after_mass);
    }
    let change = population
        .code_change_at(&window, bits)
        .map_err(population_refusal)?;
    // Per-phase, per-invocation only. Equality is literal rational equality at these same bits;
    // a changed tree mass always follows the native logarithm path.
    let mut tree_codes: Vec<Option<(Rat, ExactInterval)>> = vec![None; targets.len()];
    let before = score_at_with(
        population,
        ring,
        before,
        before_trees,
        targets,
        bits,
        |phase, face, target| match before_masses.get(phase) {
            Some(mass) => Ok(mass.clone()),
            None => face_enclosure_at(face, target, bits),
        },
        |phase, probability| {
            let code = tree_code_at(probability, bits)?;
            tree_codes[phase] = Some((probability.clone(), code.clone()));
            Ok(code)
        },
    )?;
    let after = score_at_with(
        population,
        ring,
        after,
        after_trees,
        targets,
        bits,
        |phase, face, target| match after_masses.get(phase) {
            Some(mass) => Ok(mass.clone()),
            None => face_enclosure_at(face, target, bits),
        },
        |phase, probability| match &tree_codes[phase] {
            Some((old_probability, code)) if old_probability == probability => Ok(code.clone()),
            _ => tree_code_at(probability, bits),
        },
    )?;
    Ok(ComparedScoresAt {
        change,
        before,
        after,
    })
}

#[cfg(test)]
mod tests;

//! Exterior diagnosis of an already completed release. The target never enters a native draw.
//! A sampled class, its probability, a modal class and a heard reference are separate readings.
use super::*;
use holonics::hnn::receiving::cells::{CellDecision, ScoredFaceReading};
use holonics::hnn::reference::observed::ObservedEpochCellReceipt;
use holonics::ratio::algebraic::ExactInterval;

fn masses_text(masses: &[ExactInterval]) -> String {
    masses
        .iter()
        .enumerate()
        .map(|(class, q)| format!("{class}:[{},{}]", q.lower, q.upper))
        .collect::<Vec<_>>()
        .join(";")
}

/// One plus the number of classes strictly more probable. Bounds retain unresolved ordering
/// and exact ties; no midpoint ordering or low-index tie break is passed off as a mode.
fn rank_bounds(masses: &[ExactInterval], target: usize) -> Option<(usize, usize)> {
    let q = masses.get(target)?;
    let definitely = masses
        .iter()
        .enumerate()
        .filter(|(i, p)| *i != target && p.lower > q.upper)
        .count();
    let possibly = masses
        .iter()
        .enumerate()
        .filter(|(i, p)| *i != target && p.upper > q.lower)
        .count();
    Some((1 + definitely, 1 + possibly))
}

fn unique_mode(masses: &[ExactInterval]) -> Option<usize> {
    masses.iter().enumerate().find_map(|(i, q)| {
        masses
            .iter()
            .enumerate()
            .all(|(j, p)| i == j || q.lower > p.upper)
            .then_some(i)
    })
}

fn decision_kind(decision: &CellDecision) -> &'static str {
    use holonics::receiver::release::ReleaseReturn;
    match decision.release {
        ReleaseReturn::Released { .. } => "committed",
        ReleaseReturn::Drawn(_) => "drawn",
        ReleaseReturn::Hold => "held",
        ReleaseReturn::Unresolved(_) => "unresolved",
        ReleaseReturn::Widen { .. } => "widen",
        ReleaseReturn::Ask { .. } => "ask",
        ReleaseReturn::NoContinuationBridges { .. } => "no_continuation_bridges",
    }
}

fn divergence(generated: &[usize], target: &[usize]) -> Option<usize> {
    generated
        .iter()
        .zip(target)
        .position(|(h, t)| h != t)
        .or_else(|| (generated.len() != target.len()).then_some(generated.len().min(target.len())))
}

fn correspondence(sample: &CellDecision, heard: &ScoredFaceReading) -> Result<(bool, bool)> {
    let same_operands = sample.scored_face.as_ref() == Some(heard);
    let same_enclosures = sample.face == heard.masses_at(sample.bits)?;
    Ok((same_operands, same_enclosures))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn report(
    section: usize,
    source_cut: usize,
    target: &[usize],
    released: &Released,
    decisions: &[CellDecision],
    heard_tail: &[ObservedEpochCellReceipt],
    target_was_heard: bool,
    epoch: (usize, usize, u64),
    emit: &mut dyn FnMut(String),
) -> Result<()> {
    // Called only AFTER release_fork_accounted returns. This target lookup cannot affect its
    // population, key stream, draw extent, entropy/end/held stop or emitted classes.
    let first = divergence(&released.classes, target);
    emit(format!(
        "observed_release_diagnosis section={section} source_cut={source_cut} epoch_start={} epoch_end={} comparison_commit={} generated_cells={} reference_cells={} first_divergence={first:?} generated_at_divergence={:?} reference_at_divergence={:?} unemitted_reference_cells={} reference_context=generated_prefix reference_was_heard={target_was_heard} stop={:?} maximum={} scientific_status=inspected_diagnostic",
        epoch.0,
        epoch.1,
        epoch.2,
        released.classes.len(),
        target.len(),
        first.and_then(|i| released.classes.get(i)),
        first.and_then(|i| target.get(i)),
        target.len().saturating_sub(released.classes.len()),
        released.stop,
        released.maximum,
    ));
    for (index, decision) in decisions.iter().enumerate() {
        let reference = target.get(index).copied();
        let rank = reference.and_then(|t| rank_bounds(&decision.face, t));
        let mode = unique_mode(&decision.face);
        let target_mass = reference.and_then(|t| decision.face.get(t));
        let same_prefix = released.classes.get(..index) == target.get(..index);
        let heard = if target_was_heard && index < target.len() {
            heard_tail.get(index)
        } else {
            None
        };
        let equality = heard
            .and_then(|h| h.scored_face.as_ref()).map(|h| correspondence(decision, h))
            .transpose()?;
        let sampled_expression_matches = decision
            .scored_face
            .as_ref()
            .map(|reading| reading.masses_at(decision.bits).map(|p| p == decision.face))
            .transpose()?;
        emit(format!(
            "observed_release_face section={section} index={index} sampled_class={:?} emitted={} decision_return={:?} key_index={:?} demand_bits={} certified_unique_mode={mode:?} sampled_is_unique_mode={:?} reference_class={reference:?} reference_mass={target_mass:?} reference_rank_bounds={rank:?} same_heard_prefix={same_prefix} heard_available={} identical_scored_operands={:?} identical_mass_enclosures_at_draw_bits={:?} sampled_face_matches_operands={sampled_expression_matches:?} all_mass=[{}] scored_operands={:?}",
            decision.class(),
            index < released.classes.len(),
            decision_kind(decision),
            decision.key.as_ref().map(|(i, _)| i),
            decision.bits,
            mode.zip(decision.class()).map(|(m, c)| m == c),
            heard.is_some(),
            equality.map(|x| x.0),
            equality.map(|x| x.1),
            masses_text(&decision.face),
            decision.scored_face,
        ));
        if let Some(heard) = heard.and_then(|h| h.scored_face.as_ref()) {
            emit(format!(
                "observed_heard_face section={section} reference_index={index} delivered={} comparison_context_same_prefix={same_prefix} all_mass_at_draw_bits=[{}] scored_operands={:?}",
                source_cut + index + 1,
                masses_text(&heard.masses_at(decision.bits)?),
                heard,
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonics::ratio::{integer, rat};

    #[test]
    fn face_diagnosis_rank_retains_exact_ties_and_uncertain_order() {
        let p = |q| ExactInterval::point(q);
        assert_eq!(rank_bounds(&[p(rat(1, 2)), p(rat(1, 2))], 0), Some((1, 1)));
        let uncertain = ExactInterval::new(rat(1, 4), rat(3, 4)).unwrap();
        assert_eq!(
            rank_bounds(&[uncertain.clone(), uncertain], 0),
            Some((1, 2))
        );
        assert_eq!(
            rank_bounds(&[p(rat(99, 100)), p(rat(1, 100))], 1),
            Some((2, 2))
        );
        assert_eq!(rank_bounds(&[p(integer(1))], 2), None);
        assert_eq!(unique_mode(&[p(rat(1, 2)), p(rat(1, 2))]), None);
        assert_eq!(unique_mode(&[p(rat(99, 100)), p(rat(1, 100))]), Some(0));
        assert_eq!(unique_mode(&[]), None);
    }

    #[test]
    fn face_diagnosis_divergence_keeps_wrong_payload_and_missing_end_separate() {
        assert_eq!(divergence(&[3, 21, 3, 19], &[3, 17, 0, 0]), Some(1));
        assert_eq!(divergence(&[3, 17], &[3, 17, 0, 0]), Some(2));
        assert_eq!(divergence(&[3, 17, 0, 0], &[3, 17, 0, 0]), None);
        assert_eq!(divergence(&[], &[3, 17, 0, 0]), Some(0));
    }
}

//! One frozen producing comparison for finite candidate admission.
//!
//! Candidate reads are computational trials on the original opening, not continuations or
//! additional observations. The predecessor tree faces, population, target phase and section
//! remain fixed. In particular a target's newly deposited tree count cannot certify its own fit.
//!
//! [definition; agent-inferred, October 17] Candidate halvings have no authored trial budget.
//! Let `u` be each entry's material lattice unit, `k_m` its deposit-clock precision and `d_i`
//! its starting update. The first-reach split admits only fine-grid carried remainders in
//! their half cells. For the least nonnegative `h` such that
//! `2^(−h)|d_i| < u·2^(−k_m−1)` at every entry of every locus, no entry reaches a material
//! cell. The staged candidate then executes the identical wave and is admitted as neutral,
//! provided the executed wave reads only carriers the step scales. The receiving Gram Σwffᵀ,
//! the located prior's ridge and chart move, pass-1 scale statistics and the locus clock move
//! independently of h. A wave reading any such carrier fails this hypothesis and meets the
//! typed no-reach refusal. Finitely many exact entries give a finite least h*, not an authored
//! budget. An enclosure unresolved at the full demand ladder cannot progress at this candidate.
use super::*;
use crate::compression::landmark::context::LandmarkFace;
use crate::hnn::constitution::ComparisonCandidate;
use crate::hnn::ratio::TargetPhases;

/// The least h with 2^(-h)|d_i| < u_i 2^(-k_m-1) at every stepped entry.
/// The h=0 candidate supplies pass 1's lattice/clock and pass 2's exact update coordinates.
/// floor_log2 compares integer bit lengths and shifted integers; no floating arithmetic enters.
pub fn no_reach_halving(candidate: &ComparisonCandidate) -> Result<u32, HnnError> {
    no_reach_halving_of(candidate.starting_updates()?)
}

fn no_reach_halving_of(
    parts: &[crate::hnn::constitution::ComparisonStepEntries],
) -> Result<u32, HnnError> {
    let mut halving = 0;
    for part in parts {
        let threshold =
            &part.unit * crate::holon::deposition::dyadic(-i64::from(part.precision) - 1);
        for update in &part.updates {
            if update.is_zero() {
                continue;
            }
            let order = crate::ratio::disk::floor_log2(&(update.abs() / &threshold));
            let required =
                u32::try_from((order + 1).max(0)).map_err(|_| HnnError::CountOverflow)?;
            halving = halving.max(required);
        }
    }
    Ok(halving)
}

#[derive(Clone, Debug)]
pub struct FrozenComparison {
    producing: Constitution,
    ratio: PendingRatio,
    opening: WordOpening,
    targets: Vec<usize>,
    target_phases: TargetPhases,
    trees: Vec<LandmarkFace>,
    before: ExactInterval,
    wave: Faces,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComparisonReading {
    pub before: ExactInterval,
    pub after: ExactInterval,
    /// Identical wave expressions are a plateau, never a finite-decrease witness.
    pub unchanged: bool,
    pub strictly_improved: bool,
    pub objective_change: ExactInterval,
    pub reading_bits: u32,
    pub refinement_rounds: u32,
    pub retained_interval_members: usize,
}

impl ComparisonReading {
    pub fn objective_equal(&self) -> bool {
        self.objective_change.lower == integer(0) && self.objective_change.upper == integer(0)
    }
    pub fn needs_precision(&self) -> bool {
        !self.strictly_improved
            && !self.unchanged
            && !self.objective_equal()
            && self.objective_change.lower <= integer(0)
            && self.objective_change.upper >= integer(0)
    }
    pub fn unresolved_reason(&self) -> &'static str {
        if self.strictly_improved {
            "strictly improved"
        } else if self.unchanged {
            "identical executed wave"
        } else if self.objective_equal() {
            "exact frozen objective equality with changed executed wave"
        } else if self.objective_change.lower > integer(0) {
            "candidate objective is strictly worse"
        } else {
            "objective enclosures are not strictly separated"
        }
    }
}

/// One actually executed trial; published operand changes are separate from wave equality.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComparisonTrialReading {
    pub halvings: u32,
    pub smallest_step: Option<Rat>,
    pub changes: crate::hnn::constitution::ComparisonCandidateChanges,
    pub comparison: ComparisonReading,
    pub wave_changes: ComparisonWaveChanges,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComparisonWaveChanges {
    pub changed_coordinates: usize,
    pub largest_absolute_delta: Rat,
    pub largest_numerator_bits: u64,
    pub largest_denominator_bits: u64,
}

/// The finite acceptance evidence: strict decrease or exact executed-wave neutrality.
/// Neutral acceptance retains validated statistics/carry and separately lawful landmark updates;
/// it is never reported as strict improvement. Ordinary step readings remain proposal diagnostics.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteComparisonReceipt {
    pub comparison: ComparisonReading,
    pub attempts: u32,
    pub halvings: u32,
    pub frozen_operand_bits: u64,
    pub trials: Vec<ComparisonTrialReading>,
}

impl FrozenComparison {
    pub fn new(
        field: &Field,
        producing: &Constitution,
        ratio: &PendingRatio,
        opening: &WordOpening,
        target: &Encoded,
        wave: &Faces,
    ) -> Result<Self, HnnError> {
        field.admit(target)?;
        let targets: Vec<_> = target.classes_read().collect();
        let trees = ratio.tree_faces(producing, &targets)?;
        let target_phases = target_phases(field, ratio.anchor(), ratio.phases().ring(), target)?;
        let mut frozen = Self {
            producing: producing.clone(),
            ratio: ratio.clone(),
            opening: opening.clone(),
            targets,
            target_phases,
            trees,
            before: ExactInterval::point(Rat::zero()),
            wave: wave.clone(),
        };
        frozen.before = frozen.objective(wave)?;
        Ok(frozen)
    }

    /// Stored mathematical operands, excluding recomputable face caches and allocator overhead.
    pub fn bits(&self) -> u64 {
        let rat_bits = |x: &Rat| x.numer().bits() + x.denom().bits();
        self.producing.exact_bits()
            + self.ratio.bits()
            + opening_bits(&self.opening)
            + self
                .targets
                .iter()
                .map(|x| BigInt::from(*x).bits() + 1)
                .sum::<u64>()
            + self.target_phases.branch.bits()
            + self.target_phases.phases.iter().map(rat_bits).sum::<u64>()
            + self
                .trees
                .iter()
                .map(|t| {
                    64 + t.probabilities.iter().map(rat_bits).sum::<u64>()
                        + t.exponents.iter().map(BigInt::bits).sum::<u64>()
                })
                .sum::<u64>()
            + self.wave.logits.iter().flatten().map(rat_bits).sum::<u64>()
            + rat_bits(&self.before.lower)
            + rat_bits(&self.before.upper)
    }

    pub fn matches_arrival(
        &self,
        ratio: &PendingRatio,
        opening: &WordOpening,
        targets: &[usize],
    ) -> bool {
        ratio == &self.ratio && opening == &self.opening && targets == self.targets
    }

    pub fn ratio(&self) -> &PendingRatio {
        &self.ratio
    }
    pub fn opening(&self) -> &WordOpening {
        &self.opening
    }
    pub fn producing(&self) -> &Constitution {
        &self.producing
    }
    pub fn before(&self) -> &ExactInterval {
        &self.before
    }

    /// Exact executed-logit diagnostics, independent of objective enclosure precision.
    pub fn wave_changes(&self, wave: &Faces) -> ComparisonWaveChanges {
        let deltas = wave
            .logits
            .iter()
            .flatten()
            .zip(self.wave.logits.iter().flatten())
            .map(|(after, before)| after - before)
            .collect::<Vec<_>>();
        ComparisonWaveChanges {
            changed_coordinates: deltas.iter().filter(|x| **x != integer(0)).count(),
            largest_absolute_delta: deltas
                .iter()
                .map(|x| if *x < integer(0) { -x } else { x.clone() })
                .max()
                .unwrap_or_else(|| integer(0)),
            largest_numerator_bits: deltas.iter().map(|x| x.numer().bits()).max().unwrap_or(0),
            largest_denominator_bits: deltas.iter().map(|x| x.denom().bits()).max().unwrap_or(0),
        }
    }

    pub fn stage(
        &self,
        deposit: &Deposit,
        retained: &BTreeSet<Locus>,
        halvings: u32,
    ) -> Result<ComparisonCandidate, HnnError> {
        self.producing
            .staged_comparison_candidate(deposit, retained, halvings)
    }

    /// Consume the exact candidate read by the backend; publication is possible only after
    /// strict separation of this frozen comparison's objective enclosures, or exact equality
    /// of its executed wave expression. Interval overlap alone never admits a candidate.
    pub fn admit_candidate(
        &self,
        candidate: ComparisonCandidate,
        wave: &Faces,
    ) -> Result<Option<(Constitution, DepositReading)>, HnnError> {
        Ok(self.judge_candidate(candidate, wave)?.1)
    }

    pub fn judge_candidate(
        &self,
        candidate: ComparisonCandidate,
        wave: &Faces,
    ) -> Result<(ComparisonReading, Option<(Constitution, DepositReading)>), HnnError> {
        if candidate.producing() != &self.producing {
            return Err(HnnError::Unadmitted {
                reason: "candidate belongs to this complete producing material",
            });
        }
        let reading = self.evaluate(wave)?;
        let admitted = if reading.unchanged || reading.objective_equal() {
            // Identical exact logits/face expressions give the identical frozen objective.
            // Keep the candidate's validated sub-lattice carry/statistics rather than erase
            // them or repeatedly execute a smaller proposal with the same rounded output.
            Some(candidate.admit_neutral())
        } else {
            candidate.admit_change(&reading.objective_change)
        };
        Ok((reading, admitted))
    }

    fn objective(&self, wave: &Faces) -> Result<ExactInterval, HnnError> {
        let faces = self.ratio.phases().combine(wave, &self.trees)?;
        let holon = HolonRatio::compare(faces.clone(), &self.targets, &self.target_phases)?;
        let against = Against {
            faces,
            trees: self.trees.clone(),
        };
        let scored = self
            .ratio
            .scored(&self.producing, &against, &self.targets)?;
        Ok(interval_sum(
            &window_code_length(&scored.model)?,
            &ExactInterval::point(holon.excess()),
        )?)
    }

    /// Backend handoff for the wave produced by exactly this ratio/opening under its staged
    /// material. Like other native read handoffs, a Faces value is shape-checked, not a proof
    /// of arbitrary external execution. The backend owns that producing provenance.
    pub fn evaluate(&self, wave: &Faces) -> Result<ComparisonReading, HnnError> {
        let after = self.objective(wave)?;
        let mut reading = ComparisonReading {
            unchanged: wave == &self.wave,
            strictly_improved: after.upper < self.before.lower,
            objective_change: ExactInterval::new(
                &after.lower - &self.before.upper,
                &after.upper - &self.before.lower,
            )?,
            before: self.before.clone(),
            after,
            reading_bits: crate::ratio::exponentiated::READING_BITS,
            refinement_rounds: 0,
            retained_interval_members: self
                .producing
                .population(self.ratio.phases().ring())
                .ok_or(HnnError::MissingReceivingMap {
                    ring: self.ratio.phases().ring(),
                })?
                .retained_interval_members(),
        };
        if reading.unchanged {
            reading.objective_change = ExactInterval::point(integer(0));
            return Ok(reading);
        }
        if !reading.needs_precision() {
            return Ok(reading);
        }
        let before_faces = self.ratio.phases().combine(&self.wave, &self.trees)?;
        let after_faces = self.ratio.phases().combine(wave, &self.trees)?;
        let before_holon =
            HolonRatio::compare(before_faces.clone(), &self.targets, &self.target_phases)?;
        let after_holon =
            HolonRatio::compare(after_faces.clone(), &self.targets, &self.target_phases)?;
        let phase_delta = after_holon.excess() - before_holon.excess();
        let population = self
            .producing
            .population(self.ratio.phases().ring())
            .ok_or(HnnError::MissingReceivingMap {
                ring: self.ratio.phases().ring(),
            })?;
        reading.retained_interval_members = population.retained_interval_members();
        for (round, bits) in crate::hnn::receiving::cells::demand_ladder()
            .into_iter()
            .enumerate()
        {
            use crate::receiver::population::port::ComparedFace;
            reading.reading_bits = bits;
            let mut window = Vec::with_capacity(self.targets.len());
            for (((before, after), tree), &target) in before_faces
                .faces
                .iter()
                .zip(&after_faces.faces)
                .zip(&self.trees)
                .zip(&self.targets)
            {
                let tree_mass = ExactInterval::point(tree.probabilities[target].clone());
                let before_mass = crate::hnn::receiving::face_enclosure_at(before, target, bits)?;
                let combined = if before.grain() == after.grain()
                    && before.cells().len() == after.cells().len()
                    && before
                        .cells()
                        .iter()
                        .zip(after.cells())
                        .all(|(a, b)| a.carry == b.carry && a.phase == b.phase)
                {
                    ComparedFace::Shared(before_mass)
                } else {
                    ComparedFace::Changed {
                        before: before_mass,
                        after: crate::hnn::receiving::face_enclosure_at(after, target, bits)?,
                    }
                };
                window.push(vec![ComparedFace::Shared(tree_mass), combined]);
            }
            let change = population
                .code_change_at(&window, bits)
                .map_err(crate::hnn::receiving::population_refusal)?;
            reading.objective_change =
                ExactInterval::new(change.lower + &phase_delta, change.upper + &phase_delta)?;
            reading.strictly_improved = reading.objective_change.upper < integer(0);
            reading.refinement_rounds =
                u32::try_from(round).map_err(|_| HnnError::CountOverflow)?;
            // Keep independent absolute readings for audit at the same ladder step.
            reading.before = self.objective_at(&before_faces, before_holon.excess(), bits)?;
            reading.after = self.objective_at(&after_faces, after_holon.excess(), bits)?;
            if !reading.needs_precision() {
                break;
            }
        }
        Ok(reading)
    }

    fn objective_at(
        &self,
        faces: &Faces,
        phase: Rat,
        bits: u32,
    ) -> Result<ExactInterval, HnnError> {
        let ring = self.ratio.phases().ring();
        let population = self
            .producing
            .population(ring)
            .ok_or(HnnError::MissingReceivingMap { ring })?;
        let scored = crate::hnn::receiving::score_at(
            population,
            ring,
            faces,
            &self.trees,
            &self.targets,
            bits,
        )?;
        let mut lower = phase.clone();
        let mut upper = phase;
        for interval in scored.model {
            lower += interval.lower;
            upper += interval.upper;
        }
        Ok(ExactInterval::new(lower, upper)?)
    }

    pub fn read_candidate<'c>(
        &self,
        field: &'c Field,
        candidate: &Constitution,
        charts: &mut Charts,
    ) -> Result<(Word<'c>, Faces, ComparisonReading), HnnError> {
        let (word, wave) = self
            .ratio
            .read_on(field, candidate, charts, &self.opening)?;
        let reading = self.evaluate(&wave)?;
        Ok((word, wave, reading))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::tests::{learning, support::encoded};

    #[test]
    fn overlapping_readings_request_precision_without_claiming_a_wrong_step() {
        let reading = ComparisonReading {
            before: ExactInterval::new(integer(0), integer(2)).unwrap(),
            after: ExactInterval::new(integer(1), integer(3)).unwrap(),
            unchanged: false,
            strictly_improved: false,
            objective_change: ExactInterval::new(integer(-1), integer(3)).unwrap(),
            reading_bits: 96,
            refinement_rounds: 0,
            retained_interval_members: 0,
        };
        assert!(reading.needs_precision());
        assert_eq!(
            reading.unresolved_reason(),
            "objective enclosures are not strictly separated"
        );
        let worse = ComparisonReading {
            after: ExactInterval::point(integer(4)),
            objective_change: ExactInterval::new(integer(2), integer(4)).unwrap(),
            ..reading.clone()
        };
        assert!(!worse.needs_precision());
        assert_eq!(
            worse.unresolved_reason(),
            "candidate objective is strictly worse"
        );
        let plateau = ComparisonReading {
            unchanged: true,
            ..reading
        };
        assert!(!plateau.needs_precision());
        assert_eq!(plateau.unresolved_reason(), "identical executed wave");
    }

    fn paired_comparison_fixture() -> (Field, Reference, Resident, StagedId) {
        let mut d = crate::hnn::FieldDeclaration::campaign_one(1024);
        d.rings.truncate(2);
        for (ring, n) in d.rings.iter_mut().zip([2u64, 3]) {
            ring.period = n;
            ring.placements = (0..n)
                .map(|i| crate::hnn::FieldDeclaration::quarter_turn(i, n))
                .collect();
            ring.reflector = (0..n).map(|i| ((n - i) % n) as usize).collect();
        }
        d.contacts.truncate(1);
        d.contacts[0].channel = vec![(0, 0), (1, 1)];
        d.loops.clear();
        d.alphabet = 2;
        d.receivers[0].ring = 1;
        d.receivers[0].depth = 2;
        d.receivers[0].aperture = 1;
        d.crib.window = 2;
        d.lattice.clear();
        let field = Field::declare(d.by_lattice_rule()).unwrap();
        let mut theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        theta
            .bind_arrival_context_receiving(field.receivers()[0].ring)
            .unwrap();
        let (current, moment) = learning::moment(&field, 71, 2);
        let reference = Reference::campaign_one();
        let mut resident = reference.mount_with(&field, &current, theta).unwrap();
        let moment_id = MomentId(1);
        resident.moments.insert(moment_id, moment);
        resident.next = 1;
        let phases = resident.admitted()[0].clone();
        let (pending, _) = reference
            .refine(&mut resident, &moment_id, &phases)
            .unwrap();
        let (staged, _) = reference
            .compare(&mut resident, pending, &encoded(&field, &[0]))
            .unwrap();
        (field, reference, resident, staged)
    }

    #[test]
    fn no_reach_halving_is_strict_at_the_exact_fine_half_cell() {
        use crate::hnn::constitution::ComparisonStepEntries;
        let unit = crate::ratio::rat(3, 8);
        let precision = 5;
        let threshold = &unit * crate::holon::deposition::dyadic(-6);
        for (update, expected) in [
            (threshold.clone(), 1),
            (&threshold * crate::ratio::rat(3, 4), 0),
            (Rat::zero(), 0),
        ] {
            let parts = [ComparisonStepEntries {
                unit: unit.clone(),
                precision,
                updates: vec![update.clone(), -update],
            }];
            assert_eq!(no_reach_halving_of(&parts).unwrap(), expected);
        }
        assert_eq!(no_reach_halving_of(&[]).unwrap(), 0);
    }

    #[test]
    fn full_ladder_overlap_discards_the_handle_without_changing_material_or_carry() {
        use crate::receiver::population::port::ComparedFace;
        let (field, reference, mut resident, staged) = paired_comparison_fixture();
        let before = resident.constitution.clone();
        let carry = resident.carried.clone();
        let slot = &resident.staged[&staged];
        let mut frozen = slot.comparison.as_ref().unwrap().clone();
        let candidate = frozen
            .stage(&slot.deposit, &resident.retention(), 0)
            .unwrap();
        let mut charts = slot.trial_charts.as_ref().unwrap().clone();
        let (_, trial_wave) = frozen
            .ratio
            .read_on(&field, candidate.material(), &mut charts, &frozen.opening)
            .unwrap();
        // A fixture with changed class masses and a rational target phase at the midpoint of
        // the full ladder's code enclosure. The overlapping uncertainty is real, not a forged
        // ComparisonReading: evaluate and Reference::deposit both execute the complete owner.
        let grain = frozen.ratio.phases().grain();
        let mut logits = trial_wave.logits.clone();
        logits[0][0] += crate::ratio::rat(1, grain as i64);
        logits[0][1] += integer(2);
        frozen.wave = Faces::of_reads(
            &logits
                .into_iter()
                .map(|logits| crate::hnn::receiving::ReceivingRead::of_logits(logits, grain))
                .collect::<Vec<_>>(),
            grain,
        )
        .unwrap();
        let old_faces = frozen
            .ratio
            .phases()
            .combine(&frozen.wave, &frozen.trees)
            .unwrap();
        let new_faces = frozen
            .ratio
            .phases()
            .combine(&trial_wave, &frozen.trees)
            .unwrap();
        let last_bits = *crate::hnn::receiving::cells::demand_ladder()
            .last()
            .unwrap();
        let window = old_faces
            .faces
            .iter()
            .zip(&new_faces.faces)
            .zip(&frozen.trees)
            .zip(&frozen.targets)
            .map(|(((old, new), tree), &target)| {
                vec![
                    ComparedFace::Shared(ExactInterval::point(tree.probabilities[target].clone())),
                    ComparedFace::Changed {
                        before: crate::hnn::receiving::face_enclosure_at(old, target, last_bits)
                            .unwrap(),
                        after: crate::hnn::receiving::face_enclosure_at(new, target, last_bits)
                            .unwrap(),
                    },
                ]
            })
            .collect::<Vec<_>>();
        let delta = before
            .population(frozen.ratio.phases().ring())
            .unwrap()
            .code_change_at(&window, last_bits)
            .unwrap();
        let midpoint = (&delta.lower + &delta.upper) / integer(2);
        let phase = new_faces.faces[0].phases()[0].clone();
        frozen.target_phases.phases[0] = phase + crate::ratio::rat(1, 2) - midpoint;
        frozen.before = frozen.objective(&frozen.wave).unwrap();
        let reading = frozen.evaluate(&trial_wave).unwrap();
        assert!(
            reading.needs_precision(),
            "the full-ladder fixture must overlap"
        );
        assert_eq!(reading.reading_bits, last_bits);
        resident.staged.get_mut(&staged).unwrap().comparison = Some(frozen);
        let Err(HnnError::ComparisonUnresolved { trials, .. }) =
            reference.deposit(&mut resident, staged)
        else {
            panic!("the full ladder must return ComparisonUnresolved");
        };
        assert_eq!(trials.len(), 1);
        assert_eq!(trials[0].comparison.reading_bits, last_bits);
        assert_eq!(resident.constitution, before);
        assert_eq!(resident.carried, carry);
        assert!(!resident.staged.contains_key(&staged));
    }

    #[test]
    fn paired_native_candidate_halvings_preserve_cut_and_admit() {
        let (field, reference, mut resident, staged) = paired_comparison_fixture();
        let phases = resident.admitted()[0].clone();
        let before = resident.constitution.clone();
        let carry = resident.carried.clone();
        let slot = &resident.staged[&staged];
        let frozen = slot.comparison.as_ref().unwrap();
        let starting = frozen
            .stage(&slot.deposit, &resident.retention(), 0)
            .unwrap();
        let last_halving = no_reach_halving(&starting).unwrap();
        let identity = frozen.evaluate(&frozen.wave).unwrap();
        assert!(identity.unchanged);
        assert!(!identity.strictly_improved);
        assert!(frozen.bits() >= before.exact_bits());
        // An actually executed sub-lattice proposal is admitted as neutral, not improved.
        let neutral_candidate = frozen.stage(&slot.deposit, &before.held(), 64).unwrap();
        let neutral_material = neutral_candidate.material().clone();
        let mut trial_charts = slot.trial_charts.as_ref().unwrap().clone();
        let (_, neutral_wave, neutral_reading) = frozen
            .read_candidate(&field, neutral_candidate.material(), &mut trial_charts)
            .unwrap();
        assert!(neutral_reading.unchanged);
        assert!(!neutral_reading.strictly_improved);
        let (neutral_reading, admitted) = frozen
            .judge_candidate(neutral_candidate, &neutral_wave)
            .unwrap();
        assert!(neutral_reading.unchanged);
        assert_eq!(admitted.unwrap().0, neutral_material);
        let neutral_state = neutral_material.continuing_state(0).unwrap();
        let neutral_state =
            crate::hnn::constitution::ContinuingState::from_text(&neutral_state.to_text()).unwrap();
        assert_eq!(
            before.clone().continued(&neutral_state).unwrap(),
            neutral_material
        );
        assert_eq!(resident.constitution, before);
        assert_eq!(resident.carried, carry);
        let grain = phases.grain();
        let mut bad = frozen.wave.logits.clone();
        bad[0][1] += integer(1024);
        let bad = Faces::of_reads(
            &bad.into_iter()
                .map(|x| crate::hnn::receiving::ReceivingRead::of_logits(x, grain))
                .collect::<Vec<_>>(),
            grain,
        )
        .unwrap();
        assert!(!frozen.evaluate(&bad).unwrap().strictly_improved);
        let mut good = frozen.wave.logits.clone();
        good[0][0] += integer(16);
        good[0][1] = &frozen.target_phases.phases[0] * integer(2);
        let good = Faces::of_reads(
            &good
                .into_iter()
                .map(|x| crate::hnn::receiving::ReceivingRead::of_logits(x, grain))
                .collect::<Vec<_>>(),
            grain,
        )
        .unwrap();
        assert!(frozen.evaluate(&good).unwrap().strictly_improved);
        let mut objective_neutral = frozen.wave.logits.clone();
        objective_neutral[0][3] += integer(1); // non-target phase, no class-mass change
        let objective_neutral = Faces::of_reads(
            &objective_neutral
                .into_iter()
                .map(|x| crate::hnn::receiving::ReceivingRead::of_logits(x, grain))
                .collect::<Vec<_>>(),
            grain,
        )
        .unwrap();
        let neutral = frozen.evaluate(&objective_neutral).unwrap();
        assert!(!neutral.unchanged);
        assert!(neutral.objective_equal());
        assert!(!neutral.strictly_improved);
        assert!(!neutral.needs_precision());
        let mut same_mass_fibre = frozen.wave.logits.clone();
        same_mass_fibre[0][0] += crate::ratio::rat(1, 1 << 20);
        let same_mass_fibre = Faces::of_reads(
            &same_mass_fibre
                .into_iter()
                .map(|x| crate::hnn::receiving::ReceivingRead::of_logits(x, grain))
                .collect::<Vec<_>>(),
            grain,
        )
        .unwrap();
        let fibre_reading = frozen.evaluate(&same_mass_fibre).unwrap();
        assert!(!fibre_reading.unchanged);
        assert!(fibre_reading.objective_equal());
        assert!(!fibre_reading.strictly_improved);
        let candidate = frozen.stage(&slot.deposit, &before.held(), 64).unwrap();
        assert!(
            frozen
                .judge_candidate(candidate, &objective_neutral)
                .unwrap()
                .1
                .is_some()
        );
        let candidate = frozen.stage(&slot.deposit, &before.held(), 64).unwrap();
        assert!(frozen.judge_candidate(candidate, &bad).unwrap().1.is_none());
        resident.arrived.as_mut().unwrap().targets[0] = 1;
        assert!(matches!(
            reference.deposit(&mut resident, staged),
            Err(HnnError::Unadmitted { .. })
        ));
        assert_eq!(resident.constitution, before);
        resident.arrived.as_mut().unwrap().targets[0] = 0;
        let returned = reference.deposit(&mut resident, staged).unwrap();
        let ReceiptDetail::Deposit {
            finite_comparison: Some(receipt),
            ..
        } = returned.receipt.detail
        else {
            panic!("finite comparison receipt");
        };
        assert!(
            receipt.comparison.strictly_improved,
            "the native fixture admits strict frozen-objective improvement"
        );
        assert!(!receipt.comparison.objective_equal());
        assert!(!receipt.comparison.unchanged);
        println!(
            "native candidate admission: improved={} objective_equal={} unchanged={} halvings={} no_reach_halving={}",
            receipt.comparison.strictly_improved,
            receipt.comparison.objective_equal(),
            receipt.comparison.unchanged,
            receipt.halvings,
            last_halving,
        );
        assert!(receipt.halvings <= last_halving);
        assert!(receipt.attempts > 0);
        assert_eq!(receipt.attempts, receipt.halvings + 1);
        assert!(
            crate::hnn::receiving::cells::demand_ladder()
                .contains(&receipt.comparison.reading_bits)
        );
        assert_eq!(resident.carried, carry);
        assert!(
            resident.constitution.commit() > before.commit(),
            "the fixture must admit a strictly improved candidate"
        );
    }
}

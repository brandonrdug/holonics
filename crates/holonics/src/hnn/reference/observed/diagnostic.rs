//! Receiving-map interventions at an actual kept native read, with an optional factual-prefix
//! diagnostic consumer. Read-only interventions change no producing operand. The prefix consumer
//! stages only actual target reception/ingress on a caller-owned fork, with native R frozen.

use super::*;
use crate::compression::landmark::context::LandmarkFace;
use crate::hnn::constitution::ReceivingLayout;
use crate::hnn::receiving::ReceivingCarrier;
use crate::hnn::receiving::cells::ScoredFaceReading;
use crate::hnn::receiving::cells::diagnostic::{
    ReadoutClassCodeDiagnostic, compare_readout_class_codes_at,
};
use crate::hnn::receiving::cells::diagnostic::{ReadoutMapDiagnostic, compare_readout_maps_at};

/// Exterior provenance and both operative R reads from one pending aperture-one word. The
/// control is a readout substitution on fixed features, never a replacement live constitution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PendingReadoutDiagnostic {
    pub pending: PendingId,
    pub material_commit: u64,
    pub source_cells: u64,
    pub anchor: Vec<BigInt>,
    pub phases: ReceivingPhases,
    pub tree: LandmarkFace,
    pub scored_face: ScoredFaceReading,
    pub native_map: ExactRatMatrix,
    pub control_map: ExactRatMatrix,
    pub readout: ReadoutMapDiagnostic,
}

/// Exterior same-prefix R-only class-code observation and its actual target ingress.
/// The target is ordinary observed boundary input, never a fabricated release decision.
/// No normal-law sample/deposition is published by this diagnostic consumer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetPrefixReadoutControlReceipt {
    pub diagnostic: PendingReadoutDiagnostic,
    pub codes: ReadoutClassCodeDiagnostic,
    /// The actual encoded target and both produced phases use the same passage frame.
    pub target_phase: Rat,
    pub native_phase_excess: Rat,
    pub control_phase_excess: Rat,
    pub native_minus_control_phase_excess: Rat,
    pub ingestion: IngestClassReceipt,
}

impl Reference {
    /// Score an actual target on the blind kept word under native and control R, on identical
    /// feature/tree/population, then receive that factual prefix on a caller-owned private fork.
    ///
    /// [agent-inferred consuming join] The sequence uses the existing native score, addressed
    /// tree reception, `observed_epoch_prefix`, arrival ledger and shared class ingress owners.
    /// The material maps are never deposited. A supplied frozen native R is checked both before
    /// and after ingress, including a possible actual aeon close. Every refusal is atomic in
    /// resident and crib. The caller keeps the main checkpoint apart and bounds the held-out
    /// source; this one-cell API imposes no guessed EOS, source padding or raised work limit.
    ///
    /// Later prefixes follow the factual native population/tree history. The founding-R arm
    /// is re-read at that SAME history, not a separately adapted counterfactual population.
    /// Code differences therefore isolate R at the reached feature; they do not attribute a
    /// whole-life gain to R, source learning or semantics. The returned receipt is exterior
    /// evidence; the resident retains only its existing contemporary arrival and sufficient
    /// source/tree/population operands, never a new event list or adjoint tape.
    #[allow(clippy::too_many_arguments)]
    pub fn receive_target_prefix_readout_control(
        &self,
        resident: &mut Resident,
        crib: &mut ObservedCrib,
        pairing: &PairingDeclaration,
        pending: PendingId,
        target: usize,
        expected_native_map: &ExactRatMatrix,
        control_map: &ExactRatMatrix,
        bits: u32,
        placement: Option<&OccurrencePlacement>,
    ) -> Result<TargetPrefixReadoutControlReceipt, HnnError> {
        let refuse = |reason| HnnError::Unadmitted { reason };
        resident.admit_exact_current()?;
        if resident.pending.len() != 1 || !resident.staged.is_empty() || resident.moments.len() != 1
        {
            return Err(refuse(
                "a target-prefix control consumes one actual pending word and source moment",
            ));
        }
        let slot = resident
            .pending
            .get(&pending)
            .ok_or(HnnError::UnknownHandle {
                handle: Handle::Pending(pending),
            })?;
        if slot.ratio.current(&resident.field)? != resident.current
            || resident.moments.values().next() != Some(slot.ratio.moment())
        {
            return Err(refuse(
                "a target-prefix control continues its actual producing current and moment",
            ));
        }
        // This authenticates the actual kept feature/face before consulting the target's class.
        let diagnostic = self.diagnose_pending_readout(resident, &pending, control_map, bits)?;
        if &diagnostic.native_map != expected_native_map {
            return Err(refuse(
                "a target-prefix control keeps the caller's frozen native receiving map",
            ));
        }
        let (_, encoded_target) = admit_observed_cell(resident, crib, pairing, target, placement)?;
        let codes = compare_readout_class_codes_at(
            &diagnostic.scored_face,
            &diagnostic.tree,
            &diagnostic.readout.feature,
            &diagnostic.native_map,
            &diagnostic.readout.native_wave_logits,
            control_map,
            target,
            bits,
        )?;
        let phases = slot.ratio.phases();
        let receiver = phases.ring();
        let target_phase = crate::hnn::ratio::target_phases(
            &resident.field,
            slot.ratio.anchor(),
            receiver,
            &encoded_target,
        )?
        .phases
        .into_iter()
        .next()
        .ok_or_else(|| refuse("a one-cell readout control keeps its actual target phase"))?;
        // HolonRatio::compare uses precisely half the squared unwrapped phase gap.
        // The tree contributes no imaginary logit; all produced phase data are rational.
        let phase_row = target
            .checked_mul(2)
            .and_then(|r| r.checked_add(1))
            .ok_or(HnnError::CountOverflow)?;
        let phase_excess = |wave: &[Rat]| -> Result<Rat, HnnError> {
            let produced = wave.get(phase_row).ok_or(HnnError::Shape {
                what: "a readout control's actual target phase row",
                expected: phase_row + 1,
                found: wave.len(),
            })? / integer(2);
            let gap = &target_phase - produced;
            Ok(&gap * &gap / integer(2))
        };
        let native_phase_excess = phase_excess(&diagnostic.readout.native_wave_logits)?;
        let control_phase_excess = phase_excess(&diagnostic.readout.control_wave_logits)?;
        let native_minus_control_phase_excess = &native_phase_excess - &control_phase_excess;
        let kept = slot
            .kept
            .as_ref()
            .ok_or_else(|| refuse("a target-prefix code keeps its producing word"))?;
        let against = slot
            .ratio
            .against(&resident.constitution, &kept.faces, &[])?;
        // Prefix reception uses the ordinary native likelihood precision, independently of
        // how finely this diagnostic's class codes were requested. This is score's own step.
        let scored = slot
            .ratio
            .scored(&resident.constitution, &against, &[target])?;
        let mut tree = resident
            .constitution
            .landmarks(receiver)
            .ok_or(HnnError::MissingReceivingMap { ring: receiver })?
            .clone();
        let read_tree = match slot.ratio.observed_addresses(&[])? {
            Some(addresses) => {
                tree.receive_observed_arrivals(&addresses, &[target], phases.grain())?
            }
            None => {
                tree.receive_arrivals(&slot.ratio.addresses(&[])?, &[target], phases.grain())?
            }
        };
        if read_tree.as_slice() != against.trees.as_slice() {
            return Err(refuse(
                "the target code and tree reception keep the same actual address and face",
            ));
        }
        let arrived = Arrived {
            ratio: slot.ratio.clone(),
            targets: vec![target],
            opening: slot.opening.clone(),
        };
        let mut next = resident.clone();
        let mut next_crib = crib.clone();
        next.constitution =
            next.constitution
                .observed_epoch_prefix(receiver, tree, &scored.steps)?;
        next.ledger.arrive(scored.model[0].clone(), 1);
        next.arrived = Some(arrived);
        self.discard(&mut next, Handle::Pending(pending))?;
        let ingestion =
            self.ingest_class_step(&mut next, &mut next_crib, pairing, target, placement)?;
        if next.constitution.receiving_map(receiver) != Some(expected_native_map) {
            return Err(refuse(
                "actual target-prefix ingress must preserve the frozen native receiving map",
            ));
        }
        *resident = next;
        *crib = next_crib;
        Ok(TargetPrefixReadoutControlReceipt {
            diagnostic,
            codes,
            target_phase,
            native_phase_excess,
            control_phase_excess,
            native_minus_control_phase_excess,
            ingestion,
        })
    }

    /// Compare the native and a declared control R on the *same actual kept-word feature*.
    /// This aperture-one Physical/Anchor diagnostic freezes the tree and the population before
    /// any target/release reception. Other layouts and a missing/stale kept read refuse. The
    /// caller may use the founding R as its control; E and all retained moments remain native.
    pub fn diagnose_pending_readout(
        &self,
        resident: &Resident,
        pending: &PendingId,
        control_map: &ExactRatMatrix,
        bits: u32,
    ) -> Result<PendingReadoutDiagnostic, HnnError> {
        resident.admit_exact_current()?;
        let slot = resident
            .pending
            .get(pending)
            .ok_or(HnnError::UnknownHandle {
                handle: Handle::Pending(*pending),
            })?;
        let phases = slot.ratio.phases();
        let ring = phases.ring();
        let theta = &resident.constitution;
        if phases.aperture() != 1
            || theta.receiving_layout(ring) != Some(ReceivingLayout::Single)
            || ConstitutionRead::receiving_carrier(theta, ring) != ReceivingCarrier::Anchor
        {
            return Err(HnnError::Unadmitted {
                reason: "a pending readout control requires one physical anchor read",
            });
        }
        let kept = slot.kept.as_ref().ok_or(HnnError::Unadmitted {
            reason: "a pending readout control requires its actual kept native word",
        })?;
        if kept.commit != theta.commit() || slot.ratio.commit() != theta.commit() {
            return Err(HnnError::Unadmitted {
                reason: "a pending readout control refuses a changed producing constitution",
            });
        }
        let features = resident
            .receiving_inputs(pending, phases)?
            .ok_or(HnnError::Unadmitted {
                reason: "a pending readout control has no producing receiving feature",
            })?;
        let [feature] = features.as_slice() else {
            return Err(HnnError::Unadmitted {
                reason: "a pending readout control preserves one complete producing feature",
            });
        };
        let native_read = phases.read(&resident.field, theta, feature)?;
        if kept.faces.logits.as_slice() != [native_read.logits.clone()]
            || kept.faces.faces.as_slice()
                != [crate::hnn::ratio::Face::of_read(
                    &native_read,
                    phases.grain(),
                )?]
        {
            return Err(HnnError::Unadmitted {
                reason: "a pending readout control reconstructs its exact kept native read",
            });
        }
        // No known response target enters this address. This is the actual query's first face.
        let against = slot.ratio.against(theta, &kept.faces, &[])?;
        let tree = against.trees.first().ok_or(HnnError::Unadmitted {
            reason: "a pending readout control keeps its producing tree face",
        })?;
        let population = ConstitutionRead::population(theta, ring)
            .ok_or(HnnError::MissingReceivingMap { ring })?;
        let scored_face = ScoredFaceReading {
            population: population.clone(),
            tree_probabilities: tree.probabilities.clone(),
            combined: against.faces.faces[0].clone(),
        };
        let native_map = ConstitutionRead::receiving_map(theta, ring)
            .ok_or(HnnError::MissingReceivingMap { ring })?;
        let readout = compare_readout_maps_at(
            &scored_face,
            tree,
            feature,
            native_map,
            &native_read.logits,
            control_map,
            bits,
        )?;
        Ok(PendingReadoutDiagnostic {
            pending: *pending,
            material_commit: theta.commit(),
            source_cells: slot.ratio.moment().cells(),
            anchor: slot.ratio.anchor().to_vec(),
            phases: phases.clone(),
            tree: tree.clone(),
            scored_face,
            native_map: native_map.clone(),
            control_map: control_map.clone(),
            readout,
        })
    }
}

/// One explicitly hypothetical class received under an alternate native receiver. It is an
/// branch operand, not a release certificate. A caller binds its own existing conditional
/// keyed-draw certificate or whole-section certificate before publishing a class.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiverPrefixReceipt {
    pub receiver: crate::hnn::receiving::RetainedFibreReceiver,
    pub class: usize,
    pub producing: crate::hnn::receiving::cells::diagnostic::RetainedScoredFaceReading,
    pub ingestion: IngestClassReceipt,
}

impl Reference {
    /// Same kept native word and retained map/tree/population, read by an explicitly finer
    /// receiver. Neither the original declaration nor the immutable checkpoint is changed.
    pub fn diagnose_pending_readout_at_receiver(
        &self,
        resident: &Resident,
        pending: &PendingId,
        control_map: &ExactRatMatrix,
        receiver: &crate::hnn::receiving::RetainedFibreReceiver,
        bits: u32,
    ) -> Result<crate::hnn::receiving::cells::diagnostic::RetainedReceiverDiagnostic, HnnError>
    {
        let old = self.diagnose_pending_readout(resident, pending, control_map, bits)?;
        crate::hnn::receiving::cells::diagnostic::compare_readout_maps_at_receiver(
            &old.scored_face,
            &old.tree,
            &old.readout.feature,
            &old.native_map,
            &old.readout.native_wave_logits,
            control_map,
            receiver,
            bits,
        )
    }

    /// Receive one complete hypothesized prefix class at its actual producing cut, using the
    /// SAME alternate receiver that supplied the conditional oracle. This joins its native
    /// population likelihood and addressed tree reception before ordinary continuing ingress:
    /// L_f' = L_f * p_f(c), T' = receive(T,c), then current/moment/crib advance once. Maps are not
    /// deposited. Original checkpoint/other branches stay separate; every refusal is atomic.
    ///
    /// Source/receiver encoding and physical clocks keep their original declaration. Only the
    /// explicit observation quotient changes. No class certificate is forged: this API receives
    /// a hypothesis on a disposable branch, and its receipt remains exterior evidence. The
    /// consuming chain-rule section and chart-restriction formal joins remain owed in #62.
    #[allow(clippy::too_many_arguments)]
    pub fn receive_receiver_prefix_continuing(
        &self,
        resident: &mut Resident,
        crib: &mut ObservedCrib,
        pairing: &PairingDeclaration,
        pending: PendingId,
        class: usize,
        receiver: &crate::hnn::receiving::RetainedFibreReceiver,
        placement: Option<&OccurrencePlacement>,
    ) -> Result<ReceiverPrefixReceipt, HnnError> {
        let refuse = |reason| HnnError::Unadmitted { reason };
        resident.admit_exact_current()?;
        admit_observed_cell(resident, crib, pairing, class, placement)?;
        if resident.pending.len() != 1 || !resident.staged.is_empty() || resident.moments.len() != 1
        {
            return Err(refuse(
                "an alternate receiver continues one actual pending word and moment",
            ));
        }
        let slot = resident
            .pending
            .get(&pending)
            .ok_or(HnnError::UnknownHandle {
                handle: Handle::Pending(pending),
            })?;
        let phases = slot.ratio.phases();
        let ring = phases.ring();
        if phases.aperture() != 1
            || receiver.source_grain() != phases.grain()
            || slot.ratio.commit() != resident.constitution.commit()
            || slot.ratio.current(&resident.field)? != resident.current
            || resident.moments.values().next() != Some(slot.ratio.moment())
        {
            return Err(refuse(
                "an alternate receiver prefix keeps its actual aperture, grain, material and current",
            ));
        }
        let native_map = resident
            .constitution
            .receiving_map(ring)
            .ok_or(HnnError::MissingReceivingMap { ring })?
            .clone();
        let read = self.diagnose_pending_readout_at_receiver(
            resident,
            &pending,
            &native_map,
            receiver,
            crate::ratio::exponentiated::READING_BITS,
        )?;
        let producing = read.native_reading;
        let step = crate::hnn::receiving::ReceivingStep {
            ring,
            tree: producing
                .tree_probabilities
                .get(class)
                .ok_or(HnnError::CellOutside {
                    code: class,
                    alphabet: producing.tree_probabilities.len(),
                })?
                .clone(),
            combined: producing
                .combined_masses_at(crate::ratio::exponentiated::READING_BITS)?
                .get(class)
                .ok_or(HnnError::CellOutside {
                    code: class,
                    alphabet: producing.tree_probabilities.len(),
                })?
                .clone(),
        };
        let mut tree = resident
            .constitution
            .landmarks(ring)
            .ok_or(HnnError::MissingReceivingMap { ring })?
            .clone();
        match slot.ratio.observed_addresses(&[])? {
            Some(addresses) => {
                tree.receive_observed_arrivals(&addresses, &[class], phases.grain())?;
            }
            None => {
                tree.receive_arrivals(&slot.ratio.addresses(&[])?, &[class], phases.grain())?;
            }
        }
        let mut next = resident.clone();
        let mut next_crib = crib.clone();
        next.constitution = next
            .constitution
            .observed_epoch_prefix(ring, tree, &[step])?;
        self.discard(&mut next, Handle::Pending(pending))?;
        let ingestion =
            self.ingest_class_step(&mut next, &mut next_crib, pairing, class, placement)?;
        if next.constitution.receiving_map(ring) != Some(&native_map) {
            return Err(refuse(
                "an alternate receiver prefix preserves its frozen native receiving map",
            ));
        }
        *resident = next;
        *crib = next_crib;
        Ok(ReceiverPrefixReceipt {
            receiver: receiver.clone(),
            class,
            producing,
            ingestion,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::tests::support::{contact, encoded, small_field_of};
    use crate::ratio::exponentiated::READING_BITS;

    #[test]
    fn pending_readout_control_consumes_the_actual_kept_word_without_teaching() {
        let base = small_field_of(
            &[5, 2, 3],
            vec![contact(0, 1, 1, 0), contact(1, 2, 1, 0)],
            2,
            4,
        );
        let mut declaration = base.declaration().clone();
        declaration.receivers[0].aperture = 1;
        let field = Field::declare(declaration.by_lattice_rule()).unwrap();
        let material = Constitution::initial(&field, 1 << 40).unwrap();
        let phases = field.receivers().first().unwrap();
        let map = material.receiving_law(phases.ring).unwrap().map().clone();
        let reference = Reference::new(16, 1 << 40);
        let mut resident = reference
            .mount_with(&field, &Current::at_rest(&field), material)
            .unwrap();
        let (moment, _) = reference
            .ingest(&mut resident, None, &encoded(&field, &[0, 1, 2]))
            .unwrap();
        let phases = resident.admitted[0].clone();
        let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
        // A live kept comparison is intentionally not checkpointable. Compare the complete
        // actual resident, including its kept word, without crossing that checkpoint guard.
        let before = format!("{resident:?}");
        let diagnostic = reference
            .diagnose_pending_readout(&resident, &pending, &map, READING_BITS)
            .unwrap();
        assert_eq!(diagnostic.readout.native, diagnostic.readout.control);
        assert_eq!(
            diagnostic.readout.native_wave_logits,
            resident.pending[&pending]
                .kept
                .as_ref()
                .unwrap()
                .faces
                .logits[0]
        );
        assert_eq!(diagnostic.source_cells, 3);
        assert_eq!(format!("{resident:?}"), before);
        assert!(resident.holds_kept_read(&pending));
        let malformed = ExactRatMatrix::new(vec![vec![integer(0)]]).unwrap();
        assert!(
            reference
                .diagnose_pending_readout(&resident, &pending, &malformed, READING_BITS)
                .is_err()
        );
        assert_eq!(format!("{resident:?}"), before);
        resident
            .pending
            .get_mut(&pending)
            .unwrap()
            .kept
            .as_mut()
            .unwrap()
            .faces
            .logits[0][0] += integer(1);
        let corrupt = format!("{resident:?}");
        assert!(
            reference
                .diagnose_pending_readout(&resident, &pending, &map, READING_BITS)
                .is_err()
        );
        assert_eq!(format!("{resident:?}"), corrupt);
    }
    fn target_opening(
        before_carry: bool,
    ) -> (
        Reference,
        Resident,
        ObservedCrib,
        PairingDeclaration,
        Constitution,
    ) {
        use crate::hnn::paired::PairedCarrier;
        let base = small_field_of(
            &[5, 2, 3],
            vec![contact(0, 1, 1, 0), contact(1, 2, 1, 0)],
            2,
            4,
        );
        let mut declaration = base.declaration().clone();
        declaration.receivers[0].aperture = 1;
        declaration.rings[0].lock = (0..4).collect();
        for ring in &mut declaration.rings[1..] {
            ring.lock.clear();
        }
        declaration.lattice.clear();
        let field = Field::declare(declaration.by_lattice_rule()).unwrap();
        let pairing = PairingDeclaration::Family {
            table: (0..4).map(|class| (class, class ^ 1)).collect(),
        };
        let material = PairedCarrier::found(
            &field,
            Constitution::initial(&field, 1 << 40).unwrap(),
            0,
            &pairing,
        )
        .unwrap()
        .0;
        let reference = Reference::new(16, 1 << 40);
        let current = if before_carry {
            Current::at(
                &field,
                field
                    .rings()
                    .iter()
                    .map(|ring| BigInt::from(ring.period() - 1))
                    .collect(),
            )
            .unwrap()
        } else {
            Current::at_rest(&field)
        };
        let mut resident = reference
            .mount_with(&field, &current, material.clone())
            .unwrap();
        let boundary = PairedObservation::admit(&field, &material, &pairing).unwrap();
        reference
            .ingest(&mut resident, None, &boundary.encode(&[]).unwrap())
            .unwrap();
        (reference, resident, ObservedCrib::new(0), pairing, material)
    }

    fn target_pending(port: &Reference, resident: &mut Resident) -> PendingId {
        let moment = resident.continuing().unwrap().0;
        let phases = resident.admitted[0].clone();
        port.refine(resident, &moment, &phases).unwrap().0
    }

    #[test]
    fn target_prefix_control_matches_native_score_and_advances_only_factual_prefix_statistics() {
        let (port, mut resident, mut crib, pairing, _) = target_opening(false);
        let trunk = resident.clone();
        let ring = resident.admitted[0].ring();
        let frozen = resident.constitution.receiving_map(ring).unwrap().clone();
        for target in [0, 1, 3] {
            let pending = target_pending(&port, &mut resident);
            let slot = &resident.pending[&pending];
            let phases = slot.ratio.phases();
            let against = slot
                .ratio
                .against(
                    &resident.constitution,
                    &slot.kept.as_ref().unwrap().faces,
                    &[],
                )
                .unwrap();
            let scored = slot
                .ratio
                .scored(&resident.constitution, &against, &[target])
                .unwrap();
            let population_before = resident.constitution.population(ring).unwrap().clone();
            let mut expected_tree = resident.constitution.landmarks(ring).unwrap().clone();
            expected_tree
                .receive(&slot.ratio.addresses(&[]).unwrap()[0], target)
                .unwrap();
            let expected = resident
                .constitution
                .observed_epoch_prefix(ring, expected_tree, &scored.steps)
                .unwrap();
            let maps = (
                resident.constitution.source_port(0).cloned(),
                resident.constitution.receiving_map(ring).cloned(),
            );
            let commit = resident.constitution.commit();
            let grain = phases.grain();
            let (_, encoded_target) =
                admit_observed_cell(&resident, &crib, &pairing, target, None).unwrap();
            let target_phases = crate::hnn::ratio::target_phases(
                &resident.field,
                slot.ratio.anchor(),
                ring,
                &encoded_target,
            )
            .unwrap();
            let expected_phase_excess = crate::hnn::ratio::HolonRatio::compare(
                against.faces.clone(),
                &[target],
                &target_phases,
            )
            .unwrap()
            .excess();
            let receipt = port
                .receive_target_prefix_readout_control(
                    &mut resident,
                    &mut crib,
                    &pairing,
                    pending,
                    target,
                    &frozen,
                    &frozen,
                    READING_BITS,
                    None,
                )
                .unwrap();
            let direct = crate::hnn::receiving::score_at(
                &population_before,
                ring,
                &against.faces,
                &against.trees,
                &[target],
                READING_BITS,
            )
            .unwrap();
            assert_eq!(receipt.codes.native_code, direct.model[0]);
            assert_eq!(receipt.codes.tree_code, direct.tree[0]);
            assert_eq!(
                receipt.codes.native_minus_control,
                ExactInterval::point(integer(0))
            );
            assert_eq!(receipt.diagnostic.tree.grain, grain);
            assert_eq!(receipt.native_phase_excess, expected_phase_excess);
            assert_eq!(receipt.control_phase_excess, expected_phase_excess);
            assert_eq!(receipt.native_minus_control_phase_excess, Rat::zero());
            assert_eq!(receipt.target_phase, target_phases.phases[0]);
            assert_eq!(
                resident.constitution.landmarks(ring),
                expected.landmarks(ring)
            );
            assert_eq!(
                resident.constitution.population(ring),
                expected.population(ring)
            );
            assert_eq!(
                (
                    resident.constitution.source_port(0).cloned(),
                    resident.constitution.receiving_map(ring).cloned()
                ),
                maps
            );
            assert_eq!(resident.constitution.commit(), commit);
            assert!(resident.pending.is_empty());
            assert_eq!(receipt.codes.target, target);
            assert_eq!(crib.entries().last().unwrap().class, target);
            assert_eq!(resident.arrived.as_ref().unwrap().targets, vec![target]);
        }
        assert_eq!(trunk.moments.values().next().unwrap().cells(), 0);
        assert_eq!(resident.moments.values().next().unwrap().cells(), 3);
    }

    #[test]
    fn target_prefix_control_blind_word_does_not_consult_its_target() {
        let (port, trunk, original_crib, pairing, _) = target_opening(false);
        let ring = trunk.admitted[0].ring();
        let frozen = trunk.constitution.receiving_map(ring).unwrap().clone();
        let mut readings = Vec::new();
        for target in [0, 3] {
            let mut resident = trunk.clone();
            let mut crib = original_crib.clone();
            let pending = target_pending(&port, &mut resident);
            readings.push(
                port.receive_target_prefix_readout_control(
                    &mut resident,
                    &mut crib,
                    &pairing,
                    pending,
                    target,
                    &frozen,
                    &frozen,
                    READING_BITS,
                    None,
                )
                .unwrap(),
            );
        }
        assert_eq!(readings[0].diagnostic, readings[1].diagnostic);
        assert_eq!((readings[0].codes.target, readings[1].codes.target), (0, 3));
        assert_eq!(trunk.moments.values().next().unwrap().cells(), 0);
    }

    #[test]
    fn target_prefix_control_cold_continuation_keeps_codes_and_frozen_maps_exact() {
        let (port, mut warm, mut warm_crib, pairing, material) = target_opening(false);
        let ring = warm.admitted[0].ring();
        let frozen = warm.constitution.receiving_map(ring).unwrap().clone();
        for target in [0, 1] {
            let pending = target_pending(&port, &mut warm);
            port.receive_target_prefix_readout_control(
                &mut warm,
                &mut warm_crib,
                &pairing,
                pending,
                target,
                &frozen,
                &frozen,
                READING_BITS,
                None,
            )
            .unwrap();
        }
        let saved = warm.continuing_state(0).unwrap();
        let parsed = ContinuingState::from_text(&saved.to_text(), 1 << 40).unwrap();
        let field = warm.field.clone();
        let mut cold = port
            .mount_continued(&field, &Current::at_rest(&field), material, &parsed)
            .unwrap();
        let mut cold_crib = ObservedCrib::from_unplaced_checkpoint(
            &field,
            cold.current(),
            warm_crib.next_position(),
            &warm_crib.unplaced_checkpoint().unwrap(),
        )
        .unwrap();
        for target in [3, 2, 0] {
            let a = target_pending(&port, &mut warm);
            let b = target_pending(&port, &mut cold);
            let warm_read = port
                .receive_target_prefix_readout_control(
                    &mut warm,
                    &mut warm_crib,
                    &pairing,
                    a,
                    target,
                    &frozen,
                    &frozen,
                    READING_BITS,
                    None,
                )
                .unwrap();
            let cold_read = port
                .receive_target_prefix_readout_control(
                    &mut cold,
                    &mut cold_crib,
                    &pairing,
                    b,
                    target,
                    &frozen,
                    &frozen,
                    READING_BITS,
                    None,
                )
                .unwrap();
            assert_eq!(warm_read.diagnostic, cold_read.diagnostic);
            assert_eq!(warm_read.codes, cold_read.codes);
            assert_eq!(warm.constitution.receiving_map(ring), Some(&frozen));
            assert_eq!(cold.constitution.receiving_map(ring), Some(&frozen));
            assert_eq!(warm_crib, cold_crib);
            assert_eq!(
                warm.continuing_state(0).unwrap().to_text(),
                cold.continuing_state(0).unwrap().to_text()
            );
        }
    }

    #[test]
    fn target_prefix_control_frozen_readout_and_ordinary_target_admission_refuse_atomically() {
        for defect in 0..6 {
            let (port, mut resident, mut crib, pairing, _) = target_opening(false);
            let pending = target_pending(&port, &mut resident);
            let ring = resident.admitted[0].ring();
            let frozen = resident.constitution.receiving_map(ring).unwrap().clone();
            let wrong = ExactRatMatrix::zero(1, 1).unwrap();
            if defect == 2 {
                crib = ObservedCrib::new(1);
            }
            if defect == 3 {
                // The pending word remains authentic at its old cut but no longer belongs to
                // this resident's actual source/current after an ordinary delivered cell.
                port.ingest_class_continuing(&mut resident, &mut crib, &pairing, 1, None)
                    .unwrap();
            }
            if defect == 4 {
                target_pending(&port, &mut resident);
            }
            if defect == 5 {
                resident
                    .pending
                    .get_mut(&pending)
                    .unwrap()
                    .kept
                    .as_mut()
                    .unwrap()
                    .commit += 1;
            }
            let before = format!("{resident:?}");
            let old_crib = crib.clone();
            let expected = if defect == 0 { &wrong } else { &frozen };
            let target = if defect == 1 {
                resident.field.alphabet()
            } else {
                0
            };
            assert!(
                port.receive_target_prefix_readout_control(
                    &mut resident,
                    &mut crib,
                    &pairing,
                    pending,
                    target,
                    expected,
                    &frozen,
                    READING_BITS,
                    None,
                )
                .is_err()
            );
            assert_eq!(format!("{resident:?}"), before);
            assert_eq!(crib, old_crib);
        }
    }

    #[test]
    fn target_prefix_control_late_close_refusal_rolls_back_all_factual_reception() {
        let (port, mut resident, mut crib, pairing, _) = target_opening(true);
        let pending = target_pending(&port, &mut resident);
        let ring = resident.admitted[0].ring();
        let frozen = resident.constitution.receiving_map(ring).unwrap().clone();
        crib.entries.push(ObservedCribCell {
            position: 0,
            class: resident.field.alphabet(),
            placement: None,
        });
        let before = format!("{resident:?}");
        let old_crib = crib.clone();
        assert!(
            port.receive_target_prefix_readout_control(
                &mut resident,
                &mut crib,
                &pairing,
                pending,
                0,
                &frozen,
                &frozen,
                READING_BITS,
                None,
            )
            .is_err()
        );
        assert_eq!(format!("{resident:?}"), before);
        assert_eq!(crib, old_crib);
    }
    #[test]
    fn retained_receiver_prefix_uses_full_likelihood_once_and_restores_cold() {
        let (port, mut warm, mut crib, pairing, material) = target_opening(false);
        let ring = warm.admitted[0].ring();
        let receiver =
            crate::hnn::receiving::RetainedFibreReceiver::declare(warm.admitted[0].grain())
                .unwrap();
        let frozen = warm.constitution.receiving_map(ring).unwrap().clone();
        for class in [0, 1] {
            let pending = target_pending(&port, &mut warm);
            let slot = &warm.pending[&pending];
            let addresses = slot.ratio.addresses(&[]).unwrap();
            let read = port
                .diagnose_pending_readout_at_receiver(
                    &warm,
                    &pending,
                    &frozen,
                    &receiver,
                    READING_BITS,
                )
                .unwrap();
            let mut expected_population = warm.constitution.population(ring).unwrap().clone();
            expected_population
                .receive(&[
                    ExactInterval::point(read.native_reading.tree_probabilities[class].clone()),
                    read.native_reading
                        .combined_masses_at(READING_BITS)
                        .unwrap()[class]
                        .clone(),
                ])
                .unwrap();
            let mut expected_tree = warm.constitution.landmarks(ring).unwrap().clone();
            expected_tree.receive(&addresses[0], class).unwrap();
            let before_commit = warm.constitution.commit();
            let receipt = port
                .receive_receiver_prefix_continuing(
                    &mut warm, &mut crib, &pairing, pending, class, &receiver, None,
                )
                .unwrap();
            assert_eq!(receipt.producing, read.native_reading);
            assert_eq!(
                warm.constitution.population(ring),
                Some(&expected_population)
            );
            assert_eq!(warm.constitution.landmarks(ring), Some(&expected_tree));
            assert_eq!(warm.constitution.receiving_map(ring), Some(&frozen));
            assert_eq!(warm.constitution.commit(), before_commit);
            assert!(warm.pending.is_empty());
        }
        let saved = warm.continuing_state(0).unwrap();
        let parsed = ContinuingState::from_text(&saved.to_text(), 1 << 40).unwrap();
        let mut cold = port
            .mount_continued(
                &warm.field,
                &Current::at_rest(&warm.field),
                material,
                &parsed,
            )
            .unwrap();
        let mut cold_crib = ObservedCrib::from_unplaced_checkpoint(
            &warm.field,
            cold.current(),
            crib.next_position(),
            &crib.unplaced_checkpoint().unwrap(),
        )
        .unwrap();
        let a = target_pending(&port, &mut warm);
        let b = target_pending(&port, &mut cold);
        let ra = port
            .receive_receiver_prefix_continuing(
                &mut warm, &mut crib, &pairing, a, 3, &receiver, None,
            )
            .unwrap();
        let rb = port
            .receive_receiver_prefix_continuing(
                &mut cold,
                &mut cold_crib,
                &pairing,
                b,
                3,
                &receiver,
                None,
            )
            .unwrap();
        assert_eq!(ra.producing, rb.producing);
        assert_eq!(
            warm.continuing_state(0).unwrap(),
            cold.continuing_state(0).unwrap()
        );
        assert_eq!(crib, cold_crib);
    }

    #[test]
    fn retained_receiver_prefix_foreign_grain_and_late_close_refuse_atomically() {
        for late in [false, true] {
            let (port, mut resident, mut crib, pairing, _) = target_opening(late);
            let pending = target_pending(&port, &mut resident);
            let grain = resident.admitted[0].grain();
            if late {
                crib.entries.push(ObservedCribCell {
                    position: 0,
                    class: resident.field.alphabet(),
                    placement: None,
                });
            }
            let receiver = crate::hnn::receiving::RetainedFibreReceiver::declare(if late {
                grain
            } else {
                2 * grain
            })
            .unwrap();
            let before = format!("{resident:?}");
            let old = crib.clone();
            assert!(
                port.receive_receiver_prefix_continuing(
                    &mut resident,
                    &mut crib,
                    &pairing,
                    pending,
                    0,
                    &receiver,
                    None
                )
                .is_err()
            );
            assert_eq!(format!("{resident:?}"), before);
            assert_eq!(crib, old);
        }
    }
}

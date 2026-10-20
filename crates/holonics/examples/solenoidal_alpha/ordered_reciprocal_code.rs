//! Finite synthetic CODE exterior for the ordered local R response then new-cut source return.
//! Actual observations alone enter R. Gamma remains entailed; there is no language claim.
use super::*;
use holonics::compression::keys::repair::PairRelation;
use holonics::hnn::reference::observed::{ObservedEpochExecution, ObservedEpochProbeState};
use holonics::hnn::reference::reciprocal::*;
use num_traits::Zero;

fn joint(
    positions: [usize; 2],
    testimony: [usize; 2],
    channel: JointChannel,
) -> Result<JointFamily> {
    Ok(JointFamily::declare(
        vec![PairRelation::new(
            1,
            vec![Some(1), Some(0), Some(3), Some(2)],
        )?],
        positions,
        testimony,
        [(0..4).collect(), (0..4).collect()],
        channel,
        JointBound {
            members: 16,
            visits: 64,
        },
    )?
    .0)
}
fn provenance(family: &JointFamily) -> Result<ReturnOrigin> {
    Ok(ReturnOrigin::Entailed {
        family: sha256(family.checkpoint().as_bytes())?,
        menu: "synthetic-sigma".into(),
        channel: "declared-channel".into(),
        source: "actual-synthetic-crib".into(),
    })
}
fn unchanged_upstream(field: &Field, before: &Constitution, after: &Constitution) {
    for g in 0..field.rings().len() {
        assert_eq!(before.source_law(g), after.source_law(g));
        assert_eq!(before.contrast_law(g), after.contrast_law(g));
        assert_eq!(before.standing(g), after.standing(g));
        assert_eq!(before.passive_factor(g), after.passive_factor(g));
        assert_eq!(before.slices(g), after.slices(g));
        assert_eq!(before.resonator(g), after.resonator(g));
        for &offset in field.offsets() {
            assert_eq!(before.pair_port(g, offset), after.pair_port(g, offset));
        }
        assert_eq!(
            before.clock(holonics::hnn::constitution::Locus::SourcePort(g)),
            after.clock(holonics::hnn::constitution::Locus::SourcePort(g))
        );
    }
    for c in 0..field.contacts().len() {
        assert_eq!(before.contact_storage(c), after.contact_storage(c));
        assert_eq!(before.contact_stiffness(c), after.contact_stiffness(c));
        assert_eq!(before.contact_dissipation(c), after.contact_dissipation(c));
        assert_eq!(before.contact_scales(c), after.contact_scales(c));
    }
    assert_eq!(
        before
            .carried_remainders()
            .into_iter()
            .filter(|(l, _, _, _)| *l != holonics::hnn::constitution::Locus::ReceivingMap(2))
            .collect::<Vec<_>>(),
        after
            .carried_remainders()
            .into_iter()
            .filter(|(l, _, _, _)| *l != holonics::hnn::constitution::Locus::ReceivingMap(2))
            .collect::<Vec<_>>()
    );
}
fn check_local(receipt: &holonics::hnn::reference::observed::ObservedEpochReceipt) {
    assert_eq!(
        receipt.deposition_scope,
        ObservedEpochDepositionScope::LocalReceivingReturn
    );
    assert_eq!(
        receipt.probe_state,
        ObservedEpochProbeState::NotRequestedLocalPolicy
    );
    assert!(!receipt.joint_attempted);
    assert!(
        receipt.comparison.is_none()
            && receipt.receiving_only_comparison.is_none()
            && receipt.joint_comparison.is_none()
    );
    assert!(
        receipt.wall.whole_stage.is_none()
            && receipt.wall.whole_probe.is_none()
            && receipt.wall.joint_stage.is_none()
            && receipt.wall.joint_probe.is_none()
            && receipt.wall.receiving_only_probe.is_none()
    );
    assert!(receipt.wall.probe_subphases.is_empty());
    assert!(receipt.retained_section_return.is_some());
    assert!(receipt.energy.deposition_work == Rat::zero() && !receipt.energy.physical_form_changed);
}
fn read_now(
    reference: &Reference,
    resident: &Resident,
    crib: &ObservedCrib,
    pairing: &PairingDeclaration,
    prior: &ExactRatMatrix,
) -> Result<holonics::hnn::receiving::cells::diagnostic::RetainedReceiverDiagnostic> {
    let receiver =
        holonics::hnn::receiving::RetainedFibreReceiver::declare(resident.admitted()[0].grain())?;
    Ok(fibre_prefix_read(
        reference,
        resident,
        crib,
        pairing,
        &[],
        prior,
        &receiver,
        holonics::ratio::exponentiated::READING_BITS,
    )?)
}

pub(super) fn ordered(execution: &dyn ObservedEpochExecution) -> Result<String> {
    let started = Instant::now();
    let (field, opening, pairing) = declaration(16384)?;
    let reference = port();
    let source_prior = opening.source_port(0).ok_or("source")?.clone();
    let receiving_prior = opening.receiving_map(2).ok_or("receiver")?.clone();
    let mut resident = reference.mount_with(&field, &Current::at_rest(&field), opening.clone())?;
    resident.select_receiving_law(holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1)?;
    let boundary = PairedObservation::admit(&field, resident.constitution(), &pairing)?;
    reference.ingest(&mut resident, None, &boundary.encode(&[])?)?;
    let mut crib = ObservedCrib::new(0);
    for class in [0, 1] {
        reference.ingest_class_continuing(&mut resident, &mut crib, &pairing, class, None)?;
    }
    // Actual same-Word physical motion, without a fitting transaction, before the first token.
    let (moment, _) = resident.continuing().ok_or("moment")?;
    let phases = resident.admitted()[0].clone();
    let (pending, _) = reference.refine(&mut resident, &moment, &phases)?;
    reference.discard(&mut resident, Handle::Pending(pending))?;
    let family = joint([0, 1], [0, 1], JointChannel::Exact)?;
    let origin = provenance(&family)?;
    let stale = reference.bind_source_return(
        &resident,
        &crib,
        &pairing,
        &source_prior,
        0,
        &family,
        origin.clone(),
    )?;
    let before = resident.constitution().clone();
    let ingress = [2, 3, 3, 2, 1, 0, 0, 1]; // Together with actual0,1, the first actual10-cell section.
    let first = reference.observe_epoch_continuing_at_cuts_with_scope(
        &mut resident,
        &mut crib,
        &pairing,
        &ingress,
        None,
        &[ingress.len()],
        false,
        execution,
        ObservedEpochDepositionScope::LocalReceivingReturn,
    )?;
    check_local(&first);
    let (_, blind, blind_crib) = &first.prefixes[0];
    assert_eq!(resident.current(), blind.current());
    assert_eq!(resident.carried(), blind.carried());
    assert_eq!(resident.moment(&moment), blind.moment(&moment));
    assert_eq!(&crib, blind_crib);
    let mut stream = ObservedStream::new(
        resident,
        crib,
        ObservedEpochDepositionScope::LocalReceivingReturn,
    )?;
    unchanged_upstream(&field, &before, stream.resident().constitution());
    // R has consumed the section; an E token from its predecessor must refuse, atomically.
    let mut stale_target = stream.resident().clone();
    let exact_before = stale_target.continuing_state(0)?;
    assert!(
        stale
            .publish(&reference, &mut stale_target, stream.crib())
            .is_err()
    );
    assert_eq!(stale_target.continuing_state(0)?, exact_before);
    // Empty delivery is not a second observation, including after cold restoration.
    let saved = stream.resident().continuing_state(0)?;
    assert!(
        stream
            .receive_with_execution(&reference, &pairing, &[], execution)?
            .epochs
            .is_empty()
    );
    assert_eq!(stream.resident().continuing_state(0)?, saved);
    let packed = ReciprocalCheckpoint::capture(&stream, &family, origin.clone(), 0)?.to_text();
    assert!(packed.contains("local-receiving-return-v1"));
    let checkpoint = ReciprocalCheckpoint::from_text(
        &packed,
        packed.len(),
        MATERIAL_BIT_BUDGET,
        JointBound {
            members: 16,
            visits: 64,
        },
    )?;
    let mut cold = checkpoint.restore(&reference, &field, opening.clone())?;
    assert_eq!(
        cold.scope(),
        ObservedEpochDepositionScope::LocalReceivingReturn
    );
    assert!(
        cold.receive_with_execution(&reference, &pairing, &[], execution)?
            .epochs
            .is_empty()
    );
    assert_eq!(cold.resident().continuing_state(0)?, saved);
    let r_map = stream
        .resident()
        .constitution()
        .receiving_map(2)
        .ok_or("R")?
        .clone();
    assert_ne!(
        r_map, receiving_prior,
        "synthetic local response must actually move R"
    );
    let r_read = read_now(
        &reference,
        stream.resident(),
        stream.crib(),
        &pairing,
        &receiving_prior,
    )?;
    assert!(
        r_read
            .native_minus_control_masses
            .iter()
            .any(|d| d.lower > Rat::zero() || d.upper < Rat::zero()),
        "R movement must reach same-law probability"
    );
    let before_e = stream.resident().clone();
    let e = stream.return_source_relation(
        &reference,
        &pairing,
        &source_prior,
        0,
        &family,
        origin.clone(),
    )?;
    let ReciprocalOutcome::Published(e) = e else {
        return Err("new-cut source common packet held".into());
    };
    assert_ne!(
        stream.resident().constitution().source_port(0),
        before_e.constitution().source_port(0)
    );
    assert_eq!(
        stream.resident().constitution().receiving_law(2),
        before_e.constitution().receiving_law(2)
    );
    assert_eq!(stream.resident().current(), before_e.current());
    assert_eq!(stream.resident().carried(), before_e.carried());
    assert_eq!(
        stream.resident().constitution().landmarks(2),
        before_e.constitution().landmarks(2)
    );
    assert_eq!(
        stream.resident().constitution().population(2),
        before_e.constitution().population(2)
    );
    // Matched E-held same-cut diagnostic: identical R/tree/population/current/carry and read law.
    let e_read = read_now(
        &reference,
        stream.resident(),
        stream.crib(),
        &pairing,
        &receiving_prior,
    )?;
    let e_only_delta = e_read
        .native
        .native_masses
        .iter()
        .zip(&r_read.native.native_masses)
        .map(|(a, b)| holonics::ratio::algebraic::ExactInterval {
            lower: &a.lower - &b.upper,
            upper: &a.upper - &b.lower,
        })
        .collect::<Vec<_>>();
    let e_separated = e_only_delta
        .iter()
        .any(|d| d.lower > Rat::zero() || d.upper < Rat::zero());
    let diagnostic_key = rat(1, 2); // Fixed CODE key, unrelated to targets/observations.
    let r_draw = holonics::receiver::release::draw(&r_read.native.native_masses, &diagnostic_key)?;
    let e_draw = holonics::receiver::release::draw(&e_read.native.native_masses, &diagnostic_key)?;

    assert!(
        stream
            .return_source_relation(
                &reference,
                &pairing,
                &source_prior,
                0,
                &family,
                origin.clone()
            )
            .is_err()
    );
    let r_and_e = ReciprocalCheckpoint::capture(&stream, &family, origin.clone(), 0)?.to_text();
    let restored = ReciprocalCheckpoint::from_text(
        &r_and_e,
        r_and_e.len(),
        MATERIAL_BIT_BUDGET,
        JointBound {
            members: 16,
            visits: 64,
        },
    )?;
    let mut restored = restored.restore(&reference, &field, opening.clone())?;
    assert!(
        restored
            .return_source_relation(&reference, &pairing, &source_prior, 0, &family, origin)
            .is_err()
    );
    // Actual six pending cells survive combined cold checkpoint, then exactly four new arrivals
    // close the actual ten-cell epoch. No old pending class is replayed as a new observation.
    let pending_six = [2, 3, 3, 2, 1, 0];
    let a = stream.receive_with_execution(&reference, &pairing, &pending_six, execution)?;
    let b = restored.receive_with_execution(&reference, &pairing, &pending_six, execution)?;
    assert!(a.epochs.is_empty() && b.epochs.is_empty());
    assert_eq!(a.pending, 6);
    let six = ReciprocalCheckpoint::capture(&stream, &family, provenance(&family)?, 0)?.to_text();
    let mut cold_six = ReciprocalCheckpoint::from_text(
        &six,
        six.len(),
        MATERIAL_BIT_BUDGET,
        JointBound {
            members: 16,
            visits: 64,
        },
    )?
    .restore(&reference, &field, opening)?;
    let four = [0, 0, 0, 0];
    let warm = stream.receive_with_execution(&reference, &pairing, &four, execution)?;
    let cold = cold_six.receive_with_execution(&reference, &pairing, &four, execution)?;
    assert_eq!(warm.published, 10);
    assert_eq!(cold.published, 10);
    check_local(&warm.epochs[0]);
    check_local(&cold.epochs[0]);
    assert_eq!(
        stream.resident().continuing_state(0)?,
        cold_six.resident().continuing_state(0)?
    );
    assert_eq!(stream.pending_checkpoint(), cold_six.pending_checkpoint());
    // The input/current has changed, so the prior immutable token cannot be recycled.
    let after_read = read_now(
        &reference,
        stream.resident(),
        stream.crib(),
        &pairing,
        &receiving_prior,
    )?;
    let changed_r = receiving_prior
        .entries()
        .iter()
        .zip(r_map.entries())
        .enumerate()
        .filter(|(_, (a, b))| a != b)
        .map(|(i, (a, b))| {
            (
                i / receiving_prior.columns(),
                i % receiving_prior.columns(),
                a,
                b,
            )
        })
        .collect::<Vec<_>>();
    println!(
        "V93_ORDERED_TRACE {}",
        object(&[
            (
                "kind",
                quoted("synthetic CODE local-R then new-cut E; not language")
            ),
            (
                "actual_input_classes",
                exact(&[0, 1, 2, 3, 3, 2, 1, 0, 0, 1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0])
            ),
            ("actual_Gamma", exact(family.members())),
            ("R_changed_row_column_old_new", exact(&changed_r)),
            ("R_actual_features", exact(&first.precision.features)),
            (
                "R_actual_shared_return",
                exact(&first.retained_section_return)
            ),
            (
                "same_law_R_native_minus_founding",
                exact(&r_read.native_minus_control_masses)
            ),
            ("E_only_same_cut_native_mass_delta", exact(&e_only_delta)),
            ("E_only_interval_separated", e_separated.to_string()),
            ("same_cut_key", rational(&diagnostic_key)),
            ("R_keyed_draw", exact(&r_draw)),
            ("E_keyed_draw", exact(&e_draw)),
            (
                "R_publication_preserves_actual_blind_current_carry_moment_crib",
                "true".into()
            ),
            (
                "native_real_wave_at_R",
                exact(&r_read.coarse.native_wave_logits)
            ),
            (
                "post_ordered_next_native_wave",
                exact(&after_read.coarse.native_wave_logits)
            ),
            (
                "post_ordered_next_masses",
                exact(&after_read.native.native_masses)
            ),
            ("source_packet", exact(&e.packet)),
            ("source_slip_before", rational(&e.slip_before)),
            ("source_slip_after", rational(&e.slip_after)),
            ("E_commit_current_carry_preserved", "true".into()),
            ("cold_exact", "true".into()),
            ("finite_comparisons_requested", "0".into()),
            ("R_whole_joint_setups", "0".into()),
            (
                "same_section_rebind_api",
                quoted("none: consuming observed ingress; empty delivery no-op warm/cold")
            ),
            ("R_epoch_phase_timings", exact(&first.wall)),
            ("elapsed_ns", started.elapsed().as_nanos().to_string()),
            ("processed_actual_arrivals", "20".into()),
            ("processed_base4_bytes", "5".into()),
            ("prelude_actual_arrivals_without_R", "2".into()),
            ("R_consumed_actual_arrivals", "18".into()),
            ("cold_control_repeated_arrivals", "10".into()),
            (
                "diagnostic_extra_calls",
                quoted(
                    "three explicit finite CODE diagnostics; existing coarse+fine overhead retained; low-level root/transfer counts not instrumented"
                )
            )
        ])
    );
    Ok(format!(
        "{}\n{}",
        stream.resident().continuing_state(0)?.to_text(),
        stream.pending_checkpoint()
    ))
}
#[test]
fn host_ordered_local_receiving_then_source() -> Result<()> {
    ordered(&holonics::hnn::reference::observed::HostObservedEpochExecution).map(|_| ())
}

fn fresh_at(
    testimony: [usize; 2],
) -> Result<(
    Field,
    Constitution,
    PairingDeclaration,
    Reference,
    Resident,
    ObservedCrib,
)> {
    let (field, opening, pairing) = declaration(16384)?;
    let reference = port();
    let mut resident = reference.mount_with(&field, &Current::at_rest(&field), opening.clone())?;
    resident.select_receiving_law(holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1)?;
    let boundary = PairedObservation::admit(&field, resident.constitution(), &pairing)?;
    reference.ingest(&mut resident, None, &boundary.encode(&[])?)?;
    let mut crib = ObservedCrib::new(0);
    for class in testimony {
        reference.ingest_class_continuing(&mut resident, &mut crib, &pairing, class, None)?;
    }
    let (moment, _) = resident.continuing().ok_or("moment")?;
    let phases = resident.admitted()[0].clone();
    let (pending, _) = reference.refine(&mut resident, &moment, &phases)?;
    reference.discard(&mut resident, Handle::Pending(pending))?;
    Ok((field, opening, pairing, reference, resident, crib))
}
#[test]
fn ambiguity_holds_source_but_local_R_and_actual_ingress_continue() -> Result<()> {
    let (field, opening, pairing, reference, resident, crib) = fresh_at([0, 2])?;
    let prior = opening.source_port(0).ok_or("source")?.clone();
    let family = joint([0, 1], [0, 2], JointChannel::AtMostOneChanged)?;
    let mut stream = ObservedStream::new(
        resident,
        crib,
        ObservedEpochDepositionScope::LocalReceivingReturn,
    )?;
    let held = stream.return_source_relation(
        &reference,
        &pairing,
        &prior,
        0,
        &family,
        provenance(&family)?,
    )?;
    assert!(matches!(held, ReciprocalOutcome::Hold { branches: 2 }));
    let before = stream.resident().clone();
    let old = reference.bind_source_return(
        stream.resident(),
        stream.crib(),
        &pairing,
        &prior,
        0,
        &family,
        provenance(&family)?,
    )?;
    let first = stream.receive(&reference, &pairing, &[3, 3, 3, 2, 1, 0, 0, 1])?;
    check_local(&first.epochs[0]);
    assert_ne!(before.current(), stream.resident().current());
    assert_ne!(before.carried(), stream.resident().carried());
    assert_ne!(
        before.constitution().receiving_law(2),
        stream.resident().constitution().receiving_law(2)
    );
    assert_eq!(family.members().len(), 2);
    let mut stale = stream.resident().clone();
    assert!(old.publish(&reference, &mut stale, stream.crib()).is_err());
    assert!(matches!(
        stream.return_source_relation(
            &reference,
            &pairing,
            &prior,
            0,
            &family,
            provenance(&family)?
        )?,
        ReciprocalOutcome::Hold { branches: 2 }
    ));
    // Actual class3 at address2 reached this section above. Its signed clock is exactly
    // one source turn after address1, as declared by the relation; a distant address10
    // was correctly refused in the preserved first attempt. Never weaken this guard.
    let (separated, _) =
        reference.refine_joint_exact_return(stream.resident(), stream.crib(), &family, 0, 2)?;
    assert_eq!(separated.members().len(), 1);
    assert!(
        reference
            .bind_source_return(
                stream.resident(),
                stream.crib(),
                &pairing,
                &prior,
                0,
                &separated,
                ReturnOrigin::Observed
            )
            .is_err()
    );
    let outcome = stream.return_source_relation(
        &reference,
        &pairing,
        &prior,
        0,
        &separated,
        provenance(&separated)?,
    )?;
    assert!(matches!(outcome, ReciprocalOutcome::Published(_)));
    let checkpoint =
        ReciprocalCheckpoint::capture(&stream, &separated, provenance(&separated)?, 0)?.to_text();
    let cold = ReciprocalCheckpoint::from_text(
        &checkpoint,
        checkpoint.len(),
        MATERIAL_BIT_BUDGET,
        JointBound {
            members: 16,
            visits: 64,
        },
    )?
    .restore(&reference, &field, opening)?;
    assert_eq!(
        cold.resident().continuing_state(0)?,
        stream.resident().continuing_state(0)?
    );
    assert_eq!(
        cold.scope(),
        ObservedEpochDepositionScope::LocalReceivingReturn
    );
    println!(
        "V93_ORDERED_AMBIGUITY {}",
        object(&[
            ("Gamma_before", exact(family.members())),
            ("Gamma_after_actual_class3_at2", exact(separated.members())),
            ("actual_ingress_continues", "true".into()),
            ("branch_specific_native_material_evolution", "false".into()),
            ("source_hold_is_not_ingress_freeze", "true".into())
        ])
    );
    Ok(())
}

// Counts actual selected owner calls. Root/log/kernel/transfer counts are not inferred.
#[derive(Default)]
struct CountedHost {
    forwards: std::sync::atomic::AtomicUsize,
    returns: std::sync::atomic::AtomicUsize,
    aggregates: std::sync::atomic::AtomicUsize,
    late_refuse: bool,
}
impl ObservedEpochExecution for CountedHost {
    fn forward(
        &self,
        f: &Field,
        c: &Constitution,
        r: &holonics::hnn::pending::PendingRatio,
        ch: &mut holonics::hnn::chart::Charts,
        o: &holonics::hnn::word::WordOpening,
    ) -> std::result::Result<holonics::hnn::reference::observed::ObservedEpochForwardWord, HnnError>
    {
        let out = holonics::hnn::reference::observed::HostObservedEpochExecution
            .forward(f, c, r, ch, o)?;
        self.forwards
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Ok(out)
    }
    fn forward_scoped(
        &self,
        c: &mut holonics::hnn::reference::observed::ObservedEpochForwardContext<'_, '_>,
        r: &holonics::hnn::pending::PendingRatio,
        ch: &mut holonics::hnn::chart::Charts,
        o: &holonics::hnn::word::WordOpening,
    ) -> std::result::Result<holonics::hnn::reference::observed::ObservedEpochForwardWord, HnnError>
    {
        let out = holonics::hnn::reference::observed::HostObservedEpochExecution
            .forward_scoped(c, r, ch, o)?;
        self.forwards
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Ok(out)
    }
    fn pull_back(
        &self,
        w: holonics::hnn::word::Word<'_>,
        g: &holonics::hnn::ratio::RatioCovector,
        m: &ExactRatMatrix,
        p: &holonics::hnn::receiving::ReceivingPhases,
    ) -> std::result::Result<holonics::hnn::port::WordReturn, HnnError> {
        let out =
            holonics::hnn::reference::observed::HostObservedEpochExecution.pull_back(w, g, m, p)?;
        self.returns
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Ok(out)
    }
    fn aggregate_records(
        &self,
        l: holonics::hnn::constitution::LinearLocus,
        r: usize,
        c: usize,
        g: u32,
        n: u64,
        e: u64,
        h: u64,
        records: &[holonics::hnn::constitution::EpochProducerRecordReading],
    ) -> std::result::Result<holonics::hnn::constitution::EpochRecordFlowReading, HnnError> {
        assert_eq!(
            l,
            holonics::hnn::constitution::LinearLocus::Receiving(2),
            "local policy must never prepare upstream normal records"
        );
        let out = holonics::hnn::reference::observed::HostObservedEpochExecution
            .aggregate_records(l, r, c, g, n, e, h, records)?;
        self.aggregates
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        if self.late_refuse {
            return Err(HnnError::Unadmitted {
                reason: "synthetic late R aggregate refusal",
            });
        }
        Ok(out)
    }
}
#[test]
fn actual_owner_counts_and_late_return_refusal_are_atomic() -> Result<()> {
    let execution = CountedHost::default();
    ordered(&execution)?;
    let load = |n: &std::sync::atomic::AtomicUsize| n.load(std::sync::atomic::Ordering::Relaxed);
    assert_eq!(
        (
            load(&execution.forwards),
            load(&execution.returns),
            load(&execution.aggregates)
        ),
        (28, 28, 3)
    );
    let (_, _, pairing, reference, resident, crib) = fresh_at([0, 1])?;
    let mut stream = ObservedStream::new(
        resident,
        crib,
        ObservedEpochDepositionScope::LocalReceivingReturn,
    )?;
    let before = stream.resident().continuing_state(0)?;
    let before_pending = stream.pending_checkpoint();
    let before_crib = stream.crib().unplaced_checkpoint()?;
    let late = CountedHost {
        late_refuse: true,
        ..Default::default()
    };
    assert!(
        stream
            .receive_with_execution(&reference, &pairing, &[2, 3, 3, 2, 1, 0, 0, 1], &late)
            .is_err()
    );
    assert_eq!(stream.resident().continuing_state(0)?, before);
    assert_eq!(stream.pending_checkpoint(), before_pending);
    assert_eq!(stream.crib().unplaced_checkpoint()?, before_crib);
    assert_eq!(load(&late.aggregates), 1);
    println!(
        "V93_ORDERED_OWNER_COUNTS forwards=28 actual_Word_returns=28 aggregates=3 upstream_aggregates=0 late_refusal_atomic=true additional_global_finite_probe_calls=0 low_level_root_log_kernel_transfer_sync_counters=unmeasured"
    );
    Ok(())
}

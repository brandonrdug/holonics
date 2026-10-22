//! Shared CODE-only exterior: same reciprocal successor followed by six actual native arrivals.
//! No training corpus, target scorer, score-fitting transaction or selected response branch.
use super::*;
use holonics::compression::keys::repair::PairRelation;
use holonics::hnn::reference::reciprocal::*;

pub(super) fn continuity(
    execution: &dyn holonics::hnn::reference::observed::ObservedEpochExecution,
) -> Result<String> {
    let started = Instant::now();
    let (field, opening, pairing) = declaration(16384)?;
    let prior = opening.source_port(0).ok_or("fixture source port")?.clone();
    let reference = port();
    let mut resident = reference.mount_with(&field, &Current::at_rest(&field), opening.clone())?;
    resident.select_receiving_law(holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1)?;
    let boundary = PairedObservation::admit(&field, &opening, &pairing)?;
    reference.ingest(&mut resident, None, &boundary.encode(&[])?)?;
    let mut crib = ObservedCrib::new(0);
    for class in [0, 1] {
        reference.ingest_class_continuing(&mut resident, &mut crib, &pairing, class, None)?;
    }
    let relation = PairRelation::new(1, vec![Some(1), Some(0), Some(3), Some(2)])?;
    let (family, _) = JointFamily::declare(
        vec![relation],
        [0, 1],
        [0, 1],
        [(0..4).collect(), (0..4).collect()],
        JointChannel::Exact,
        JointBound {
            members: 16,
            visits: 64,
        },
    )?;
    let origin = ReturnOrigin::Entailed {
        family: sha256(family.checkpoint().as_bytes())?,
        menu: "synthetic-sigma".into(),
        channel: "exact-witnesses".into(),
        source: sha256(resident.continuing_state(0)?.to_text().as_bytes())?,
    };
    let mut stream = ObservedStream::restore(
        resident,
        crib,
        ObservedEpochDepositionScope::NormalMaps,
        vec![0, 1, 2, 3, 0, 1],
    )?;
    let before_stream = stream.clone();
    let receipt =
        stream.return_source_relation(&reference, &pairing, &prior, 0, &family, origin.clone())?;
    let ReciprocalOutcome::Published(reading) = receipt else {
        return Err("the common CODE packet held".into());
    };
    let packed = ReciprocalCheckpoint::capture(&stream, &family, origin, 0)?.to_text();
    let cold = ReciprocalCheckpoint::from_text(
        &packed,
        packed.len(),
        MATERIAL_BIT_BUDGET,
        JointBound {
            members: 16,
            visits: 64,
        },
    )?;
    let restored = cold.restore(&reference, &field, opening)?;
    assert_eq!(restored.pending_classes(), stream.pending_classes());
    // This executes the same no-deposition physical continuation on the selected executor.
    let (warm, crib) = stream.query_fork_with_execution(&reference, &pairing, execution)?;
    let (cold, cold_crib) = restored.query_fork_with_execution(&reference, &pairing, execution)?;
    assert_eq!(warm.continuing_state(0)?, cold.continuing_state(0)?);
    assert_eq!(crib, cold_crib);
    assert_eq!(family.members().len(), 1);
    let (control, control_crib) =
        before_stream.query_fork_with_execution(&reference, &pairing, execution)?;
    let after_port = stream
        .resident()
        .constitution()
        .source_port(0)
        .ok_or("successor source port")?;
    let changed = prior
        .entries()
        .iter()
        .zip(after_port.entries())
        .enumerate()
        .filter(|(_, (a, b))| a != b)
        .map(|(i, (a, b))| {
            (
                i / prior.columns(),
                i % prior.columns(),
                a.clone(),
                b.clone(),
            )
        })
        .collect::<Vec<_>>();
    println!(
        "V93_INSPECTABLE_TRACE {}",
        object(&[
            ("kind", quoted("synthetic CODE control; not language")),
            ("actual_input_classes", "[0,1,0,1,2,3,0,1]".into()),
            ("packet", exact(&reading.packet)),
            ("Gamma", exact(family.members())),
            ("changed_source_entries_row_column_old_new", exact(&changed)),
            ("local_slip_before", rational(&reading.slip_before)),
            ("local_slip_after", rational(&reading.slip_after)),
            (
                "commit_current_preserved",
                (stream.resident().current() == before_stream.resident().current()).to_string()
            ),
            (
                "commit_carry_preserved",
                (stream.resident().carried() == before_stream.resident().carried()).to_string()
            ),
            ("future_before", exact(&control.carried())),
            ("future_after", exact(&warm.carried())),
            (
                "actual_future_changed",
                (control.carried() != warm.carried()).to_string()
            ),
            (
                "same_actual_future_crib",
                (control_crib == crib).to_string()
            ),
            ("cold_matches_warm", "true".into()),
        ])
    );
    assert_ne!(control.carried(), warm.carried());
    eprintln!(
        "V93_SHARED_CONTINUITY elapsed_ns={} actual_arrivals=8 pending_at_source_publication=6 source_paired_batches={} normal_preparations={} slip_before={} slip_after={} cold=true score_fitting_calls=0",
        started.elapsed().as_nanos(),
        reading.paired_batches,
        reading.normal_preparations,
        reading.slip_before,
        reading.slip_after
    );
    Ok(format!(
        "{}\n{}\n{}",
        warm.continuing_state(0)?.to_text(),
        crib.unplaced_checkpoint()?,
        family.checkpoint()
    ))
}

#[test]
fn host_reciprocal_shared_continuity() {
    continuity(&holonics::hnn::reference::observed::HostObservedEpochExecution).unwrap();
}

#[test]
fn inspectable_ambiguous_actual_return_trace() -> Result<()> {
    let (field, opening, pairing) = declaration(16384)?;
    let prior = opening.source_port(0).ok_or("prior")?.clone();
    let reference = port();
    let mut resident = reference.mount_with(&field, &Current::at_rest(&field), opening)?;
    let boundary = PairedObservation::admit(&field, resident.constitution(), &pairing)?;
    reference.ingest(&mut resident, None, &boundary.encode(&[])?)?;
    let mut crib = ObservedCrib::new(0);
    for class in [0, 2] {
        reference.ingest_class_continuing(&mut resident, &mut crib, &pairing, class, None)?;
    }
    let (family, _) = JointFamily::declare(
        vec![PairRelation::new(
            1,
            vec![Some(1), Some(0), Some(3), Some(2)],
        )?],
        [0, 1],
        [0, 2],
        [(0..4).collect(), (0..4).collect()],
        JointChannel::AtMostOneChanged,
        JointBound {
            members: 16,
            visits: 64,
        },
    )?;
    let origin = ReturnOrigin::Entailed {
        family: sha256(family.checkpoint().as_bytes())?,
        menu: "sigma".into(),
        channel: "at-most-one-changed".into(),
        source: "synthetic".into(),
    };
    let held = reference
        .bind_source_return(
            &resident,
            &crib,
            &pairing,
            &prior,
            0,
            &family,
            origin.clone(),
        )?
        .publish(&reference, &mut resident, &crib)?;
    assert!(matches!(held, ReciprocalOutcome::Hold { branches: 2 }));
    let before = resident.continuing_state(0)?.to_text();
    let before_lift = resident.current().lift().to_vec();
    reference.ingest_class_continuing(&mut resident, &mut crib, &pairing, 3, None)?;
    let (moment, _) = resident.continuing().ok_or("source")?;
    let phases = resident.admitted()[0].clone();
    let (pending, _) = reference.refine(&mut resident, &moment, &phases)?;
    reference.discard(&mut resident, Handle::Pending(pending))?;
    let (separated, _) = reference.refine_joint_exact_return(&resident, &crib, &family, 0, 2)?;
    let update = reference
        .bind_source_return(&resident, &crib, &pairing, &prior, 0, &separated, origin)?
        .publish(&reference, &mut resident, &crib)?;
    assert!(matches!(update, ReciprocalOutcome::Published(_)));
    println!(
        "V93_INSPECTABLE_TRACE {}",
        object(&[
            (
                "kind",
                quoted("synthetic ambiguous compatibility and actual-return CODE trace")
            ),
            ("actual_input_classes", "[0,2,3]".into()),
            ("Gamma_before_Hold", exact(family.members())),
            (
                "hypothetical_relational_future_before_actual_return",
                exact(&family.relational_future()?)
            ),
            ("observed_return_position", "2".into()),
            ("observed_return_class", "3".into()),
            ("Gamma_after_actual_return", exact(separated.members())),
            ("source_update", exact(&update)),
            ("actual_lift_before", exact(&before_lift)),
            ("actual_lift_after", exact(resident.current().lift())),
            (
                "native_state_advanced",
                (before != resident.continuing_state(0)?.to_text()).to_string()
            ),
            (
                "branch_specific_native_material_evolution",
                quoted("not implemented; no branch was chosen during Hold")
            ),
        ])
    );
    Ok(())
}

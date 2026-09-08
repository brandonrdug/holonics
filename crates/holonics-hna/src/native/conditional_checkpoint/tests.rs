use super::*;
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConditionContactMetric, NativeConstitutiveField, NativeFieldOccurrence, NativeJunctionSeed,
        NativePhaseCurrent, ResidentConstitutiveCurrent, ResidentConstitutiveFibre,
    },
    resident_section::{ResidentGrain, ResidentSectionRest, ResidentSurface},
};

fn point<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    values: &[i64],
) -> holonic_engine::resident_section::ResidentSection<'chart> {
    surface
        .mount_section_rest(
            &ResidentSectionRest::found(
                1,
                values.len(),
                ResidentGrain(0),
                64,
                values.iter().map(|value| (*value, *value)).collect(),
            )
            .unwrap(),
        )
        .unwrap()
}

fn current<'a, 'chart>(
    section: &'a holonic_engine::resident_section::ResidentSection<'chart>,
) -> ResidentConstitutiveCurrent<'a, 'chart> {
    ResidentConstitutiveCurrent::integers(section).unwrap()
}

fn seed(nodes: usize) -> Vec<NativeJunctionSeed> {
    vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        };
        nodes
    ]
}

#[test]
#[ignore = "requires native GPU; checkpoint continuation owns exact resident carriers"]
fn conditional_checkpoint_restores_three_owners_and_capabilities() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let source = point(&surface, &[2, 3]);
    let condition_input = point(&surface, &[5, 7]);
    let receiving = point(&surface, &[-11, 29, 7, -2]);
    let held_input = point(&surface, &[4, -2]);
    let mut relation =
        ResidentConstitutiveFibre::found_bilinear_contact(&surface, 1, 1, 2).unwrap();
    relation
        .advance_bilinear_contact(
            current(&source),
            current(&condition_input),
            Some(current(&receiving)),
        )
        .unwrap();
    let family = relation
        .read_condition_preimage(current(&source), current(&receiving))
        .unwrap();
    let mut condition = relation
        .retain_condition_current(
            current(&held_input),
            ConditionContactMetric::UnitAdmittanceRealification,
        )
        .unwrap();
    condition.contact(&family).unwrap();
    drop(family);

    let predicted = relation
        .advance_bilinear_contact(current(&source), condition.current(), None)
        .unwrap();
    let predicted_reading = predicted.inspect().unwrap().predecessor_reading;
    let mut field = NativeConstitutiveField::found(&surface, seed(2)).unwrap();
    let mut occurrence = NativeFieldOccurrence::entering(vec![]);
    let first = field
        .advance_current_resident(&mut occurrence, predicted.current())
        .unwrap();
    let anchor = field.retain_source(&first.source).unwrap();
    let old_source = first.source;
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("conditional.hna");
    save_conditional_checkpoint(
        &path,
        &relation,
        &condition,
        &field,
        &[Some(&old_source)],
        &[Some(&anchor)],
        &HnaStreamState::default(),
        b"controlled-application",
    )
    .unwrap();
    assert!(save_conditional_checkpoint(
        &path,
        &relation,
        &condition,
        &field,
        &[Some(&old_source)],
        &[Some(&anchor)],
        &HnaStreamState::default(),
        b"must-not-overwrite",
    )
    .is_err());
    let saved = NativeSavedConditionalField::read(&path).unwrap();
    assert_eq!(saved.application(), b"controlled-application");
    assert_eq!(saved.source_slots(), &[Some(0)]);
    assert_eq!(saved.anchor_slots(), &[Some(0)]);

    let mut bytes = std::fs::read(&path).unwrap();
    let original = bytes.clone();
    bytes.truncate(bytes.len() - 1);
    let truncated = directory.path().join("truncated.hna");
    std::fs::write(&truncated, bytes).unwrap();
    assert!(NativeSavedConditionalField::read(&truncated).is_err());
    let mut corrupt = original.clone();
    let middle = corrupt.len() / 2;
    corrupt[middle] ^= 1;
    let corrupt_path = directory.path().join("corrupt.hna");
    std::fs::write(&corrupt_path, corrupt).unwrap();
    assert!(NativeSavedConditionalField::read(&corrupt_path).is_err());
    let trailing = directory.path().join("trailing.hna");
    let mut trailing_bytes = original;
    trailing_bytes.extend_from_slice(b"trailing");
    std::fs::write(&trailing, trailing_bytes).unwrap();
    assert!(NativeSavedConditionalField::read(&trailing).is_err());

    drop(condition);
    drop(relation);
    drop(field);
    let (
        mut resumed_relation,
        mut resumed_condition,
        mut resumed_field,
        mut sources,
        anchors,
        stream,
        application,
    ) = saved.remount(&surface).unwrap();
    assert_eq!(sources.len(), 1);
    assert_eq!(anchors.len(), 1);
    assert!(sources[0].is_some());
    assert!(anchors[0].is_some());
    assert_eq!(stream, HnaStreamState::default());
    assert_eq!(application, b"controlled-application");

    let later_family = resumed_relation
        .read_condition_preimage(current(&source), current(&receiving))
        .unwrap();
    resumed_condition.contact(&later_family).unwrap();
    assert_eq!(resumed_condition.contacts(), 2);
    let mut old_occurrence = NativeFieldOccurrence::through(
        old_source,
        vec![NativePhaseCurrent::new(2, 0, 1).unwrap(); 2],
    );
    assert!(matches!(
        resumed_field.advance_resident(&mut old_occurrence),
        Err(holonic_engine::native_ecology::constitutive_fibre::ConstitutiveFibreError::ForeignOccurrence)
    ));
    let predicted = resumed_relation
        .advance_bilinear_contact(current(&source), resumed_condition.current(), None)
        .unwrap();
    assert_eq!(
        predicted.inspect().unwrap().predecessor_reading,
        predicted_reading
    );
    let mut linked = NativeFieldOccurrence::through(sources[0].take().unwrap(), vec![]);
    let linked = resumed_field
        .advance_current_resident(&mut linked, predicted.current())
        .unwrap();
    assert_eq!(linked.lineage.received_from, Some(0));
    let mut continued = NativeFieldOccurrence::through_anchor(
        anchors[0].as_ref().unwrap(),
        vec![NativePhaseCurrent::new(2, 0, 1).unwrap(); 2],
    );
    resumed_field.advance_resident(&mut continued).unwrap();
    assert_eq!(resumed_field.occurrence_count(), 3);
}

#[test]
#[ignore = "requires native GPU; composition rejects unequal relation receiver and field widths"]
fn conditional_checkpoint_rejects_unequal_receiver_dimensions() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let relation = ResidentConstitutiveFibre::found_bilinear_contact(&surface, 1, 1, 2).unwrap();
    let held_input = point(&surface, &[1, 0]);
    let condition = relation
        .retain_condition_current(
            current(&held_input),
            ConditionContactMetric::UnitAdmittanceRealification,
        )
        .unwrap();
    let field = NativeConstitutiveField::found(&surface, seed(1)).unwrap();
    let directory = tempfile::tempdir().unwrap();
    let error = save_conditional_checkpoint(
        directory.path().join("mismatch.hna"),
        &relation,
        &condition,
        &field,
        &[],
        &[],
        &HnaStreamState::default(),
        &[],
    )
    .unwrap_err();
    assert!(matches!(error, ConditionalCheckpointError::Composition(_)));
}

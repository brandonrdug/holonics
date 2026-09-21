use super::*;
use num_rational::BigRational as Rat;
#[path = "../../../../examples/support/linked_torus_field.rs"]
mod linked_torus_field;

fn spec() -> NativeFieldSourceSpec {
    let geometry = linked_torus_field::linked_torus_field_spec(1, 1, 1).unwrap();
    NativeFieldSourceSpec {
        receiver: geometry.slot_junctions[1],
        geometry,
    }
}
fn field<'c>(surface: &'c ResidentSurface<'c>) -> NativeConstitutiveField<'c> {
    let mut field = NativeConstitutiveField::found_with_enclosed_junction(
        surface,
        vec![NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        }],
        ResidentGrain(32),
    )
    .unwrap();
    let first = field
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::new(2, 0, 1).unwrap(),
        ]))
        .unwrap();
    field
        .advance_resident(&mut NativeFieldOccurrence::through(
            first.source,
            vec![NativePhaseCurrent::new(-1, 1, 1).unwrap()],
        ))
        .unwrap();
    field
}
fn preparation<'c>(
    session: &NativeFieldSession<'c, NativeFieldSources<'c>>,
    shift: i64,
) -> ResidentSection<'c> {
    let n = session.incidence().preparation_complex();
    let values = (0..n)
        .flat_map(|i| {
            [
                Rat::from_integer((i as i64 % 3 + shift).into()),
                Rat::from_integer((i as i64 % 2).into()),
            ]
        })
        .collect::<Vec<_>>();
    session
        .surface
        .mount_exact_rational_packet(&values)
        .unwrap()
}
fn target<'c>(surface: &'c ResidentSurface<'c>, values: &[i64]) -> ResidentSection<'c> {
    surface
        .mount_exact_rational_packet(
            &values
                .iter()
                .map(|v| Rat::from_integer((*v).into()))
                .collect::<Vec<_>>(),
        )
        .unwrap()
}

#[test]
#[ignore = "requires CUDA; actual incidence/pre-target cut, field formation and continuation across remount"]
fn native_source_retains_pre_target_condition_and_same_field_after_reopen() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut session =
        NativeFieldSession::from_native_field(&surface, field(&surface), spec()).unwrap();
    let original = preparation(&session, 1);
    let id = session.prepare_native(&original).unwrap();
    let old_condition = surface
        .read_out(&session.presentation.pending[&id].condition)
        .unwrap();
    let second = preparation(&session, 3);
    let second_id = session.prepare_native(&second).unwrap();
    let observed = target(&surface, &[2, 1, -1, 0, 3, -1]);
    session
        .form_native_reaction(
            second_id,
            ResidentConstitutiveCurrent::rational(&observed).unwrap(),
        )
        .unwrap();
    let before = session.generate_native(id, false, false).unwrap();
    let reaction = before.reaction_output().inspect().unwrap();
    let joint = before.joint_output().inspect().unwrap();
    assert_eq!(session.body.normal_observations(), Some(1));
    let mut bytes = Vec::new();
    session.rest_native().unwrap().write(&mut bytes).unwrap();
    drop(before);
    drop(session);
    let saved = NativeSourceSavedSession::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    let mut session = saved.remount(&surface).unwrap();
    assert_eq!(
        surface
            .read_out(&session.presentation.pending[&id].condition)
            .unwrap(),
        old_condition
    );
    let reopened = session.generate_native(id, false, false).unwrap();
    assert_eq!(reopened.reaction_output().inspect().unwrap(), reaction);
    assert_eq!(reopened.joint_output().inspect().unwrap(), joint);
    drop(reopened);
    let wrong = target(&surface, &[1, 0]);
    assert!(
        session
            .form_native_reaction(id, ResidentConstitutiveCurrent::rational(&wrong).unwrap())
            .is_err()
    );
    assert_eq!(session.pending_preparations(), vec![id]);
    assert_eq!(session.body.normal_observations(), Some(1));
    session
        .form_native_reaction(
            id,
            ResidentConstitutiveCurrent::rational(&observed).unwrap(),
        )
        .unwrap();
    assert!(session.pending_preparations().is_empty());
    assert_eq!(session.body.normal_observations(), Some(2));
    assert!(
        session
            .form_native_reaction(
                id,
                ResidentConstitutiveCurrent::rational(&observed).unwrap()
            )
            .is_err()
    );
    let fresh = session.prepare_native(&original).unwrap();
    let current = session.generate_native(fresh, true, true).unwrap();
    let comparison = current.comparison_id().unwrap();
    let current_joint = current.joint_output().inspect().unwrap();
    drop(current);
    let state = session.inspect_native_current().unwrap();
    session.release_native(fresh).unwrap();
    let rest = session.rest_native().unwrap();
    drop(session);
    let mut restored = rest.remount(&surface).unwrap();
    assert_eq!(restored.inspect_native_current().unwrap(), state);
    assert_eq!(restored.body.pending_ids().unwrap(), vec![comparison]);
    restored.release_native_comparison(comparison).unwrap();
    assert!(restored.body.pending_ids().unwrap().is_empty());
    assert!(restored.release_native_comparison(comparison).is_err());
    assert!(
        current_joint.center.len() > 3,
        "continuation retains operative internal coordinates"
    );
    assert!(current_joint.radius >= Rat::from_integer(0.into()));
}

#[test]
#[ignore = "requires CUDA; failed source attachment returns the actual continuing field"]
fn native_source_attachment_refusal_preserves_field_owner_for_retry() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut original = field(&surface);
    let source = original.read_current_source().unwrap();
    let mut bad = spec();
    let receiver = bad.receiver;
    bad.receiver = AnalyticFieldJunctionId(u64::MAX);
    let mut refusal = match NativeFieldSession::from_native_field(&surface, original, bad) {
        Ok(_) => panic!("unadmitted source receiver accepted"),
        Err(refusal) => refusal,
    };
    let retained = refusal.field.read_current_source().unwrap();
    assert!(source.same_owner(&retained));
    assert_eq!(source.field_cut(), retained.field_cut());
    assert_eq!(
        source.enclosure().inspect().unwrap(),
        retained.enclosure().inspect().unwrap()
    );
    refusal.spec.receiver = receiver;
    let session =
        NativeFieldSession::from_native_field(&surface, refusal.field, refusal.spec).unwrap();
    assert_eq!(session.body.roots(), 1);
}

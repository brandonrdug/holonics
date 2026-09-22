use super::*;
use crate::native::coupled_wave::body::field::incident::machine_tests::{
    make_machine_anchor, spec,
};
use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::resident_section::{ResidentGrain, ResidentSurface};
use num_bigint::BigInt;
use relational_geometry::{AffineMap3, Rat, RatVec3, cayley_rotation_z};

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn clock() -> ClockSpec {
    ClockSpec {
        lineage: "receiving-clock".into(),
        duration: rat(1),
        unit: "s".into(),
    }
}

#[test]
fn signed_translation_and_cayley_powers_are_exact_and_checked() {
    let translation = AffineMap3 {
        linear: relational_geometry::RatMat3::identity(),
        translation: RatVec3::from_i64(1, 0, 0),
    };
    assert_eq!(
        signed_affine_power(&translation, -2).unwrap().translation,
        RatVec3::from_i64(-2, 0, 0)
    );
    assert_eq!(
        signed_affine_power(&AffineMap3::identity(), i64::MIN).unwrap(),
        AffineMap3::identity()
    );
    let cayley = AffineMap3 {
        linear: cayley_rotation_z(&(rat(1) / rat(2))),
        translation: RatVec3::zero(),
    };
    let forward = signed_affine_power(&cayley, 2).unwrap();
    let round_trip = forward.followed_by(&signed_affine_power(&forward, -1).unwrap());
    assert_eq!(round_trip, AffineMap3::identity());
}

#[test]
fn invalid_binding_rejects_missing_ports_and_nonpositive_clock() {
    let binding = GeneratorPhaseReceiverBinding {
        receiver_id: "boundary-receiver".into(),
        ports: vec![],
        clock: ClockSpec {
            lineage: "receiving-clock".into(),
            duration: rat(0),
            unit: "s".into(),
        },
        aperture: 0,
        termination_receiver_id: "boundary-termination".into(),
    };
    assert!(binding.validate().is_err());
}

#[test]
fn phase_binding_wire_roundtrips_and_refuses_a_legacy_slot_tag() {
    let binding = GeneratorPhaseReceiverBinding {
        receiver_id: "text".into(),
        termination_receiver_id: "stop".into(),
        ports: vec![GeneratorPhasePort {
            site_id: "b".into(),
            origin_exponent: -1,
            step_exponent: 2,
        }],
        clock: clock(),
        aperture: 3,
    };
    let mut wire = serde_json::to_value(&binding).unwrap();
    assert_eq!(wire["kind"], "generator-phases");
    assert_eq!(
        serde_json::from_value::<GeneratorPhaseReceiverBinding>(wire.clone()).unwrap(),
        binding
    );
    wire["kind"] = serde_json::json!("slots");
    assert!(serde_json::from_value::<GeneratorPhaseReceiverBinding>(wire).is_err());
}

#[test]
#[ignore = "requires CUDA; receiver endpoint, changed phase action, and complete adjoint return"]
fn receiving_uses_generated_endpoint_and_returns_full_machine_boundary() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let grain = ResidentGrain(48);
    let mut spec = spec();
    let mut sites = spec.machine.sites().to_vec();
    sites[1].phase.step = AffineMap3 {
        linear: cayley_rotation_z(&(rat(1) / rat(2))),
        translation: RatVec3::new(rat(0), rat(0), rat(1) / rat(4)),
    };
    sites[1].phase.period = None;
    let step = sites[1].phase.step.clone();
    spec.machine = crate::native::field_geometry::machine::GeneratorMachineSpec::declare(
        spec.machine.frame(),
        spec.machine.units().clone(),
        sites,
        spec.machine.arcs().to_vec(),
        spec.machine.cells().to_vec(),
    )
    .unwrap();
    let mut body = NativeCoupledBody::found_generator_field(&surface, spec, grain).unwrap();
    let anchor = make_machine_anchor(&surface, grain, 0);
    let held = vec![false; anchor.view().components() / 2];
    let prepared = body.prepare_incident_field(anchor.view(), &held).unwrap();
    let generated = body.publish_incident_field(prepared, false, true).unwrap();
    let binding = GeneratorPhaseReceiverBinding {
        receiver_id: "boundary-receiver".into(),
        ports: vec![GeneratorPhasePort {
            site_id: "b".into(),
            origin_exponent: 1,
            step_exponent: 1,
        }],
        clock: clock(),
        aperture: 2,
        termination_receiver_id: "boundary-termination".into(),
    };
    let wire = serde_json::to_value(&binding).unwrap();
    assert_eq!(wire["kind"], "generator-phases");
    let binding = serde_json::from_value(wire).unwrap();
    let received = generated.receive_generator_phases(binding).unwrap();
    assert_eq!(received.output().rows(), 2);
    assert_eq!(received.output().components(), 12);
    let endpoint = received.output().inspect_rows().unwrap();
    let source = generated.boundary().unwrap().inspect().unwrap();
    let vector = |q: &[holonic_engine::ExactComplexWaveCurrent], offset: usize| {
        RatVec3::new(
            q[offset].real.clone(),
            q[offset + 2].real.clone(),
            q[offset + 4].real.clone(),
        )
    };
    let native = |re: &RatVec3, im: &RatVec3| {
        [&re.x, &im.x, &re.y, &im.y, &re.z, &im.z]
            .into_iter()
            .map(|x| holonic_engine::ExactComplexWaveCurrent::new(x.clone(), rat(0)))
            .collect::<Vec<_>>()
    };
    let qre = vector(&source.center[6..], 0);
    let qim = vector(&source.center[6..], 1);
    let mut returned_re = RatVec3::zero();
    let mut returned_im = RatVec3::zero();
    for (j, row) in endpoint.iter().enumerate() {
        let action = signed_affine_power(&step, (j + 1) as i64).unwrap();
        // Chart law: the current advances by the linear part only; the affine translation
        // (and the initial configuration) act on configuration, not on the current.
        let re = action.linear.apply(&qre);
        let im = action.linear.apply(&qim);
        assert!(row.contains(&native(&re, &im)));
        returned_re = returned_re.add(&action.linear.transpose().apply(&vector(&row.center, 0)));
        returned_im = returned_im.add(&action.linear.transpose().apply(&vector(&row.center, 1)));
    }
    assert_ne!(endpoint[0].center, endpoint[1].center);
    let returned = received.pull_back(received.output()).unwrap();
    assert_eq!(returned.rows(), 2);
    assert_eq!(returned.components(), 12);
    assert!(
        returned
            .row(0)
            .unwrap()
            .inspect()
            .unwrap()
            .contains(&native(&RatVec3::zero(), &RatVec3::zero()))
    );
    assert!(
        returned
            .row(1)
            .unwrap()
            .inspect()
            .unwrap()
            .contains(&native(&returned_re, &returned_im))
    );
    let joint = received.pull_back_joint(received.output()).unwrap();
    assert_eq!(
        joint.view().components(),
        generated.joint_output().components()
    );
    let returned_material = body
        .prepare_incident_material_return(generated.comparison_id().unwrap(), joint.view(), 4)
        .unwrap();
    assert_eq!(
        returned_material.anchor_covector().components(),
        joint.view().components()
    );
}

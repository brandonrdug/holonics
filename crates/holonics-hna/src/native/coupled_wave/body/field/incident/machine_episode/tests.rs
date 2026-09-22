use super::super::machine_tests::spec;
use super::*;
use crate::native::GeneratorPhasePort;
use crate::native::field_geometry::machine::{ClockSpec, GeneratorMachineSpec};
use holonic_engine::native_ecology::constitutive_fibre::ResidentConstitutiveSection;
use holonic_engine::{ExactComplexWaveCurrent, embedding_fiber::ResidentReadout};
use num_traits::{Signed, Zero};
use relational_geometry::{AffineMap3, Rat, RatMat3, RatVec3};

fn r(n: i64) -> Rat {
    Rat::from_integer(n.into())
}
fn setup() -> (GeneratorIncidentFieldSpec, GeneratorSourceBinding) {
    let mut spec = spec();
    spec.source_condition_ports = 1;
    let mut sites = spec.machine.sites().to_vec();
    sites[0].phase.step = AffineMap3 {
        linear: RatMat3::identity(),
        translation: RatVec3::new(r(1) / r(16), r(0), r(0)),
    };
    sites[0].phase.period = None;
    spec.machine = GeneratorMachineSpec::declare(
        spec.machine.frame(),
        spec.machine.units().clone(),
        sites,
        spec.machine.arcs().to_vec(),
        spec.machine.cells().to_vec(),
    )
    .unwrap();
    let source = GeneratorSourceBinding {
        contact_kinds: vec![super::super::GeneratorSourceContactKind::IntraPart],
        source_id: "ordered-input".into(),
        clock: ClockSpec {
            lineage: "input-clock".into(),
            duration: r(1),
            unit: "s".into(),
        },
        clocks: spec
            .machine
            .sites()
            .iter()
            .map(|s| GeneratorPhasePort {
                site_id: s.id.clone(),
                origin_exponent: 0,
                step_exponent: 1,
            })
            .collect(),
        injection_sites: vec!["a".into()],
    };
    (spec, source)
}
fn encoded<'c>(
    surface: &'c ResidentSurface<'c>,
    reverse: bool,
    shift: i64,
) -> Rc<ResidentNormalEnclosureSection<'c>> {
    let mut values = [
        [2048, 512, 1024, 256, 512, 128],
        [512, 256, 3072, 512, 1024, 256],
    ];
    values[0][0] += shift;
    if reverse {
        values.reverse();
    }
    let points = values
        .into_iter()
        .flat_map(|row| row.into_iter().chain([65536]))
        .map(|x| (x, x))
        .collect();
    let section = surface
        .mount_section_rest(
            &ResidentSectionRest::found(2, 7, ResidentGrain(0), 64, points).unwrap(),
        )
        .unwrap();
    Rc::new(
        ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::rationals(&section).unwrap(),
            ResidentGrain(48),
        )
        .unwrap(),
    )
}
fn contacts() -> Vec<GeneratorSourceContact> {
    vec![GeneratorSourceContact {
        from: 0,
        to: 1,
        kind: super::super::GeneratorSourceContactKind::IntraPart,
    }]
}
fn condition_material(body: &mut NativeCoupledBody<'_>) {
    use holonic_engine::native_ecology::constitutive_fibre::NativeNormalPrior;
    let BodyState::Incident(model) = body.state_mut().unwrap() else {
        panic!("machine")
    };
    let grain = model
        .field
        .read_current_source()
        .unwrap()
        .enclosure()
        .grain();
    model.materials = model
        .layout
        .material_features
        .iter()
        .enumerate()
        .map(|(owner, &features)| {
            let mut rows = vec![vec![ExactComplexWaveCurrent::zero(); features]; 6];
            for j in 0..6 {
                rows[j][j] = ExactComplexWaveCurrent::new(r(1) / r(8), r(0));
            }
            let site = model
                .layout
                .sites
                .iter()
                .find(|s| s.material == owner)
                .unwrap();
            let external = 6 + 6 * site.differences.len();
            rows[0][external] = ExactComplexWaveCurrent::new(r(1) / r(16), r(0));
            ResidentNormalMaterial::found_features_with_prior(
                model.field.surface(),
                features,
                6,
                grain,
                NativeNormalPrior::from_coefficients(rows).unwrap(),
            )
            .unwrap()
        })
        .collect();
}
fn dot(a: &[ExactComplexWaveCurrent], b: &[ExactComplexWaveCurrent]) -> Rat {
    a.iter()
        .zip(b)
        .map(|(a, b)| &a.real * &b.real + &a.imaginary * &b.imaginary)
        .sum()
}

#[test]
#[ignore = "requires CUDA; ordered nonlinear episode, full E return and frozen tape rest"]
fn ordered_episode_preserves_order_and_returns_every_source_occurrence() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let (spec, binding) = setup();
    let mut body =
        NativeCoupledBody::found_generator_field(&surface, spec, ResidentGrain(48)).unwrap();
    condition_material(&mut body);
    let original = body.inspect_current().unwrap();
    let source = encoded(&surface, false, 0);
    let generated = body
        .prepare_generator_episode(source.clone(), binding.clone(), 0, contacts())
        .unwrap();
    let forward = generated.joint_output().inspect().unwrap();
    let reversed = body
        .prepare_generator_episode(encoded(&surface, true, 0), binding.clone(), 0, contacts())
        .unwrap();
    assert_ne!(
        forward.center,
        reversed.joint_output().inspect().unwrap().center
    );
    assert_eq!(body.inspect_current().unwrap(), original);
    let generated = body.publish_incident_field(generated, false, true).unwrap();
    let id = generated.comparison_id().unwrap();
    let returned = body
        .prepare_incident_material_return(id, generated.joint_output(), 4)
        .unwrap();
    let ge = returned.source_covector().unwrap();
    assert_eq!((ge.rows(), ge.components()), (2, 6));
    let plus = body
        .prepare_generator_episode(encoded(&surface, false, 1), binding.clone(), 0, contacts())
        .unwrap();
    let minus = body
        .prepare_generator_episode(encoded(&surface, false, -1), binding.clone(), 0, contacts())
        .unwrap();
    let delta = plus
        .joint_output()
        .inspect()
        .unwrap()
        .center
        .iter()
        .zip(minus.joint_output().inspect().unwrap().center)
        .map(|(p, m)| {
            ExactComplexWaveCurrent::new(
                (&p.real - m.real) / r(2),
                (&p.imaginary - m.imaginary) / r(2),
            )
        })
        .collect::<Vec<_>>();
    let direct = dot(&forward.center, &delta);
    let adjoint = ge.row(0).unwrap().inspect().unwrap().center[0].real.clone() / r(65536);
    let residual = (&direct - &adjoint).abs();
    assert!(!adjoint.is_zero());
    assert!(
        residual < adjoint.abs() / r(1000),
        "source tape residual {residual}, forward {direct}, adjoint {adjoint}"
    );
    let BodyState::Incident(model) = body.state().unwrap() else {
        panic!("machine")
    };
    let mut bytes = Vec::new();
    model.rest().unwrap().write(&mut bytes).unwrap();
    assert_eq!(&bytes[..19], b"HNA-INCIDENT-FIELD\x02");
    let rest = NativeIncidentModelRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    let model = rest.remount(&surface).unwrap();
    let mut after = Vec::new();
    model.rest().unwrap().write(&mut after).unwrap();
    assert_eq!(bytes, after);
    let mut restored = NativeCoupledBody {
        state: Some(BodyState::Incident(model)),
    };
    let restored_word = restored.incident_comparison(id).unwrap();
    let restored_return = restored
        .prepare_incident_material_return(id, restored_word.joint_output(), 4)
        .unwrap();
    assert_eq!(
        ge.inspect_rows().unwrap(),
        restored_return
            .source_covector()
            .unwrap()
            .inspect_rows()
            .unwrap()
    );
    restored
        .publish_incident_material_return(restored_return)
        .unwrap();
    assert_eq!(restored.pending_coupled_predictions(), 0);
}

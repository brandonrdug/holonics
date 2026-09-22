use super::*;
use crate::native::field_geometry::GeometricFieldSpec;
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        NativeConstitutiveField, NativeJunctionSeed, NativeNormalPrior, NativePhaseCurrent,
        ResidentConstitutiveSection, ResidentNormalEnclosure, ResidentNormalEnclosureSection,
        ResidentNormalMaterial,
    },
    resident_section::{ResidentGrain, ResidentSectionRest, ResidentSurface},
};
use num_traits::{Signed, Zero};

#[path = "../../../../../examples/support/linked_torus_field.rs"]
mod linked_torus_field;

fn spec() -> IncidentFieldSpec {
    let mut geometry: GeometricFieldSpec =
        linked_torus_field::linked_torus_field_spec(1, 2, 1).unwrap();
    geometry.beta_significand = 0;
    geometry.beta_exponent = 0;
    geometry.series_terms = 1;
    geometry.refinement_steps = 2;
    geometry.relaxation_bits = 2;
    IncidentFieldSpec {
        participation: Default::default(),
        geometry,
        local_roots: 1,
        material_owners: vec![],
        solve_steps: 256,
        solver: IncidentFieldSolver::Richardson,
    }
}

fn model<'c>(surface: &'c ResidentSurface<'c>) -> IncidentFieldModel<'c> {
    let seed = NativeJunctionSeed {
        incoming_admittance: 1,
        held_admittance: 1,
        incoming_transport: NativePhaseCurrent::unit(),
        initial_held: NativePhaseCurrent::zero(),
    };
    let mut field = NativeConstitutiveField::found_with_enclosed_junction(
        surface,
        vec![seed; 7],
        ResidentGrain(32),
    )
    .unwrap();
    let mut model = IncidentFieldModel::new(field, spec()).unwrap();
    let surface = model.field.surface();
    let grain = model
        .field
        .read_current_source()
        .unwrap()
        .enclosure()
        .grain();
    let targets = model.layout.width / 2;
    model.materials = model
        .layout
        .material_features
        .iter()
        .map(|&features| {
            let mut coefficients =
                vec![vec![holonic_engine::ExactComplexWaveCurrent::zero(); features]; targets];
            for (row, values) in coefficients
                .iter_mut()
                .enumerate()
                .take(targets.min(features))
            {
                values[row] = holonic_engine::ExactComplexWaveCurrent::new(
                    num_rational::BigRational::new(1.into(), 4.into()),
                    num_rational::BigRational::zero(),
                );
                let condition = (features - targets) / (targets + 1);
                if condition > 0 {
                    values[targets + row] = holonic_engine::ExactComplexWaveCurrent::new(
                        num_rational::BigRational::new(1.into(), 8.into()),
                        num_rational::BigRational::zero(),
                    );
                    values[targets + condition + row] =
                        holonic_engine::ExactComplexWaveCurrent::new(
                            num_rational::BigRational::new(1.into(), 16.into()),
                            num_rational::BigRational::zero(),
                        );
                }
            }
            let prior = NativeNormalPrior::from_coefficients(coefficients).unwrap();
            ResidentNormalMaterial::found_features_with_prior(
                surface, features, targets, grain, prior,
            )
            .unwrap()
        })
        .collect();
    model
}

fn make_anchor<'c>(
    surface: &'c ResidentSurface<'c>,
    components: usize,
    grain: ResidentGrain,
    shift: i64,
) -> ResidentNormalEnclosure<'c> {
    let values = (0..components / 2)
        .flat_map(|at| {
            let real = (((at as i64) + 1) * 17 << 10) + shift;
            let imaginary = (((at as i64) % 3) * 5 << 10) - shift;
            [(real, real), (imaginary, imaginary)]
        })
        .chain(std::iter::once((65536, 65536)))
        .collect();
    let raw = surface
        .mount_section_rest(
            &ResidentSectionRest::found(1, components + 1, ResidentGrain(0), 64, values).unwrap(),
        )
        .unwrap();
    ResidentNormalEnclosureSection::from_points(
        ResidentConstitutiveSection::rationals(&raw).unwrap(),
        grain,
    )
    .unwrap()
    .row(0)
    .unwrap()
    .to_owned()
    .unwrap()
}

#[test]
#[ignore = "requires CUDA; incident Phi(q,Delta) and participation drive are inspected on the resident word"]
fn incident_phi_uses_query_difference_and_distinct_phase_drive_at_zero_beta() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut model = model(&surface);
    let source = model.field.read_current_source().unwrap();
    let anchor = make_anchor(
        &surface,
        source.boundary_components(),
        source.enclosure().grain(),
        0,
    );
    let held = vec![false; anchor.view().components() / 2];
    let admitted = model
        .layout
        .sites
        .iter()
        .map(|site| vec![true; site.sources.len()])
        .collect();
    let word = model.word(anchor.view(), &held, admitted).unwrap();
    assert_eq!(
        model
            .materials
            .iter()
            .map(|m| m.observations())
            .sum::<u64>(),
        0
    );
    let site = word
        .steps
        .iter()
        .flat_map(|step| step.sites.iter())
        .find(|site| site.condition.is_some())
        .unwrap();
    assert_ne!(
        site.query.row(0).unwrap().inspect().unwrap().center,
        site.condition
            .as_ref()
            .unwrap()
            .row(0)
            .unwrap()
            .inspect()
            .unwrap()
            .center
    );
    assert_ne!(
        site.phase
            .output()
            .row(0)
            .unwrap()
            .inspect()
            .unwrap()
            .center,
        site.query.row(0).unwrap().inspect().unwrap().center
    );
    let scaled = |z: &holonic_engine::ExactComplexWaveCurrent, den: i64| {
        holonic_engine::ExactComplexWaveCurrent::new(
            &z.real / num_rational::BigRational::from_integer(den.into()),
            &z.imaginary / num_rational::BigRational::from_integer(den.into()),
        )
    };
    let mut expected = Vec::new();
    for site in &word.steps[0].sites {
        let q = site.query.row(0).unwrap().inspect().unwrap().center;
        let c = site
            .condition
            .as_ref()
            .map(|c| c.row(0).unwrap().inspect().unwrap().center);
        let neighbors = site.phase.transported_neighbors();
        let mut drive = vec![holonic_engine::ExactComplexWaveCurrent::zero(); q.len()];
        for row in 0..neighbors.rows() {
            for (sum, u) in drive
                .iter_mut()
                .zip(neighbors.row(row).unwrap().inspect().unwrap().center)
            {
                *sum = sum.add(&u);
            }
        }
        for (i, q) in q.iter().enumerate() {
            let mut reaction = scaled(q, 4);
            if let Some(c) = &c {
                reaction = reaction
                    .add(&scaled(&c[i], 8))
                    .add(&scaled(&q.multiply(&c[0]), 16));
            }
            expected.push(scaled(&drive[i], neighbors.rows() as i64).add(&reaction));
        }
    }
    assert!(word.steps[0].input.inspect().unwrap().contains(&expected));
}

#[test]
#[ignore = "requires CUDA; full multi-step incident pullback returns source anchor, material and contact operands"]
fn incident_full_word_pullback_returns_anchor_and_all_stage_operands() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut model = model(&surface);
    let source = model.field.read_current_source().unwrap();
    let anchor = make_anchor(
        &surface,
        source.boundary_components(),
        source.enclosure().grain(),
        0,
    );
    let held = (0..anchor.view().components() / 2)
        .map(|i| i % 3 == 0)
        .collect::<Vec<_>>();
    let admitted = model
        .layout
        .sites
        .iter()
        .map(|site| vec![true; site.sources.len()])
        .collect();
    let word = model.word(anchor.view(), &held, admitted).unwrap();
    let pull = model.pull_back(&word, word.output.view()).unwrap();
    assert_eq!(pull.contacts.len(), model.layout.steps);
    assert_eq!(pull.material.len(), model.materials.len());
    assert!(pull.material.iter().map(Vec::len).sum::<usize>() > 0);
    assert!(
        pull.anchor
            .view()
            .inspect()
            .unwrap()
            .center
            .iter()
            .any(|v| !v.is_zero())
    );

    // At beta=0 this two-stage word is a polynomial of degree at most four along a
    // source direction. Central Richardson cancels its cubic term exactly, so the only
    // tolerance below is the returned numerical enclosure, not an arbitrary epsilon.
    let admitted = model
        .layout
        .sites
        .iter()
        .map(|site| vec![true; site.sources.len()])
        .collect::<Vec<_>>();
    let mut outputs = Vec::new();
    for shift in [64, -64, 32, -32] {
        let point = make_anchor(
            &surface,
            source.boundary_components(),
            source.enclosure().grain(),
            shift,
        );
        outputs.push(
            model
                .word(point.view(), &held, admitted.clone())
                .unwrap()
                .output
                .inspect()
                .unwrap(),
        );
    }
    let g = word.output.inspect().unwrap();
    let gradient = pull.anchor.inspect().unwrap();
    let pairing = |values: &[holonic_engine::ExactComplexWaveCurrent]| {
        g.center
            .iter()
            .zip(values)
            .map(|(a, b)| a.conjugate().multiply(b).real)
            .sum::<num_rational::BigRational>()
    };
    let h = num_rational::BigRational::new(1.into(), 1024.into());
    let two = num_rational::BigRational::from_integer(2.into());
    let three = num_rational::BigRational::from_integer(3.into());
    let four = num_rational::BigRational::from_integer(4.into());
    let coarse = (pairing(&outputs[0].center) - pairing(&outputs[1].center)) / (&h * &two);
    let fine = (pairing(&outputs[2].center) - pairing(&outputs[3].center)) / &h;
    let derivative = (fine * &four - coarse) / &three;
    let direction = holonic_engine::ExactComplexWaveCurrent::new(
        num_rational::BigRational::from_integer(1.into()),
        num_rational::BigRational::from_integer((-1).into()),
    );
    let adjoint = gradient
        .center
        .iter()
        .map(|value| value.conjugate().multiply(&direction).real)
        .sum::<num_rational::BigRational>();
    let g_norm = g
        .center
        .iter()
        .map(|value| value.real.abs() + value.imaginary.abs())
        .sum::<num_rational::BigRational>();
    let coarse_radius = &g_norm * (&outputs[0].radius + &outputs[1].radius) / (&h * &two);
    let fine_radius = &g_norm * (&outputs[2].radius + &outputs[3].radius) / &h;
    let tolerance = (fine_radius * &four + coarse_radius) / &three
        + gradient.radius
            * num_rational::BigRational::from_integer((2 * gradient.center.len()).into());
    assert!((derivative - adjoint).abs() <= tolerance);
}

#[test]
#[ignore = "requires CUDA; preview pending incident word restores its frozen producing cut without changing the continuing current"]
fn incident_pending_restores_frozen_word_and_preview_is_nonmutating() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut model = model(&surface);
    let source = model.field.read_current_source().unwrap();
    let before = source.enclosure().inspect().unwrap();
    let anchor = make_anchor(
        &surface,
        source.boundary_components(),
        source.enclosure().grain(),
        0,
    );
    let prepared = model
        .prepare(anchor.view(), &vec![false; anchor.view().components() / 2])
        .unwrap();
    let generated = model.publish(prepared, false, true).unwrap();
    let output = generated.joint_output().inspect().unwrap();
    assert_eq!(model.generations, 0);
    assert_eq!(model.pending(), 1);
    assert_eq!(
        model
            .field
            .read_current_source()
            .unwrap()
            .enclosure()
            .inspect()
            .unwrap(),
        before
    );
    let restored = model.rest().unwrap().remount(&surface).unwrap();
    assert_eq!(restored.pending(), 1);
    assert_eq!(
        restored
            .pending
            .values()
            .next()
            .unwrap()
            .output
            .inspect()
            .unwrap(),
        output
    );
}

#[test]
fn incident_participation_wire_preserves_legacy_and_tags_quadrance() {
    let legacy = spec();
    let wire = serde_json::to_value(&legacy).unwrap();
    assert!(wire.get("participation").is_none());
    let restored: IncidentFieldSpec = serde_json::from_value(wire).unwrap();
    assert_eq!(restored.participation, IncidentParticipationChart::Bilinear);
    let mut geometric = legacy;
    geometric.participation = IncidentParticipationChart::QuadranceCurrent;
    let wire = serde_json::to_value(&geometric).unwrap();
    assert_eq!(wire["participation"], "quadrance-current");
    assert_eq!(
        serde_json::from_value::<IncidentFieldSpec>(wire).unwrap(),
        geometric
    );
}

#[test]
#[ignore = "requires CUDA; quadrance consumer keeps both source returns and its producing chart through rest"]
fn incident_quadrance_word_retains_complete_return_and_saved_chart() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut model = model(&surface);
    let IncidentModelSpec::Legacy(spec) = &mut model.spec else {
        panic!("legacy test model")
    };
    spec.participation = IncidentParticipationChart::QuadranceCurrent;
    model.layout.participation = IncidentParticipationChart::QuadranceCurrent;
    spec.geometry.beta_significand = 1;
    spec.geometry.beta_exponent = 0;
    model.layout.beta = Dyadic::ONE;
    spec.geometry.series_terms = 40;
    model.layout.series = 40;
    let source = model.field.read_current_source().unwrap();
    let anchor = make_anchor(
        &surface,
        source.boundary_components(),
        source.enclosure().grain(),
        0,
    );
    let held = vec![false; anchor.view().components() / 2];
    let prepared = model.prepare(anchor.view(), &held).unwrap();
    assert!(
        prepared
            .word
            .steps
            .iter()
            .flat_map(|s| &s.sites)
            .all(|s| matches!(s.phase, IncidentParticipationForward::Quadrance(_)))
    );
    let back = model
        .pull_back(&prepared.word, prepared.word.output.view())
        .unwrap();
    assert_eq!(back.contacts.len(), model.layout.steps);
    assert!(
        back.anchor
            .inspect()
            .unwrap()
            .center
            .iter()
            .any(|x| !x.is_zero())
    );
    let generated = model.publish(prepared, false, true).unwrap();
    let before = generated.joint_output().inspect().unwrap();
    let restored = model.rest().unwrap().remount(&surface).unwrap();
    assert!(matches!(&restored.spec, IncidentModelSpec::Legacy(s)
        if s.participation == IncidentParticipationChart::QuadranceCurrent));
    assert_eq!(restored.pending.len(), 1);
    let word = Rc::clone(restored.pending.values().next().unwrap());
    assert_eq!(word.output.inspect().unwrap(), before);
    let restored_back = restored.pull_back(&word, word.output.view()).unwrap();
    assert_eq!(
        restored_back.anchor.inspect().unwrap(),
        back.anchor.inspect().unwrap()
    );
    for (left, right) in restored_back.material.iter().zip(&back.material) {
        assert_eq!(left.len(), right.len());
        for ((lf, lg), (rf, rg)) in left.iter().zip(right) {
            assert_eq!(lf.rest().unwrap(), rf.rest().unwrap());
            assert_eq!(lg.rest().unwrap(), rg.rest().unwrap());
        }
    }
}

#[test]
fn incident_model_wire_preserves_the_legacy_numeric_key_atlas() {
    let legacy = spec();
    let encoded = serde_json::to_string(&IncidentModelSpec::Legacy(legacy.clone())).unwrap();
    assert_eq!(
        serde_json::from_str::<IncidentFieldSpec>(&encoded).unwrap(),
        legacy
    );
    assert_eq!(
        serde_json::from_str::<IncidentModelSpec>(&encoded).unwrap(),
        IncidentModelSpec::Legacy(legacy)
    );
}

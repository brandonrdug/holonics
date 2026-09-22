use super::super::GeneratorSourceContact;
use super::super::machine_tests::spec;
use super::*;
use crate::native::GeneratorPhasePort;
use crate::native::field_geometry::machine::{ClockSpec, GeneratorMachineSpec};
use holonic_engine::native_ecology::constitutive_fibre::ResidentConstitutiveSection;
use holonic_engine::{ExactComplexWaveCurrent, embedding_fiber::ResidentReadout};
use num_traits::{Signed, ToPrimitive, Zero};
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
        offsets: vec![],
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
fn rows_section<'c>(
    surface: &'c ResidentSurface<'c>,
    values: Vec<[i64; 6]>,
) -> Rc<ResidentNormalEnclosureSection<'c>> {
    let rows = values.len();
    let points = values
        .into_iter()
        .flat_map(|row| row.into_iter().chain([65536]))
        .map(|x| (x, x))
        .collect();
    let section = surface
        .mount_section_rest(
            &ResidentSectionRest::found(rows, 7, ResidentGrain(0), 64, points).unwrap(),
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
fn encoded<'c>(
    surface: &'c ResidentSurface<'c>,
    reverse: bool,
    shift: i64,
) -> Rc<ResidentNormalEnclosureSection<'c>> {
    let mut values = vec![
        [2048, 512, 1024, 256, 512, 128],
        [512, 256, 3072, 512, 1024, 256],
    ];
    values[0][0] += shift;
    if reverse {
        values.reverse();
    }
    rows_section(surface, values)
}
/// A passage of `n` cells with bounded, non-periodic-looking row values.
fn passage<'c>(
    surface: &'c ResidentSurface<'c>,
    n: usize,
) -> Rc<ResidentNormalEnclosureSection<'c>> {
    rows_section(
        surface,
        (0..n as i64)
            .map(|k| {
                [
                    512 * (k % 5 + 1),
                    256 * (k % 3 + 1),
                    1024,
                    128 * (k % 7 + 1),
                    512,
                    64 * (k % 2 + 1),
                ]
            })
            .collect(),
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

/// Central-difference pairing of the returned source covector at row 0, component 0.
fn pairing_residual(
    body: &mut NativeCoupledBody<'_>,
    forward: &[ExactComplexWaveCurrent],
    adjoint_row0: &ExactComplexWaveCurrent,
    plus: &NativeIncidentGenerated<'_>,
    minus: &NativeIncidentGenerated<'_>,
) -> (Rat, Rat, Rat) {
    let _ = body;
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
    let direct = dot(forward, &delta);
    let adjoint = adjoint_row0.real.clone() / r(65536);
    let residual = (&direct - &adjoint).abs();
    (direct, adjoint, residual)
}

fn model_bytes(body: &NativeCoupledBody<'_>) -> Vec<u8> {
    let BodyState::Incident(model) = body.state().unwrap() else {
        panic!("machine")
    };
    let mut bytes = Vec::new();
    model.rest().unwrap().write(&mut bytes).unwrap();
    bytes
}

fn restore<'c>(surface: &'c ResidentSurface<'c>, bytes: &[u8]) -> NativeCoupledBody<'c> {
    let rest = NativeIncidentModelRest::read(&mut &bytes[..], bytes.len() as u64).unwrap();
    NativeCoupledBody {
        state: Some(BodyState::Incident(rest.remount(surface).unwrap())),
    }
}

#[test]
#[ignore = "requires CUDA; source moment accumulation, one incident word, transposed return and moment rest"]
fn ordered_moment_preserves_order_and_returns_every_source_occurrence() {
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
    let reversed = reversed.joint_output().inspect().unwrap();
    assert_ne!(forward.center, reversed.center);
    let order_gap = forward
        .center
        .iter()
        .zip(&reversed.center)
        .map(|(a, b)| (&a.real - &b.real).abs() + (&a.imaginary - &b.imaginary).abs())
        .sum::<Rat>();
    eprintln!("MEASURED directional return |ab-ba|_1 = {order_gap}");
    assert_eq!(body.inspect_current().unwrap(), original);
    let operands = generated.generator_moment_operands().unwrap();
    assert_eq!((operands.rows, operands.start), (2, 0));
    assert_eq!(operands.clock_witnesses.len(), 2);
    assert!(operands.condition.is_some());
    let generated = body.publish_incident_field(generated, false, true).unwrap();
    let id = generated.comparison_id().unwrap();
    let retained = body.incident_comparison(id).unwrap();
    let census = retained.retained_operand_census().unwrap();
    assert_eq!(census["solver_iterates"], 0);
    assert_eq!(census["material_views"], 0);
    assert_eq!(census["sections"], 3);
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
    let row0 = ge.row(0).unwrap().inspect().unwrap().center[0].clone();
    let (direct, adjoint, residual) =
        pairing_residual(&mut body, &forward.center, &row0, &plus, &minus);
    eprintln!("MEASURED pairing: direct {direct}, adjoint {adjoint}, residual {residual}");
    assert!(!adjoint.is_zero());
    assert!(
        residual < adjoint.abs() / r(1000),
        "source moment residual {residual}, forward {direct}, adjoint {adjoint}"
    );
    let bytes = model_bytes(&body);
    assert_eq!(&bytes[..19], b"HNA-INCIDENT-FIELD\x03");
    let mut restored = restore(&surface, &bytes);
    assert_eq!(bytes, model_bytes(&restored));
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
    // A retired per-occurrence tape is refused, not reinterpreted.
    let mut tape = bytes.clone();
    tape[18] = 2;
    let refused = NativeIncidentModelRest::read(&mut &tape[..], tape.len() as u64)
        .err()
        .unwrap();
    assert!(refused.to_string().contains("retired"), "{refused}");
}

fn prepare_offset<'c>(
    body: &mut NativeCoupledBody<'c>,
    surface: &'c ResidentSurface<'c>,
    binding: &GeneratorSourceBinding,
    reverse: bool,
    shift: i64,
) -> NativeIncidentGenerated<'c> {
    body.prepare_generator_episode_with_offsets(
        encoded(surface, reverse, shift),
        binding.clone(),
        vec![1],
        0,
        vec![],
    )
    .unwrap()
}

#[test]
#[ignore = "requires CUDA; identity phases leave a plural first-moment fibre that the offset port separates"]
fn identity_actions_separate_order_only_through_the_declared_offset() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let (_, mut binding) = setup();
    binding.contact_kinds.clear();
    let mut plain = spec();
    plain.source_condition_ports = 0;
    let mut body =
        NativeCoupledBody::found_generator_field(&surface, plain, ResidentGrain(48)).unwrap();
    let ab = body
        .prepare_generator_episode(encoded(&surface, false, 0), binding.clone(), 0, vec![])
        .unwrap();
    let ba = body
        .prepare_generator_episode(encoded(&surface, true, 0), binding.clone(), 0, vec![])
        .unwrap();
    assert_eq!(
        ab.joint_output().inspect().unwrap().center,
        ba.joint_output().inspect().unwrap().center,
        "identity phases and no offset: [a,b] and [b,a] share their moment"
    );
    let mut offset = spec();
    offset.source_condition_ports = 1;
    let mut body =
        NativeCoupledBody::found_generator_field(&surface, offset, ResidentGrain(48)).unwrap();
    condition_material(&mut body);
    let ab = prepare_offset(&mut body, &surface, &binding, false, 0);
    let ba = prepare_offset(&mut body, &surface, &binding, true, 0);
    let forward = ab.joint_output().inspect().unwrap();
    let backward = ba.joint_output().inspect().unwrap();
    assert_ne!(forward.center, backward.center);
    let order_gap = forward
        .center
        .iter()
        .zip(&backward.center)
        .map(|(a, b)| (&a.real - &b.real).abs() + (&a.imaginary - &b.imaginary).abs())
        .sum::<Rat>();
    eprintln!("MEASURED identity-phase offset(1) directional return |ab-ba|_1 = {order_gap}");
    let ab = body.publish_incident_field(ab, false, true).unwrap();
    let id = ab.comparison_id().unwrap();
    let returned = body
        .prepare_incident_material_return(id, ab.joint_output(), 4)
        .unwrap();
    let row0 = returned
        .source_covector()
        .unwrap()
        .row(0)
        .unwrap()
        .inspect()
        .unwrap()
        .center[0]
        .clone();
    let plus = prepare_offset(&mut body, &surface, &binding, false, 1);
    let minus = prepare_offset(&mut body, &surface, &binding, false, -1);
    let (direct, adjoint, residual) =
        pairing_residual(&mut body, &forward.center, &row0, &plus, &minus);
    eprintln!("MEASURED offset pairing: direct {direct}, adjoint {adjoint}, residual {residual}");
    assert!(!adjoint.is_zero());
    assert!(residual < adjoint.abs() / r(1000));
}

#[test]
#[ignore = "requires CUDA; a delayed comparison is read through contemporary material, identically across restart"]
fn delayed_comparison_reads_contemporary_material_identically_after_restart() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let (spec, binding) = setup();
    let mut body =
        NativeCoupledBody::found_generator_field(&surface, spec, ResidentGrain(48)).unwrap();
    condition_material(&mut body);
    let first = body
        .prepare_generator_episode(encoded(&surface, false, 0), binding.clone(), 0, contacts())
        .unwrap();
    let first = body.publish_incident_field(first, false, true).unwrap();
    let first_id = first.comparison_id().unwrap();
    // The comparison read before any intervening publication.
    let before_update = body
        .prepare_incident_material_return(first_id, first.joint_output(), 4)
        .unwrap()
        .source_covector()
        .unwrap()
        .inspect_rows()
        .unwrap();
    let second = body
        .prepare_generator_episode(encoded(&surface, true, 0), binding.clone(), 0, contacts())
        .unwrap();
    let second = body.publish_incident_field(second, false, true).unwrap();
    let second_id = second.comparison_id().unwrap();
    let update = body
        .prepare_incident_material_return(second_id, second.joint_output(), 4)
        .unwrap();
    body.publish_incident_material_return(update).unwrap();
    let saved = model_bytes(&body);
    let covector = first.joint_output().to_owned().unwrap();
    let direct = body
        .prepare_incident_material_return(first_id, covector.view(), 4)
        .unwrap();
    let direct_rows = direct.source_covector().unwrap().inspect_rows().unwrap();
    assert_ne!(
        direct_rows, before_update,
        "the delayed return is read through the contemporary material"
    );
    body.publish_incident_material_return(direct).unwrap();
    let direct_after = model_bytes(&body);
    let mut resumed = restore(&surface, &saved);
    let restored = resumed
        .prepare_incident_material_return(first_id, covector.view(), 4)
        .unwrap();
    assert_eq!(
        restored.source_covector().unwrap().inspect_rows().unwrap(),
        direct_rows
    );
    resumed.publish_incident_material_return(restored).unwrap();
    assert_eq!(model_bytes(&resumed), direct_after);
    assert_eq!(resumed.pending_coupled_predictions(), 0);
}

#[test]
#[ignore = "requires CUDA; retained comparison size against source length; prints MEASURED rows"]
fn moment_comparison_storage_is_independent_of_source_length() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut censuses = Vec::new();
    use holonic_engine::native_ecology::constitutive_fibre::NativeEnclosurePropagation as Law;
    for (chained, law) in [
        (false, Law::JointBall),
        (true, Law::JointBall),
        (false, Law::ComponentIntervals),
    ] {
        for n in [2usize, 8, 32, 128] {
            let (mut spec, binding) = setup();
            spec.enclosure_propagation = law;
            let mut body =
                NativeCoupledBody::found_generator_field(&surface, spec, ResidentGrain(48))
                    .unwrap();
            condition_material(&mut body);
            let contacts = if chained {
                (0..n - 1)
                    .map(|k| GeneratorSourceContact {
                        from: k,
                        to: k + 1,
                        kind: super::super::GeneratorSourceContactKind::IntraPart,
                    })
                    .collect()
            } else {
                vec![]
            };
            let source = passage(&surface, n);
            let empty = model_bytes(&body).len();
            let started = std::time::Instant::now();
            let generated = body
                .prepare_generator_episode(source, binding, 0, contacts)
                .unwrap();
            let generated = body.publish_incident_field(generated, false, true).unwrap();
            let request_us = started.elapsed().as_micros();
            let id = generated.comparison_id().unwrap();
            let rest = model_bytes(&body);
            assert_eq!(&rest[..19], b"HNA-INCIDENT-FIELD\x03");
            let census = body
                .incident_comparison(id)
                .unwrap()
                .retained_operand_census()
                .unwrap();
            let covector = generated.joint_output().to_owned().unwrap();
            let sup = |values: Vec<ExactComplexWaveCurrent>| {
                values
                    .iter()
                    .map(|v| v.real.abs().max(v.imaginary.abs()))
                    .fold(r(0), |a, b| a.max(b))
            };
            let accumulated = sup(generated
                .generator_moment_operands()
                .unwrap()
                .accumulated
                .inspect()
                .unwrap()
                .center);
            let output = sup(covector.inspect().unwrap().center);
            eprintln!(
                "MEASURED law={law:?} contacts={} N={n} sup|accumulated|={:.4e} sup|output|={:.4e}",
                if chained { "chain" } else { "none" },
                accumulated.to_f64().unwrap(),
                output.to_f64().unwrap()
            );
            let started = std::time::Instant::now();
            let returned = body
                .prepare_incident_material_return(id, covector.view(), 4)
                .unwrap();
            assert_eq!(returned.source_covector().unwrap().rows(), n);
            let source_sup = sup(returned
                .source_covector()
                .unwrap()
                .inspect_rows()
                .unwrap()
                .into_iter()
                .flat_map(|row| row.center)
                .collect());
            let rows = returned.source_covector().unwrap().inspect_rows().unwrap();
            let radius = rows
                .iter()
                .map(|row| row.radius.clone())
                .fold(r(0), |a, b| a.max(b));
            eprintln!(
                "MEASURED N={n} sup|source covector|={:.4e} sup radius={:.4e} (row0 {:.4e}, last {:.4e})",
                source_sup.to_f64().unwrap(),
                radius.to_f64().unwrap(),
                rows[0].radius.to_f64().unwrap(),
                rows[n - 1].radius.to_f64().unwrap()
            );
            body.publish_incident_material_return(returned).unwrap();
            let observe_us = started.elapsed().as_micros();
            eprintln!(
                "MEASURED law={law:?} contacts={} N={n} rest_bytes={} pending_bytes={} held_sections={} held_octets={} solver_iterates={} material_views={} request_us={request_us} observe_us={observe_us}",
                if chained { "chain" } else { "none" },
                rest.len(),
                rest.len() - empty,
                census["sections"],
                census["octets"],
                census["solver_iterates"],
                census["material_views"],
            );
            censuses.push((chained, rest.len() - empty, census));
        }
    }
    let plain = censuses[..4].iter().collect::<Vec<_>>();
    for row in &plain {
        assert_eq!(row.2["sections"], plain[0].2["sections"]);
        assert_eq!(row.2["octets"], plain[0].2["octets"]);
        // Only the decimal digits of the recorded passage length differ.
        assert!(
            row.1.abs_diff(plain[0].1) <= 4,
            "{} vs {}",
            row.1,
            plain[0].1
        );
    }
}

#[test]
#[ignore = "requires CUDA; closed-form accumulation equals repeated per-step source maps"]
fn closed_form_accumulation_equals_repeated_steps() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let (spec, binding) = setup();
    let mut body =
        NativeCoupledBody::found_generator_field(&surface, spec, ResidentGrain(48)).unwrap();
    let BodyState::Incident(model) = body.state_mut().unwrap() else {
        panic!("machine")
    };
    let machine = model.layout.machine.clone().unwrap();
    let start = model
        .field
        .read_current_source()
        .unwrap()
        .enclosure()
        .to_owned()
        .unwrap();
    let n = 9;
    let cells = passage(&surface, n);
    let maps = |count| {
        super::super::machine_source::MachineSourceMaps::new(
            &surface,
            &machine,
            &binding,
            0,
            count,
            ResidentGrain(48),
        )
        .unwrap()
    };
    let stepper = maps(n);
    let mut stepped = start.view().to_owned().unwrap();
    for k in 0..n {
        let row = Rc::new(cells.row(k).unwrap().as_section().unwrap());
        stepped = stepper
            .apply(stepped.view(), row)
            .unwrap()
            .output()
            .to_owned()
            .unwrap();
    }
    let closed = maps(n)
        .accumulate(start.view(), &cells)
        .unwrap()
        .into_output();
    let stepped = stepped.inspect().unwrap();
    let closed = closed.inspect().unwrap();
    let gap = stepped
        .center
        .iter()
        .zip(&closed.center)
        .map(|(a, b)| (&a.real - &b.real).abs() + (&a.imaginary - &b.imaginary).abs())
        .sum::<Rat>();
    eprintln!(
        "MEASURED closed-form vs {n} steps: |gap|_1 = {gap}, radius stepped {}, closed {}",
        stepped.radius, closed.radius
    );
    assert!(gap <= &stepped.radius + &closed.radius);
}

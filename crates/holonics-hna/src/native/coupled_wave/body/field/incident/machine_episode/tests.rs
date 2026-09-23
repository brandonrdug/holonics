use super::super::GeneratorSourceContact;
use super::super::machine_tests::spec;
use super::*;
use crate::native::GeneratorPhasePort;
use crate::native::field_geometry::machine::{ClockSpec, GeneratorMachineSpec};
use holonic_engine::native_ecology::constitutive_fibre::ResidentConstitutiveSection;
use holonic_engine::{ExactComplexWaveCurrent, embedding_fiber::ResidentReadout};
use num_traits::{Signed, ToPrimitive, Zero};
use relational_geometry::{AffineMap3, Rat, RatVec3, cayley_rotation_z};

fn r(n: i64) -> Rat {
    Rat::from_integer(n.into())
}
fn setup() -> (GeneratorIncidentFieldSpec, GeneratorSourceBinding) {
    let mut spec = spec();
    spec.source_condition_ports = 1;
    let mut sites = spec.machine.sites().to_vec();
    // A nonidentity Cayley quarter-parameter rotation on the injection site, so each cell's
    // composite phase L^(N−1−k) differs from its neighbours'.
    sites[0].phase.step = AffineMap3 {
        linear: cayley_rotation_z(&(r(1) / r(2))),
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
/// A word over the alphabet `a, b, c`, one fixed encoded row per symbol.
fn word<'c>(
    surface: &'c ResidentSurface<'c>,
    text: &str,
) -> Rc<ResidentNormalEnclosureSection<'c>> {
    rows_section(
        surface,
        text.chars()
            .map(|c| match c {
                'a' => [2048, 512, 1024, 256, 512, 128],
                'b' => [512, 256, 3072, 512, 1024, 256],
                'c' => [1024, 2048, 256, 128, 256, 1024],
                _ => panic!("alphabet"),
            })
            .collect(),
    )
}
fn l1_gap(a: &[ExactComplexWaveCurrent], b: &[ExactComplexWaveCurrent]) -> Rat {
    a.iter()
        .zip(b)
        .map(|(a, b)| (&a.real - &b.real).abs() + (&a.imaginary - &b.imaginary).abs())
        .sum::<Rat>()
}
fn prepare_plain<'c>(
    body: &mut NativeCoupledBody<'c>,
    surface: &'c ResidentSurface<'c>,
    binding: &GeneratorSourceBinding,
    reverse: bool,
    shift: i64,
) -> NativeIncidentGenerated<'c> {
    body.prepare_generator_episode(encoded(surface, reverse, shift), binding.clone(), 0, vec![])
        .unwrap()
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
#[ignore = "requires CUDA; source moment under a rotating phase, one incident word, transposed return and moment rest"]
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
    let order_gap = l1_gap(&forward.center, &reversed.center);
    eprintln!("MEASURED directional return |ab-ba|_1 = {order_gap}");
    assert_eq!(body.inspect_current().unwrap(), original);
    let operands = generated.generator_moment_operands().unwrap();
    assert_eq!((operands.rows, operands.start), (2, 0));
    assert_eq!(operands.clock_witnesses.len(), 2);
    assert_eq!(operands.contact_counts, &[1]);
    assert!(operands.condition.is_some());
    let generated = body.publish_incident_field(generated, false, true).unwrap();
    let id = generated.comparison_id().unwrap();
    // No producing word is retained: the census holds no field cut, material view or iterate.
    let census = body.generator_comparison_census(id).unwrap();
    assert_eq!(census["solver_iterates"], 0);
    assert_eq!(census["material_views"], 0);
    assert_eq!(census["field_cuts"], 0);
    assert_eq!(census["sections"], 2);
    // A passage that pooled directed contacts needs its declared relation to return.
    assert!(
        body.prepare_incident_material_return(id, generated.joint_output(), 4)
            .is_err()
    );
    let contemporary = generated.contemporary_output(&mut body).unwrap();
    assert_eq!(
        contemporary.joint_output().inspect().unwrap(),
        forward,
        "nothing published in between: the contemporary reading is the producing one"
    );
    let returned = body
        .prepare_generator_material_return(&contemporary, generated.joint_output(), 4, &contacts())
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
    eprintln!(
        "MEASURED rotating-phase pairing: direct {direct}, adjoint {adjoint}, residual {residual}, relative {:.3e}",
        (&residual / adjoint.abs()).to_f64().unwrap()
    );
    assert!(!adjoint.is_zero());
    assert!(
        residual < adjoint.abs() / r(1000),
        "source moment residual {residual}, forward {direct}, adjoint {adjoint}"
    );
    let bytes = model_bytes(&body);
    assert_eq!(&bytes[..19], b"HNA-INCIDENT-FIELD\x04");
    let mut restored = restore(&surface, &bytes);
    assert_eq!(bytes, model_bytes(&restored));
    let restored_word = restored.contemporary_incident_comparison(id).unwrap();
    let restored_return = restored
        .prepare_generator_material_return(&restored_word, generated.joint_output(), 4, &contacts())
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
    // The retired per-occurrence tape and the retired producing-anchor form are refused.
    for (tag, word) in [(2u8, "retired"), (3u8, "retired")] {
        let mut old = bytes.clone();
        old[18] = tag;
        let refused = NativeIncidentModelRest::read(&mut &old[..], old.len() as u64)
            .err()
            .unwrap();
        assert!(refused.to_string().contains(word), "{refused}");
    }
}

#[test]
#[ignore = "requires CUDA; a rotating phase separates abca from acba without any contact port"]
fn rotating_phase_separates_permuted_passages_without_contacts() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let (mut rotating, mut binding) = setup();
    binding.contact_kinds.clear();
    rotating.source_condition_ports = 0;
    let mut identity = spec();
    identity.source_condition_ports = 0;
    let mut gaps = Vec::new();
    for (name, spec) in [("identity", identity), ("rotation", rotating)] {
        let mut body =
            NativeCoupledBody::found_generator_field(&surface, spec, ResidentGrain(48)).unwrap();
        let abca = body
            .prepare_generator_episode(word(&surface, "abca"), binding.clone(), 0, vec![])
            .unwrap();
        let acba = body
            .prepare_generator_episode(word(&surface, "acba"), binding.clone(), 0, vec![])
            .unwrap();
        let moment_gap = l1_gap(
            &abca
                .generator_moment_operands()
                .unwrap()
                .moment
                .inspect()
                .unwrap()
                .center,
            &acba
                .generator_moment_operands()
                .unwrap()
                .moment
                .inspect()
                .unwrap()
                .center,
        );
        let output_gap = l1_gap(
            &abca.joint_output().inspect().unwrap().center,
            &acba.joint_output().inspect().unwrap().center,
        );
        eprintln!(
            "MEASURED phase={name} |m(abca)-m(acba)|_1 = {:.6e}, |y(abca)-y(acba)|_1 = {:.6e}",
            moment_gap.to_f64().unwrap(),
            output_gap.to_f64().unwrap()
        );
        gaps.push((moment_gap, output_gap));
    }
    assert!(
        gaps[0].0.is_zero() && gaps[0].1.is_zero(),
        "identity phase: one multiset fibre"
    );
    assert!(
        !gaps[1].0.is_zero() && !gaps[1].1.is_zero(),
        "rotation separates order"
    );
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
    binding.offsets = vec![1];
    // The offsets are owned by the binding; a different separate list is refused.
    assert!(
        body.prepare_generator_episode_with_offsets(
            encoded(&surface, false, 0),
            binding.clone(),
            vec![2],
            0,
            vec![]
        )
        .is_err()
    );
    let mut offset = spec();
    offset.source_condition_ports = 1;
    let mut body =
        NativeCoupledBody::found_generator_field(&surface, offset, ResidentGrain(48)).unwrap();
    condition_material(&mut body);
    let ab = prepare_plain(&mut body, &surface, &binding, false, 0);
    let ba = prepare_plain(&mut body, &surface, &binding, true, 0);
    let forward = ab.joint_output().inspect().unwrap();
    let backward = ba.joint_output().inspect().unwrap();
    assert_ne!(forward.center, backward.center);
    let order_gap = l1_gap(&forward.center, &backward.center);
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
    let plus = prepare_plain(&mut body, &surface, &binding, false, 1);
    let minus = prepare_plain(&mut body, &surface, &binding, false, -1);
    let (direct, adjoint, residual) =
        pairing_residual(&mut body, &forward.center, &row0, &plus, &minus);
    eprintln!("MEASURED offset pairing: direct {direct}, adjoint {adjoint}, residual {residual}");
    assert!(!adjoint.is_zero());
    assert!(residual < adjoint.abs() / r(1000));
}

#[test]
#[ignore = "requires CUDA; a delayed comparison is one fresh word at the contemporary constitution, identically across restart"]
fn delayed_comparison_reads_contemporary_constitution_identically_after_restart() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let (spec, binding) = setup();
    let mut body =
        NativeCoupledBody::found_generator_field(&surface, spec, ResidentGrain(48)).unwrap();
    condition_material(&mut body);
    let first = body
        .prepare_generator_episode(encoded(&surface, false, 0), binding.clone(), 0, contacts())
        .unwrap();
    let producing = first.joint_output().inspect().unwrap();
    let first = body.publish_incident_field(first, false, true).unwrap();
    let first_id = first.comparison_id().unwrap();
    let covector = first.joint_output().to_owned().unwrap();
    // An intervening passage moves the current (commit) and the material (its return).
    let second = body
        .prepare_generator_episode(encoded(&surface, true, 0), binding.clone(), 0, contacts())
        .unwrap();
    let second = body.publish_incident_field(second, true, true).unwrap();
    let second_id = second.comparison_id().unwrap();
    let second_word = body.contemporary_incident_comparison(second_id).unwrap();
    let update = body
        .prepare_generator_material_return(&second_word, second.joint_output(), 4, &contacts())
        .unwrap();
    body.publish_incident_material_return(update).unwrap();
    let saved = model_bytes(&body);
    let contemporary = first.contemporary_output(&mut body).unwrap();
    let fresh = body
        .prepare_generator_episode(encoded(&surface, false, 0), binding.clone(), 0, contacts())
        .unwrap();
    let delayed = contemporary.joint_output().inspect().unwrap();
    assert_eq!(
        delayed,
        fresh.joint_output().inspect().unwrap(),
        "the delayed reading is one fresh word at the contemporary constitution"
    );
    assert_eq!(
        contemporary
            .generator_moment_operands()
            .unwrap()
            .moment
            .inspect()
            .unwrap(),
        fresh
            .generator_moment_operands()
            .unwrap()
            .moment
            .inspect()
            .unwrap(),
        "the same source moment m"
    );
    assert_ne!(delayed, producing, "the constitution moved in between");
    eprintln!(
        "MEASURED delayed vs producing |y_now - y_then|_1 = {:.6e}",
        l1_gap(&delayed.center, &producing.center).to_f64().unwrap()
    );
    let direct = body
        .prepare_generator_material_return(&contemporary, covector.view(), 4, &contacts())
        .unwrap();
    let direct_rows = direct.source_covector().unwrap().inspect_rows().unwrap();
    body.publish_incident_material_return(direct).unwrap();
    let direct_after = model_bytes(&body);
    let mut resumed = restore(&surface, &saved);
    let resumed_word = resumed.contemporary_incident_comparison(first_id).unwrap();
    assert_eq!(resumed_word.joint_output().inspect().unwrap(), delayed);
    let restored = resumed
        .prepare_generator_material_return(&resumed_word, covector.view(), 4, &contacts())
        .unwrap();
    assert_eq!(
        restored.source_covector().unwrap().inspect_rows().unwrap(),
        direct_rows
    );
    resumed.publish_incident_material_return(restored).unwrap();
    assert_eq!(model_bytes(&resumed), direct_after);
    assert_eq!(resumed.pending_coupled_predictions(), 0);
    // After that publication the resumed reading is stale and is refused.
    let mut stale = restore(&surface, &saved);
    let stale_word = stale.contemporary_incident_comparison(first_id).unwrap();
    let third = stale
        .prepare_generator_episode(encoded(&surface, false, 0), binding.clone(), 0, contacts())
        .unwrap();
    stale.publish_incident_field(third, true, false).unwrap();
    assert!(
        stale
            .prepare_generator_material_return(&stale_word, covector.view(), 4, &contacts())
            .is_err()
    );
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
        (true, Law::ComponentIntervals),
    ] {
        for n in [2usize, 8, 32, 128] {
            let (mut spec, binding) = setup();
            spec.enclosure_propagation = law.clone();
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
                .prepare_generator_episode(source, binding, 0, contacts.clone())
                .unwrap();
            let generated = body.publish_incident_field(generated, false, true).unwrap();
            let request_us = started.elapsed().as_micros();
            let id = generated.comparison_id().unwrap();
            let rest = model_bytes(&body);
            assert_eq!(&rest[..19], b"HNA-INCIDENT-FIELD\x04");
            let census = body.generator_comparison_census(id).unwrap();
            let covector = generated.joint_output().to_owned().unwrap();
            let sup = |values: Vec<ExactComplexWaveCurrent>| {
                values
                    .iter()
                    .map(|v| v.real.abs().max(v.imaginary.abs()))
                    .fold(r(0), |a, b| a.max(b))
            };
            let moment = sup(generated
                .generator_moment_operands()
                .unwrap()
                .moment
                .inspect()
                .unwrap()
                .center);
            let output = sup(covector.inspect().unwrap().center);
            eprintln!(
                "MEASURED law={law:?} contacts={} N={n} sup|m|={:.4e} sup|output|={:.4e}",
                if chained { "chain" } else { "none" },
                moment.to_f64().unwrap(),
                output.to_f64().unwrap()
            );
            let started = std::time::Instant::now();
            let contemporary = generated.contemporary_output(&mut body).unwrap();
            let returned = body
                .prepare_generator_material_return(&contemporary, covector.view(), 4, &contacts)
                .unwrap();
            assert_eq!(returned.source_covector().unwrap().rows(), n);
            let rows = returned.source_covector().unwrap().inspect_rows().unwrap();
            let radius = rows
                .iter()
                .map(|row| row.radius.clone())
                .fold(r(0), |a, b| a.max(b));
            eprintln!(
                "MEASURED N={n} sup|source covector|={:.4e} sup radius={:.4e}",
                sup(rows.iter().flat_map(|row| row.center.clone()).collect())
                    .to_f64()
                    .unwrap(),
                radius.to_f64().unwrap(),
            );
            body.publish_incident_material_return(returned).unwrap();
            let observe_us = started.elapsed().as_micros();
            eprintln!(
                "MEASURED law={law:?} contacts={} N={n} rest_bytes={} pending_bytes={} held_sections={} held_octets={} solver_iterates={} material_views={} field_cuts={} request_us={request_us} observe_us={observe_us}",
                if chained { "chain" } else { "none" },
                rest.len(),
                rest.len() - empty,
                census["sections"],
                census["octets"],
                census["solver_iterates"],
                census["material_views"],
                census["field_cuts"],
            );
            censuses.push((chained, rest.len() - empty, census));
        }
    }
    for group in censuses.chunks(4) {
        for row in group {
            assert_eq!(row.2["sections"], group[0].2["sections"]);
            assert_eq!(row.2["octets"], group[0].2["octets"]);
            // Only the decimal digits of the passage length and contact count differ.
            assert!(
                row.1.abs_diff(group[0].1) <= 8,
                "{} vs {}",
                row.1,
                group[0].1
            );
        }
    }
}

#[test]
#[ignore = "requires CUDA; closed-form accumulation equals repeated per-step source maps under a rotating phase"]
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
    let closed = maps(n).accumulate(start.view(), &cells).unwrap();
    let stepped = stepped.inspect().unwrap();
    let closed = closed.inspect().unwrap();
    let gap = l1_gap(&stepped.center, &closed.center);
    eprintln!(
        "MEASURED closed-form vs {n} rotating steps: |gap|_1 = {gap}, radius stepped {}, closed {}",
        stepped.radius, closed.radius
    );
    assert!(gap <= &stepped.radius + &closed.radius);
}

#[test]
#[ignore = "requires CUDA; a target passage accumulates through the same maps without a word and is received through the same phases"]
fn target_moment_accumulates_without_a_word_and_receives_through_the_same_phases() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let (spec, binding) = setup();
    let mut body =
        NativeCoupledBody::found_generator_field(&surface, spec, ResidentGrain(48)).unwrap();
    condition_material(&mut body);
    let before = model_bytes(&body);
    let target = body
        .accumulate_generator_moment(word(&surface, "abca"), &binding)
        .unwrap();
    assert_eq!(
        model_bytes(&body),
        before,
        "no current, material or pending change"
    );
    let produced = body
        .prepare_generator_episode(word(&surface, "abca"), binding.clone(), 0, vec![])
        .unwrap();
    let operands = produced.generator_moment_operands().unwrap();
    assert_eq!(
        target.moment().inspect().unwrap(),
        operands.moment.inspect().unwrap()
    );
    assert_eq!(
        target.accumulated().inspect().unwrap(),
        operands.accumulated.inspect().unwrap()
    );
    assert_eq!(target.source_rows(), 4);
    let receiver = GeneratorPhaseReceiverBinding {
        receiver_id: "text".into(),
        termination_receiver_id: "stop".into(),
        ports: vec![GeneratorPhasePort {
            site_id: "b".into(),
            origin_exponent: 0,
            step_exponent: 1,
        }],
        clock: ClockSpec {
            lineage: "receiving-clock".into(),
            duration: r(1),
            unit: "s".into(),
        },
        aperture: 3,
    };
    let received = body
        .receive_moment_phases(&target, receiver.clone())
        .unwrap();
    assert_eq!(
        (received.output().rows(), received.output().components()),
        (3, 12)
    );
    // The same receiving maps read the accumulated field of an ordinary generator word.
    let control = NativeIncidentGenerated {
        word: Rc::new(IncidentWord {
            source_moment: None,
            boundary: None,
            external_condition: None,
            machine: produced.word.machine.clone(),
            source: produced.word.source.retained_clone(),
            material: Vec::new(),
            anchor: Rc::clone(&produced.word.anchor),
            held: produced.word.held.clone(),
            admitted: Vec::new(),
            steps: Vec::new(),
            output: produced.word.anchor.view().to_owned().unwrap(),
            epoch: produced.word.epoch,
            solver: produced.word.solver,
            solve_steps: produced.word.solve_steps,
            enclosure_propagation: produced.word.enclosure_propagation.clone(),
        }),
        comparison: None,
    }
    .receive_generator_phases(receiver)
    .unwrap();
    assert_eq!(
        received.output().inspect_rows().unwrap(),
        control.output().inspect_rows().unwrap()
    );
}

fn table<'c>(
    surface: &'c ResidentSurface<'c>,
    shift: i64,
) -> Rc<ResidentNormalEnclosureSection<'c>> {
    let mut rows = vec![
        [2048, 512, 1024, 256, 512, 128],
        [512, 256, 3072, 512, 1024, 256],
        [1024, 2048, 256, 128, 256, 1024],
    ];
    rows[0][0] += shift;
    rows_section(surface, rows)
}
/// An encoder table over `alphabet` symbols; symbols 0..3 match `table(_, 0)`.
fn wide_table<'c>(
    surface: &'c ResidentSurface<'c>,
    alphabet: usize,
) -> Rc<ResidentNormalEnclosureSection<'c>> {
    let base = [
        [2048, 512, 1024, 256, 512, 128],
        [512, 256, 3072, 512, 1024, 256],
        [1024, 2048, 256, 128, 256, 1024],
    ];
    rows_section(
        surface,
        (0..alphabet as i64)
            .map(|a| {
                base.get(a as usize).copied().unwrap_or([
                    512 * (a % 5 + 1),
                    256 * (a % 3 + 1),
                    1024,
                    128 * (a % 7 + 1),
                    512,
                    64 * (a % 2 + 1),
                ])
            })
            .collect(),
    )
}
fn symbols_of(text: &str) -> Vec<usize> {
    text.chars().map(|c| c as usize - 'a' as usize).collect()
}
fn chain(n: usize) -> Vec<GeneratorSourceContact> {
    (0..n - 1)
        .map(|k| GeneratorSourceContact {
            from: k,
            to: k + 1,
            kind: super::super::GeneratorSourceContactKind::IntraPart,
        })
        .collect()
}

#[test]
#[ignore = "requires CUDA; a symbol passage is retained as per-symbol sums and read at one contemporary cut including the encoder"]
fn symbol_passage_reads_the_contemporary_encoder_at_one_cut() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let (spec, binding) = setup();
    let mut body =
        NativeCoupledBody::found_generator_field(&surface, spec, ResidentGrain(48)).unwrap();
    condition_material(&mut body);
    let text = symbols_of("abca");
    // Symbol sums equal the row passage up to the coefficient enclosure.
    let rows = body
        .prepare_generator_episode(word(&surface, "abca"), binding.clone(), 0, chain(4))
        .unwrap();
    let first = body
        .prepare_generator_symbol_episode(table(&surface, 0), &text, binding.clone(), 0, chain(4))
        .unwrap();
    let (by_rows, by_symbols) = (
        rows.joint_output().inspect().unwrap(),
        first.joint_output().inspect().unwrap(),
    );
    let gap = l1_gap(&by_rows.center, &by_symbols.center);
    eprintln!(
        "MEASURED symbol-sum vs row passage |gap|_1 = {:.3e}, radii {:.3e} + {:.3e}",
        gap.to_f64().unwrap(),
        by_rows.radius.to_f64().unwrap(),
        by_symbols.radius.to_f64().unwrap()
    );
    assert!(gap <= &by_rows.radius + &by_symbols.radius);
    let producing = by_symbols;
    let first = body.publish_incident_field(first, false, true).unwrap();
    let first_id = first.comparison_id().unwrap();
    let census = body.generator_comparison_census(first_id).unwrap();
    assert_eq!(census["sections"], 2);
    assert_eq!(census["alphabet"], 3);
    assert!(body.contemporary_incident_comparison(first_id).is_err());
    let covector = first.joint_output().to_owned().unwrap();
    // An intervening passage sharing symbols moves current, material and (by the caller) the
    // encoder: E_now = table(shift 1).
    let second = body
        .prepare_generator_symbol_episode(
            table(&surface, 0),
            &symbols_of("acba"),
            binding.clone(),
            4,
            chain(4),
        )
        .unwrap();
    let second = body.publish_incident_field(second, true, true).unwrap();
    let second_now = second
        .contemporary_symbol_output(&mut body, &table(&surface, 0))
        .unwrap();
    let update = body
        .prepare_generator_material_return(&second_now, second.joint_output(), 4, &[])
        .unwrap();
    body.publish_incident_material_return(update).unwrap();
    let now = table(&surface, 1);
    let saved = model_bytes(&body);
    let delayed = first.contemporary_symbol_output(&mut body, &now).unwrap();
    let fresh = body
        .prepare_generator_symbol_episode(now.clone(), &text, binding.clone(), 0, chain(4))
        .unwrap();
    let delayed_y = delayed.joint_output().inspect().unwrap();
    assert_eq!(
        delayed_y,
        fresh.joint_output().inspect().unwrap(),
        "one cut: q₀, M and E all contemporary"
    );
    let at_old_encoder = first
        .contemporary_symbol_output(&mut body, &table(&surface, 0))
        .unwrap();
    assert_ne!(at_old_encoder.joint_output().inspect().unwrap(), delayed_y);
    eprintln!(
        "MEASURED symbol delayed vs producing |Δy|_1 = {:.6e}; encoder-only shift |Δy|_1 = {:.6e}",
        l1_gap(&delayed_y.center, &producing.center)
            .to_f64()
            .unwrap(),
        l1_gap(
            &delayed_y.center,
            &at_old_encoder.joint_output().inspect().unwrap().center
        )
        .to_f64()
        .unwrap()
    );
    let returned = body
        .prepare_generator_material_return(&delayed, covector.view(), 4, &[])
        .unwrap();
    let ge = returned.symbol_covector().unwrap();
    assert_eq!((ge.rows(), ge.components()), (3, 6));
    assert!(returned.source_covector().is_none());
    assert!(returned.moment_covector().is_some());
    assert_eq!(
        returned
            .condition_covector()
            .map(|c| (c.rows(), c.components())),
        Some((2, 12))
    );
    // Central-difference pairing of the encoder covector at symbol a, component 0.
    let plus = body
        .prepare_generator_symbol_episode(table(&surface, 2), &text, binding.clone(), 0, chain(4))
        .unwrap();
    let minus = body
        .prepare_generator_symbol_episode(table(&surface, 0), &text, binding.clone(), 0, chain(4))
        .unwrap();
    let row0 = ge.row(0).unwrap().inspect().unwrap().center[0].clone();
    let (direct, adjoint, residual) = pairing_residual(
        &mut body,
        &covector.inspect().unwrap().center,
        &row0,
        &plus,
        &minus,
    );
    eprintln!(
        "MEASURED symbol-table pairing: direct {:.6e}, adjoint {:.6e}, relative {:.3e}",
        direct.to_f64().unwrap(),
        adjoint.to_f64().unwrap(),
        (&residual / adjoint.abs()).to_f64().unwrap()
    );
    assert!(!adjoint.is_zero());
    assert!(residual < adjoint.abs() / r(1000));
    let returned_rows = ge.inspect_rows().unwrap();
    body.publish_incident_material_return(returned).unwrap();
    // Rest keeps the sums only and reproduces the one-cut reading and return.
    assert_eq!(&saved[..19], b"HNA-INCIDENT-FIELD\x04");
    let mut resumed = restore(&surface, &saved);
    assert_eq!(model_bytes(&resumed), saved);
    let resumed_word = resumed
        .contemporary_symbol_comparison(first_id, &now)
        .unwrap();
    assert_eq!(resumed_word.joint_output().inspect().unwrap(), delayed_y);
    let resumed_return = resumed
        .prepare_generator_material_return(&resumed_word, covector.view(), 4, &[])
        .unwrap();
    assert_eq!(
        resumed_return
            .symbol_covector()
            .unwrap()
            .inspect_rows()
            .unwrap(),
        returned_rows
    );
}

#[test]
#[ignore = "requires CUDA; symbol-passage comparison size against source length; prints MEASURED rows"]
fn symbol_comparison_storage_is_independent_of_source_length() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut rows = Vec::new();
    for chained in [false, true] {
        for (n, alphabet) in [
            (3usize, 3usize),
            (8, 3),
            (32, 3),
            (128, 3),
            (32, 16),
            (32, 64),
        ] {
            let (spec, binding) = setup();
            let mut body =
                NativeCoupledBody::found_generator_field(&surface, spec, ResidentGrain(48))
                    .unwrap();
            condition_material(&mut body);
            let text = (0..n).map(|k| (k * 7 + k / 3) % 3).collect::<Vec<_>>();
            let contacts = if chained { chain(n) } else { vec![] };
            let empty = model_bytes(&body).len();
            let started = std::time::Instant::now();
            let generated = body
                .prepare_generator_symbol_episode(
                    wide_table(&surface, alphabet),
                    &text,
                    binding,
                    0,
                    contacts,
                )
                .unwrap();
            let generated = body.publish_incident_field(generated, false, true).unwrap();
            let request_us = started.elapsed().as_micros();
            let id = generated.comparison_id().unwrap();
            let pending = model_bytes(&body).len() - empty;
            let census = body.generator_comparison_census(id).unwrap();
            let started = std::time::Instant::now();
            let now = generated
                .contemporary_symbol_output(&mut body, &wide_table(&surface, alphabet))
                .unwrap();
            let returned = body
                .prepare_generator_material_return(&now, generated.joint_output(), 4, &[])
                .unwrap();
            assert_eq!(returned.symbol_covector().unwrap().rows(), alphabet);
            body.publish_incident_material_return(returned).unwrap();
            let observe_us = started.elapsed().as_micros();
            eprintln!(
                "MEASURED symbols contacts={} N={n} |A|={alphabet} distinct=3 pending_bytes={pending} held_sections={} held_octets={} request_us={request_us} observe_us={observe_us}",
                if chained { "chain" } else { "none" },
                census["sections"],
                census["octets"],
            );
            rows.push((pending, census));
        }
    }
    for group in rows.chunks(6) {
        for row in group {
            assert_eq!(row.1["sections"], group[0].1["sections"]);
            assert_eq!(row.1["octets"], group[0].1["octets"]);
            assert!(
                row.0.abs_diff(group[0].0) <= 8,
                "{} vs {}",
                row.0,
                group[0].0
            );
        }
    }
}

/// `E_g = Σ |q_g|²` of site `g`'s 12 boundary components of the published current.
fn site_energy(body: &mut NativeCoupledBody<'_>, site: usize) -> f64 {
    let BodyState::Incident(model) = body.state_mut().unwrap() else {
        panic!("machine")
    };
    let ball = model
        .field
        .read_current_source()
        .unwrap()
        .enclosure()
        .inspect()
        .unwrap();
    ball.center[site * 6..site * 6 + 6]
        .iter()
        .map(|v| {
            (&v.real * &v.real + &v.imaginary * &v.imaginary)
                .to_f64()
                .unwrap()
        })
        .sum()
}

fn current_radius(body: &mut NativeCoupledBody<'_>) -> Rat {
    let BodyState::Incident(model) = body.state_mut().unwrap() else {
        panic!("machine")
    };
    model
        .field
        .read_current_source()
        .unwrap()
        .enclosure()
        .inspect()
        .unwrap()
        .radius
}

/// `cycles` commit/observe returns of symbol passages; returns per cycle
/// (produced output radius, published current radius, recorded last residual).
fn commit_cycles(
    surface: &ResidentSurface<'_>,
    cycles: usize,
    rebase: bool,
) -> Vec<(Rat, Rat, Rat)> {
    let (spec, binding) = setup();
    let mut body =
        NativeCoupledBody::found_generator_field(surface, spec, ResidentGrain(48)).unwrap();
    condition_material(&mut body);
    if let BodyState::Incident(model) = body.state_mut().unwrap() {
        model.rebase_off = !rebase;
    }
    let mut rows = Vec::new();
    let mut start = 0u64;
    for cycle in 0..cycles {
        let text = (0..4)
            .map(|k| (cycle + k * (cycle % 3 + 1)) % 3)
            .collect::<Vec<_>>();
        let mut step = || -> Result<(Rat, Rat, Rat), NativeSessionError> {
            let generated = body.prepare_generator_symbol_episode(
                table(surface, 0),
                &text,
                binding.clone(),
                start,
                chain(4),
            )?;
            let produced = generated.joint_output().inspect()?.radius;
            let generated = body.publish_incident_field(generated, true, true)?;
            let published = current_radius(&mut body);
            if rebase {
                eprintln!(
                    "MEASURED cycle={cycle} committed steps={} sqrt(E_g0)={:.6e}",
                    start + 4,
                    site_energy(&mut body, 0).sqrt()
                );
            }
            let residual = body.incident_rebase_residual()?;
            let now = generated.contemporary_symbol_output(&mut body, &table(surface, 0))?;
            let returned =
                body.prepare_generator_material_return(&now, generated.joint_output(), 4, &[])?;
            body.publish_incident_material_return(returned)?;
            assert_eq!(residual.commits, cycle as u64 + 1);
            Ok((produced, published, residual.last_radius()?))
        };
        match step() {
            Ok(row) => rows.push(row),
            Err(error) => {
                assert!(!rebase, "rebased cycle {cycle} refused: {error}");
                eprintln!("MEASURED without-rebase refused at cycle {cycle}: {error}");
                return rows;
            }
        }
        start += 4;
    }
    if rebase {
        let residual = body.incident_rebase_residual().unwrap();
        let max = rows.iter().map(|r| r.0.clone()).fold(r(0), |a, b| a.max(b));
        let sum = rows.iter().map(|r| r.0.clone()).fold(r(0), |a, b| a + b);
        assert_eq!(residual.max_radius().unwrap(), max);
        assert_eq!(residual.sum_radius().unwrap(), sum);
        let bytes = model_bytes(&body);
        let restored = restore(surface, &bytes);
        assert_eq!(model_bytes(&restored), bytes, "restart byte identity");
        assert_eq!(restored.incident_rebase_residual().unwrap(), residual);
    }
    rows
}

#[test]
#[ignore = "requires CUDA; committed currents are rebased to their dyadic centres with a declared residual; prints MEASURED radii"]
fn committed_current_rebases_to_its_centre_without_enclosure_growth() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let grain = r(1) / Rat::from_integer(num_bigint::BigInt::from(1u64 << 48));
    for cycles in [6usize, 32] {
        let before = commit_cycles(&surface, cycles, false);
        let after = commit_cycles(&surface, cycles, true);
        assert_eq!(after.len(), cycles);
        for (cycle, a) in after.iter().enumerate() {
            let b = before.get(cycle);
            eprintln!(
                "MEASURED cycles={cycles} cycle={cycle} without-rebase produced_r={} published_r={} | rebase produced_r={:.3e} published_r={:.3e} residual_r={:.3e}",
                b.map_or("refused".into(), |b| format!(
                    "{:.3e}",
                    b.0.to_f64().unwrap()
                )),
                b.map_or("refused".into(), |b| format!(
                    "{:.3e}",
                    b.1.to_f64().unwrap()
                )),
                a.0.to_f64().unwrap(),
                a.1.to_f64().unwrap(),
                a.2.to_f64().unwrap()
            );
            // The published current sits at the grain and the residual is that commit's radius.
            assert!(a.1 <= grain, "published radius {}", a.1);
            assert_eq!(a.2, a.0);
        }
        // Without growth: the last produced radius stays within a bounded factor of the first.
        let first = &after[0].0;
        let last = &after[after.len() - 1].0;
        assert!(
            last <= &(first * r(16)),
            "produced radius grew {first} -> {last}"
        );
    }
}

#[test]
#[ignore = "requires CUDA; a translation-bearing step moves configuration, not the standing current"]
fn translation_bearing_step_does_not_grow_the_standing_current() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let (mut spec, binding) = setup();
    let mut sites = spec.machine.sites().to_vec();
    sites[0].phase.step.translation = RatVec3::new(r(0), r(0), r(1));
    spec.machine = GeneratorMachineSpec::declare(
        spec.machine.frame(),
        spec.machine.units().clone(),
        sites,
        spec.machine.arcs().to_vec(),
        spec.machine.cells().to_vec(),
    )
    .unwrap();
    let mut body =
        NativeCoupledBody::found_generator_field(&surface, spec.clone(), ResidentGrain(48))
            .unwrap();
    let BodyState::Incident(model) = body.state_mut().unwrap() else {
        panic!("machine")
    };
    let machine = model.layout.machine.clone().unwrap();
    let _ = &model.field;
    // A nonzero standing current on both sites.
    let q0 = super::super::machine_tests::make_machine_anchor(&surface, ResidentGrain(48), 0);
    let energy = |values: &[ExactComplexWaveCurrent]| {
        values
            .iter()
            .map(|v| &v.real * &v.real + &v.imaginary * &v.imaginary)
            .sum::<Rat>()
    };
    // 24 real boundary components = 12 complex entries (two sites).
    let boundary = 24;
    let entries = boundary / 2;
    let before = energy(&q0.inspect().unwrap().center[..entries]);
    assert!(!before.is_zero());
    for n in [1usize, 16, 128, 1024] {
        let maps = super::super::machine_source::MachineSourceMaps::new(
            &surface,
            &machine,
            &binding,
            0,
            n,
            ResidentGrain(48),
        )
        .unwrap();
        let zero = ResidentNormalEnclosureSection::zeros(&surface, 1, boundary, ResidentGrain(48))
            .unwrap()
            .row(0)
            .unwrap()
            .to_owned()
            .unwrap();
        let standing = maps
            .anchor(q0.view(), zero.view())
            .unwrap()
            .inspect()
            .unwrap();
        let after = energy(&standing.center[..entries]);
        eprintln!(
            "MEASURED steps={n} E(q0)={:.6e} E(L^N q0)={:.6e} radius={:.3e}",
            before.to_f64().unwrap(),
            after.to_f64().unwrap(),
            standing.radius.to_f64().unwrap()
        );
        let gap = (&after - &before).abs();
        assert!(
            gap <= &before / r(1_000_000) + r(1) / r(1_000_000_000),
            "standing current energy moved with step count: {before} -> {after}"
        );
    }
    // Committed cycles with a silent source (zero encoder). The source standing is carried by
    // L only. The declared arc (source_to_receiver translation (1,-1,0), initials 0 and (2,1,0))
    // has a nonzero current-action bias; a control arc with translation (2,1,0) has none.
    let silent = rows_section(&surface, vec![[0; 6]; 3]);
    let mut runs = Vec::new();
    for (name, arc_translation) in [
        ("declared-arc", RatVec3::from_i64(1, -1, 0)),
        ("unbiased-arc", RatVec3::from_i64(2, 1, 0)),
    ] {
        let mut arcs = spec.machine.arcs().to_vec();
        arcs[0].source_to_receiver.translation = arc_translation;
        let mut run_spec = spec.clone();
        run_spec.machine = GeneratorMachineSpec::declare(
            spec.machine.frame(),
            spec.machine.units().clone(),
            spec.machine.sites().to_vec(),
            arcs,
            spec.machine.cells().to_vec(),
        )
        .unwrap();
        let mut body =
            NativeCoupledBody::found_generator_field(&surface, run_spec, ResidentGrain(48))
                .unwrap();
        condition_material(&mut body);
        let seed = body
            .prepare_generator_symbol_episode(
                table(&surface, 0),
                &symbols_of("abca"),
                binding.clone(),
                0,
                vec![],
            )
            .unwrap();
        body.publish_incident_field(seed, true, false).unwrap();
        let mut energies = Vec::new();
        for cycle in 0..16u64 {
            let generated = body
                .prepare_generator_symbol_episode(
                    silent.clone(),
                    &symbols_of("abca"),
                    binding.clone(),
                    4 + 4 * cycle,
                    vec![],
                )
                .unwrap();
            body.publish_incident_field(generated, true, false).unwrap();
            let e = site_energy(&mut body, 0);
            eprintln!(
                "MEASURED {name} silent source cycle={cycle} committed steps={} sqrt(E_g0)={:.6e}",
                8 + 4 * cycle,
                e.sqrt()
            );
            energies.push(e);
        }
        runs.push(energies);
    }
    eprintln!(
        "MEASURED silent 16-cycle energy ratio: declared-arc {:.4}, unbiased-arc {:.4}",
        runs[0][15] / runs[0][0],
        runs[1][15] / runs[1][0]
    );
}

#[test]
#[ignore = "requires CUDA; the target Holon is one full word at the comparison's contemporary cut"]
fn target_holon_is_one_word_at_the_contemporary_cut() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let (spec, binding) = setup();
    let mut body =
        NativeCoupledBody::found_generator_field(&surface, spec, ResidentGrain(48)).unwrap();
    condition_material(&mut body);
    let produced = body
        .prepare_generator_symbol_episode(
            table(&surface, 0),
            &symbols_of("abca"),
            binding.clone(),
            5,
            chain(4),
        )
        .unwrap();
    let produced = body.publish_incident_field(produced, true, true).unwrap();
    let id = produced.comparison_id().unwrap();
    let receiver = GeneratorPhaseReceiverBinding {
        receiver_id: "text".into(),
        termination_receiver_id: "stop".into(),
        ports: vec![GeneratorPhasePort {
            site_id: "b".into(),
            origin_exponent: 0,
            step_exponent: 1,
        }],
        clock: ClockSpec {
            lineage: "receiving-clock".into(),
            duration: r(1),
            unit: "s".into(),
        },
        aperture: 3,
    };
    let before = model_bytes(&body);
    let target = body
        .evaluate_target_holon(
            id,
            &table(&surface, 0),
            &symbols_of("acb"),
            chain(3),
            receiver.clone(),
        )
        .unwrap();
    assert_eq!(model_bytes(&body), before, "nothing committed or retained");
    let control = body
        .prepare_generator_symbol_episode(
            table(&surface, 0),
            &symbols_of("acb"),
            binding.clone(),
            5,
            chain(3),
        )
        .unwrap()
        .receive_generator_phases(receiver)
        .unwrap();
    assert_eq!(
        target.output().inspect_rows().unwrap(),
        control.output().inspect_rows().unwrap()
    );
    // It is the word, not the word-free moment reading.
    let moment_only = body
        .accumulate_generator_symbol_moment(table(&surface, 0), &symbols_of("acb"), &binding)
        .unwrap();
    let word = body
        .prepare_generator_symbol_episode(
            table(&surface, 0),
            &symbols_of("acb"),
            binding.clone(),
            5,
            chain(3),
        )
        .unwrap();
    assert_ne!(
        moment_only.accumulated().inspect().unwrap(),
        word.joint_output().inspect().unwrap()
    );
    let refused = body.evaluate_target_holon(
        id,
        &wide_table(&surface, 4),
        &symbols_of("acb"),
        chain(3),
        GeneratorPhaseReceiverBinding {
            receiver_id: "text".into(),
            termination_receiver_id: "stop".into(),
            ports: vec![GeneratorPhasePort {
                site_id: "b".into(),
                origin_exponent: 0,
                step_exponent: 1,
            }],
            clock: ClockSpec {
                lineage: "receiving-clock".into(),
                duration: r(1),
                unit: "s".into(),
            },
            aperture: 3,
        },
    );
    assert!(refused.is_err(), "a different alphabet is refused");
}

/// **The retired `\x02` source tape decodes to its moment.** A pre-moment build retained every
/// occurrence's word and the encoded rows; the rows are the producing operands. The tape wire
/// decodes, its rows are accumulated through the contemporary source maps into `m` and `c`, and
/// the decoded comparison reads and returns exactly as the passage comparison of the same rows
/// retained by this build (same cut, same contacts).
#[test]
#[ignore = "requires CUDA; a retired \\x02 source tape decodes to the moment comparison of its rows and returns identically"]
fn a_retired_source_tape_decodes_to_the_moment_of_its_rows() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let (spec, binding) = setup();
    let mut body =
        NativeCoupledBody::found_generator_field(&surface, spec, ResidentGrain(48)).unwrap();
    condition_material(&mut body);
    let rows = encoded(&surface, false, 0);
    let generated = body
        .prepare_generator_episode(Rc::clone(&rows), binding.clone(), 0, contacts())
        .unwrap();
    let covector = generated.joint_output().to_owned().unwrap();
    let generated = body.publish_incident_field(generated, false, true).unwrap();
    let id = generated.comparison_id().unwrap();
    drop(generated);
    let native = model_bytes(&body);
    assert_eq!(&native[..19], b"HNA-INCIDENT-FIELD\x05");
    let mut tape = Vec::new();
    {
        let BodyState::Incident(model) = body.state_mut().unwrap() else {
            panic!("machine")
        };
        NativeIncidentModelRest::write_legacy_tape(
            model,
            id,
            &binding,
            0,
            &rows,
            &contacts(),
            &mut tape,
        )
        .unwrap();
    }
    assert_eq!(&tape[..19], b"HNA-INCIDENT-FIELD\x02");
    let mut retained = restore(&surface, &native);
    let mut decoded = restore(&surface, &tape);
    assert_eq!(decoded.pending_ids().unwrap(), vec![id]);
    assert_eq!(
        decoded.generator_comparison_declaration(id).unwrap(),
        retained.generator_comparison_declaration(id).unwrap(),
        "the tape's per-edge relation becomes the passage's contact counts"
    );
    // The decoded body writes the operands, byte for byte the retained comparison's rest.
    assert_eq!(model_bytes(&decoded), native);
    fn read<'c>(
        body: &mut NativeCoupledBody<'c>,
        id: u64,
        covector: &ResidentNormalEnclosure<'c>,
    ) -> (
        holonic_engine::native_ecology::constitutive_fibre::NativeFieldCurrentBall,
        Vec<holonic_engine::native_ecology::constitutive_fibre::NativeFieldCurrentBall>,
        Vec<u8>,
    ) {
        let word = body.contemporary_incident_comparison(id).unwrap();
        let output = word.joint_output().inspect().unwrap();
        let returned = body
            .prepare_generator_material_return(&word, covector.view(), 4, &contacts())
            .unwrap();
        let rows = returned.source_covector().unwrap().inspect_rows().unwrap();
        drop(word);
        body.publish_incident_material_return(returned).unwrap();
        (output, rows, model_bytes(body))
    }
    assert_eq!(
        read(&mut decoded, id, &covector),
        read(&mut retained, id, &covector)
    );
}

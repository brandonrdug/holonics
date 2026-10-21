use super::*;
use crate::hnn::paired::PairedCarrier;
use crate::hnn::tests::support::{contact, small_field_of};
use crate::ratio::{integer, rat};
fn bounds() -> ContextualBounds {
    ContextualBounds {
        branches: 2,
        pending: 8,
        precision_bits: 20,
        rational_bits: 1024,
        max_features: 32,
        max_scalar_work: 1_000_000,
    }
}
fn fixture() -> (Reference, Constitution, ClassInput) {
    let base = small_field_of(&[3, 2], vec![contact(0, 1, 2, 0)], 1, 2);
    let mut d = base.declaration().clone();
    d.rings[0].lock = vec![0, 1, 2];
    d.offsets.clear();
    d.lattice.clear();
    let field = Field::declare(d.by_lattice_rule()).unwrap();
    let pairing = PairingDeclaration::Family {
        table: vec![(0, 1), (1, 0)],
    };
    let free = ExactRatMatrix::shaped(
        6,
        2,
        (0..6)
            .map(|i| {
                (0..2)
                    .map(|j| integer(i64::from(i == 2 && j == 0)))
                    .collect()
            })
            .collect(),
    )
    .unwrap();
    let source = PairedCarrier::complete_port(&field, 0, &pairing, &free).unwrap();
    let carrier = PairedCarrier::admit(&field, 0, &pairing, &source).unwrap();
    let opening = Constitution::initial(&field, 1 << 40)
        .unwrap()
        .with_symmetric_source(0, source, carrier.symmetry())
        .unwrap()
        .with_ports(1, None, None, Some(ExactRatMatrix::identity(4).unwrap()))
        .unwrap();
    let reference = Reference::new(16, 1 << 40);
    let mut resident = reference
        .mount_with(&field, &Current::at_rest(&field), opening.clone())
        .unwrap();
    let boundary = PairedObservation::admit(&field, &opening, &pairing).unwrap();
    reference
        .ingest(&mut resident, None, &boundary.encode(&[]).unwrap())
        .unwrap();
    let input = ClassInput::found(
        resident,
        ObservedCrib::new(0),
        pairing,
        boundary,
        0,
        0,
        "class-unit/opening-wave-coordinate0-v1".into(),
        bounds(),
        &[7, 11],
    )
    .unwrap();
    (reference, opening, input)
}
fn restored(reference: &Reference, opening: &Constitution, input: &ClassInput) -> ClassInput {
    ClassInput::restored(
        reference,
        input.resident.field(),
        opening.clone(),
        input.pairing.clone(),
        input.boundary.clone(),
        input.ring,
        input.context_coordinate,
        input.units.clone(),
        &input.to_text().unwrap(),
    )
    .unwrap()
}
fn raw_read(word: &Word<'_>, input: &ClassInput) -> Vec<Rat> {
    let p = &input.resident.admitted[0];
    let epoch = p.epochs().next().unwrap();
    input
        .resident
        .constitution
        .receiving_map(p.ring())
        .unwrap()
        .apply(word.anchor(epoch, p.ring()).unwrap())
        .unwrap()
}
#[test]
fn class_input_actual_prefix_material_control_and_combined_cold() {
    let started = Instant::now();
    let (reference, opening, mut input) = fixture();
    let mut twin = input.clone();
    let data = input.boundary.encode(&[0, 1, 0, 1]).unwrap();
    let mut times = Vec::new();
    let mut last_cut = None;
    for at in 0..4 {
        let before = input.branches.clone();
        let r = input.observe(&reference, &data, at, at as u64).unwrap();
        r.material.unwrap();
        reference
            .ingest_class_continuing(
                &mut twin.resident,
                &mut twin.crib,
                &twin.pairing,
                data.cells()[at].class(),
                None,
            )
            .unwrap();
        assert_eq!(
            input.resident.continuing_state(0).unwrap(),
            twin.resident.continuing_state(0).unwrap()
        );
        assert_eq!(input.resident.carried(), twin.resident.carried());
        if at < 2 {
            assert_eq!(before, input.branches);
        }
        last_cut = r.producing;
        times.push((
            r.prefix_context_ns,
            r.native_ingress_ns,
            r.material_formation_ns,
        ));
    }
    assert_eq!(input.accepted, 4);
    assert_eq!(input.branches[0].material.observations(), 2);
    let cut_h = input.branches[0].material.cross();
    assert!(cut_h.iter().flatten().any(|z| !z[0].is_zero()));
    let cold = restored(&reference, &opening, &input);
    assert_eq!(input.to_text().unwrap(), cold.to_text().unwrap());
    let before = input.resident.continuing_state(0).unwrap();
    let saved = input.to_text().unwrap();
    let ticks = input.resident.admitted[0].junction_steps();
    let prospects = input.prospects(ticks, &integer(100)).unwrap();
    let cold_p = cold.prospects(ticks, &integer(100)).unwrap();
    let p = &prospects[0];
    assert!(p.control.iter().any(|x| !x.is_zero()));
    assert!(!p.lift.is_zero());
    // Independent contraction of stored M and actual prefix f, no contract helper.
    let h = input.context().unwrap();
    let f = feature(2, input.history[0], input.history[1], &h);
    let direct: Vec<_> = input.branches[0]
        .material
        .applied()
        .iter()
        .map(|row| row.iter().zip(&f).map(|(m, f)| &m[0] * &f[0]).sum::<Rat>())
        .collect();
    assert_eq!(p.control, direct);
    let baseline = input.word().unwrap();
    let binding = SourceClassPreparation::at(&baseline, &input.boundary, 0).unwrap();
    let e = input.boundary.ports()[0].injection();
    assert_ne!(&p.preparation, e);
    let raw = e.apply(&direct).unwrap();
    let added = input
        .resident
        .field
        .ring(0)
        .rotate(&raw, &input.resident.current.lift()[0]);
    assert_eq!(p.work.added, added);
    assert_eq!(binding.preparation().map().apply(&direct).unwrap(), added);
    assert!(p.work.closes());
    let old = binding.source_opening().to_vec();
    let form = crate::hnn::word::PowerForm::read(
        &input.resident.field,
        &input.resident.constitution,
        &input.resident.current,
    )
    .unwrap();
    let after: Vec<_> = old.iter().zip(&added).map(|(x, y)| x + y).collect();
    assert_eq!(
        p.work.work,
        form.ring_power(0, &after) - form.ring_power(0, &old)
    );
    let mut injected = baseline.change().unwrap();
    for (x, d) in injected.storage[0].iter_mut().zip(&added) {
        *x += d;
    }
    let mut direct_word = Word::continuing(
        &input.resident.field,
        baseline.operands().clone(),
        &injected,
        &input
            .resident
            .field
            .rings()
            .iter()
            .map(|r| vec![Rat::zero(); r.width()])
            .collect::<Vec<_>>(),
        baseline.opened_at(),
    )
    .unwrap();
    direct_word.run(ticks).unwrap();
    assert_eq!(direct_word.change().unwrap(), p.native.change().unwrap());
    let mut frozen = input.word().unwrap();
    frozen.run(ticks).unwrap();
    let learned = raw_read(&p.native, &input);
    let frozen_read = raw_read(&frozen, &input);
    assert_ne!(learned, frozen_read);
    assert_eq!(
        p.native.change().unwrap(),
        cold_p[0].native.change().unwrap()
    );
    assert_eq!(p.work, cold_p[0].work);
    assert_eq!(input.resident.continuing_state(0).unwrap(), before);
    assert_eq!(input.to_text().unwrap(), saved);
    assert_eq!(p.forward_passes, 1);
    assert_eq!(p.adjoint_passes, 0);
    fn q(v: &[Rat]) -> String {
        format!(
            "[{}]",
            v.iter()
                .map(|x| format!("\"{x}\""))
                .collect::<Vec<_>>()
                .join(",")
        )
    }
    let cut = last_cut.unwrap();
    println!(
        "CLASS_INPUT_JSON {{\"kind\":\"synthetic_CODE_class_input_preparation\",\"p\":{},\"c\":{},\"y\":{},\"known_prefix_h\":\"{}\",\"future_h\":\"{}\",\"source_lift\":\"{}\",\"u_eta_M\":{},\"added_Bu\":{},\"preparation_work\":\"{}\",\"cross\":\"{}\",\"quadratic\":\"{}\",\"H00\":\"{}\",\"B00\":\"{}\",\"M00\":\"{}\",\"fit_bound\":\"{}\",\"learned_logits\":{},\"frozen_logits\":{},\"contraction_ns\":{},\"preparation_ns\":{},\"forward_ns\":{},\"total_ns\":{},\"actual_arrivals\":4,\"class_bytes\":4,\"direct_adjoint_calls\":0,\"warm_cold_exact\":true,\"actual_unchanged_by_prospect\":true}}",
        cut.previous,
        cut.current,
        cut.actual,
        cut.context,
        h,
        p.lift,
        q(&p.control),
        q(&p.work.added),
        p.work.work,
        p.work.cross,
        p.work.quadratic,
        input.branches[0].material.normal()[0][0][0],
        input.branches[0].material.cross()[0][0][0],
        input.branches[0].material.applied()[0][0][0],
        input.branches[0].material.coefficient_error_upper(),
        q(&learned),
        q(&frozen_read),
        p.contraction_ns,
        p.preparation_ns,
        p.forward_ns,
        started.elapsed().as_nanos()
    );
    println!(
        "CLASS_INPUT_STATE_BEGIN\n{}\nCLASS_INPUT_STATE_END",
        input.to_text().unwrap()
    );
    println!(
        "CLASS_INPUT_PHASES prefix_context_native_ingress_material_formation_ns={times:?} B={:?} original_source={cut:?}",
        p.preparation
    );

    drop(prospects);
    drop(cold_p);
    drop(baseline);
    drop(binding);
    drop(direct_word);
    drop(frozen);
    let next = input.boundary.encode(&[0]).unwrap();
    let mut warm = input.clone();
    let mut resumed = cold;
    warm.observe(&reference, &next, 0, 4)
        .unwrap()
        .material
        .unwrap();
    resumed
        .observe(&reference, &next, 0, 4)
        .unwrap()
        .material
        .unwrap();
    assert_eq!(warm.to_text().unwrap(), resumed.to_text().unwrap());
    println!(
        "CLASS_INPUT_COLD_CONTINUATION next_actual_accepted_once=true complete_native_material_exact=true"
    );
}
#[test]
fn class_input_refused_material_keeps_actual_once_and_original_cut_cold() {
    let (reference, opening, mut input) = fixture();
    let data = input.boundary.encode(&[0, 1, 0, 1]).unwrap();
    for at in 0..2 {
        input
            .observe(&reference, &data, at, at as u64)
            .unwrap()
            .material
            .unwrap();
    }
    let prior = input.branches.clone();
    let r = input
        .observe_with_formation_limit(&reference, &data, 2, 2, 1)
        .unwrap();
    assert!(r.material.is_err());
    assert_eq!(input.accepted, 3);
    assert_eq!(input.history, vec![1, 0]);
    assert_eq!(input.branches, prior);
    assert_eq!(input.work.successful_fit_proposals, 1);
    let pending = input.pending.get(&2).unwrap();
    assert_eq!(
        (pending.previous, pending.current, pending.actual),
        (0, 1, 0)
    );
    let state = input.resident.continuing_state(0).unwrap();
    assert!(input.observe(&reference, &data, 2, 2).is_err());
    let mut cold = restored(&reference, &opening, &input);
    assert!(cold.observe(&reference, &data, 2, 2).is_err());
    cold.form(2).unwrap();
    assert_eq!(cold.accepted, 3);
    assert_eq!(cold.resident.continuing_state(0).unwrap(), state);
    assert!(cold.form(2).is_err());
    cold.observe(&reference, &data, 3, 3)
        .unwrap()
        .material
        .unwrap();
    assert_eq!(cold.accepted, 4);
    // Native failure must not publish empirical observations.
    let before = cold.to_text().unwrap();
    assert!(cold.observe(&reference, &data, 99, 4).is_err());
    assert_eq!(before, cold.to_text().unwrap());
    println!(
        "CLASS_INPUT_REFUSAL actual_arrivals=4 late_first_stage_fit=1 material_held=true original_source_cold=true retry_ingress=0 later_actual_accepted=true"
    );
}
#[test]
fn class_input_binding_and_direct_vs_existing_preparation() {
    let (reference, opening, mut input) = fixture();
    let data = input.boundary.encode(&[0, 1, 0]).unwrap();
    for at in 0..3 {
        input
            .observe(&reference, &data, at, at as u64)
            .unwrap()
            .material
            .unwrap();
    }
    let source = Arc::new(input.resident.moments.values().next().unwrap().clone());
    let reopen = || {
        Word::open_source_exact_received(
            &input.resident.field,
            &input.resident.constitution,
            &input.resident.current,
            source.clone(),
            &input.resident.reception_opening(),
        )
        .unwrap()
        .0
    };
    let baseline = reopen();
    let binding = SourceClassPreparation::at(&baseline, &input.boundary, 0).unwrap();
    let other = input.word().unwrap();
    assert!(
        binding
            .clone()
            .apply(other, &[rat(1, 4), rat(-1, 4)], &integer(100), 1024)
            .is_err()
    );
    let mut moved = input.clone();
    reference
        .ingest_class_continuing(
            &mut moved.resident,
            &mut moved.crib,
            &moved.pairing,
            0,
            None,
        )
        .unwrap();
    assert!(
        binding
            .clone()
            .apply(
                moved.word().unwrap(),
                &[rat(1, 4), rat(-1, 4)],
                &integer(100),
                1024
            )
            .is_err()
    );
    assert!(
        binding
            .clone()
            .apply(reopen(), &[rat(1, 4), rat(-1, 4)], &integer(0), 1024)
            .is_err()
    );
    let phases = input.resident.admitted[0].clone();
    let compared = vec![true; phases.epochs().count()];
    let old = baseline
        .prospective_feature(&phases, binding.preparation(), &compared)
        .unwrap();
    let control = [rat(1, 4), rat(-1, 4)];
    let (a, ra) = binding
        .apply(reopen(), &control, &integer(100), 1024)
        .unwrap();
    let (b, rb, _) = old.prepare_control(baseline, &control).unwrap();
    assert_eq!(ra, rb);
    assert_eq!(a.change().unwrap(), b.change().unwrap());
    let source = opening.source_port(0).unwrap().scaled(&integer(2));
    let changed = Constitution::initial(&input.resident.field, 1 << 40)
        .unwrap()
        .with_symmetric_source(0, source, input.boundary.ports()[0].carrier().symmetry())
        .unwrap();
    assert!(input.boundary.check_material(&changed).is_err());
    let _ = input.boundary.ports()[0].decoder().unwrap();
    let _ = input.boundary.ports()[0].square().unwrap();
    restored(&reference, &opening, &input);
    let mut bad = input.units.clone();
    bad.push_str("-other");
    assert!(
        ClassInput::restored(
            &reference,
            &input.resident.field,
            opening,
            input.pairing.clone(),
            input.boundary.clone(),
            0,
            0,
            bad,
            &input.to_text().unwrap()
        )
        .is_err()
    );
    println!(
        "CLASS_INPUT_BINDING full_opening_source_identity=true stale_frame_refuses=true stale_E_refuses=true work_refuses=true existing_J_path_equal=true direct_adjoint_calls=0 cache_init_cold=true"
    );
}

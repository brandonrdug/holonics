use super::*;
use crate::embedding_fiber::ResidentReadout;
type W = ExactComplexWaveCurrent;
fn norm(v: &[W]) -> Rat {
    v.iter().map(W::norm_square).sum()
}
fn sub(a: &[W], b: &[W]) -> Vec<W> {
    a.iter().zip(b).map(|(a, b)| a.subtract(b)).collect()
}
fn gram(d: &[Vec<W>], width: usize) -> Vec<Vec<W>> {
    (0..width)
        .map(|i| {
            (0..width)
                .map(|j| {
                    d.iter()
                        .fold(W::zero(), |s, r| s.add(&r[i].multiply(&r[j].conjugate())))
                })
                .collect()
        })
        .collect()
}
fn aggregate(d: &[Vec<W>], b: &[W], width: usize) -> Vec<W> {
    (0..width)
        .map(|j| {
            d.iter()
                .zip(b)
                .fold(W::zero(), |s, (r, b)| s.add(&r[j].multiply(b)))
        })
        .collect()
}
fn contains(read: &NativeOperativeContactReading, d: &[Vec<W>], b: &[W]) {
    assert!(
        read.contacts
            .iter()
            .zip(d)
            .map(|(a, b)| norm(&sub(a, b)))
            .sum::<Rat>()
            <= &read.contacts_radius * &read.contacts_radius
    );
    assert!(read.internal.contains(b));
    let width = read.aggregate.center.len();
    let c = gram(d, width);
    assert!(
        read.covariance
            .iter()
            .zip(c)
            .map(|(a, b)| norm(&sub(a, &b)))
            .sum::<Rat>()
            <= &read.covariance_radius * &read.covariance_radius
    );
    assert!(read.aggregate.contains(&aggregate(d, b, width)));
}

// Independent full recomputation checks reuse of only the unchanged covariance within the
// actual reflection. The aggregate and both moment radii must still match bit for bit.
fn assert_fresh_moments(field: &NativeConstitutiveField<'_>) {
    let op = field.junction.as_ref().unwrap().operative.as_ref().unwrap();
    let surface = field.relation.surface;
    let d = 6 * field.nodes();
    let m = d / 2;
    let rebuilt = sections(surface, d, op.births.len()).unwrap();
    let rounds = surface.fresh_section(1, 2 * (m * m + m), ResidentGrain(0)).unwrap();
    let mut passage = surface.begin_passage(&[vec![]]).unwrap();
    {
        let lane = passage.open(0, &[]).unwrap();
        surface.record_operative_moments(&lane, d, op.births.len(), op.grain,
            op.sections.current(), rebuilt.moments(), &rounds).unwrap();
    }
    passage.close(0, &rebuilt.moment_bounds, 64).unwrap();
    assert!(passage.finish().unwrap().launch().unwrap().obstruction.is_empty());
    for (actual, full) in op.sections.moments().into_iter().zip(rebuilt.moments()) {
        assert_eq!(surface.detach_section(actual, 64).unwrap(),
            surface.detach_section(full, 64).unwrap());
    }
}
fn seed() -> Vec<NativeJunctionSeed> {
    vec![NativeJunctionSeed {
        incoming_admittance: 1,
        held_admittance: 1,
        incoming_transport: NativePhaseCurrent::unit(),
        initial_held: NativePhaseCurrent::zero(),
    }]
}
fn populate(field: &mut NativeConstitutiveField<'_>) {
    let mut latest = None;
    let mut anchor = None;
    for at in 0..4 {
        if at == 2 {
            field
                .rechart(&[NativePhaseCurrent::new(3, 4, 5).unwrap()])
                .unwrap();
        }
        let input = vec![NativePhaseCurrent::new(at + 1, 1, 3).unwrap()];
        let mut occurrence = if at == 3 {
            NativeFieldOccurrence::through_anchor(anchor.as_ref().unwrap(), input)
        } else if let Some(source) = latest.take() {
            NativeFieldOccurrence::through(source, input)
        } else {
            NativeFieldOccurrence::entering(input)
        };
        let next = field.advance_resident(&mut occurrence).unwrap();
        if at == 0 {
            anchor = Some(field.retain_source(&next.source).unwrap());
        }
        latest = Some(next.source);
    }
}
fn packed<'c>(
    s: &'c ResidentSurface<'c>,
    rows: usize,
    width: usize,
    v: Vec<i128>,
) -> ResidentSection<'c> {
    assert_eq!(v.len() * 2, rows * width);
    let words = v
        .into_iter()
        .flat_map(|v| [(v as u128 as u64) as i64, ((v as u128 >> 64) as u64) as i64])
        .map(|v| (v, v))
        .collect();
    s.mount_section_rest(
        &ResidentSectionRest::found(rows, width, ResidentGrain(0), 64, words).unwrap(),
    )
    .unwrap()
}
fn returned<'c>(
    source: &NativeOperativeContactStaging<'_, 'c>,
    huge: bool,
) -> Rc<OperativeReturn<'c>> {
    let surface = source.field.relation.surface;
    let d = 6 * source.field.nodes();
    let k = source.births.len();
    let s = 1i128 << source.grain;
    let mut ports = vec![0; 2 * d];
    ports[0] = if huge { 1i128 << 120 } else { s / 2 };
    ports[1] = s / 4;
    ports[d + 2] = s / 4;
    ports[d + 3] = -s / 8;
    let mut rows = vec![0; 4 * k.max(1)];
    let mut db = vec![0; 2 * k.max(1)];
    for i in 0..k {
        rows[2 * i] = s;
        rows[2 * i + 1] = s / 4;
        rows[2 * k + 2 * i] = s / 2;
        rows[2 * k + 2 * i + 1] = -s / 8;
        db[2 * i] = s / 16;
        db[2 * i + 1] = -s / 32;
    }
    Rc::new(OperativeReturn {
        realization: NativeContactRealization::EnclosedFlow,
        at_cut: source.field_cut(),
        contact_count: source.births.len(),
        factor_count: source.births.len(),
        origin: Rc::clone(&source.origin),
        ports: Rc::new(packed(surface, 2, 2 * d, ports)),
        currents: Rc::new(packed(surface, 2, 4 * k.max(1), rows)),
        b: Some(Rc::new(packed(surface, k.max(1), 4, db))),
        bounds: Rc::new(packed(surface, 1, 4, vec![0, 0])),
    })
}
fn decode<'c>(
    source: &NativeOperativeContactStaging<'_, 'c>,
    wire: &ResidentSection<'c>,
) -> Vec<W> {
    let values = wides(
        &source
            .field
            .relation
            .surface
            .detach_section(wire, 64)
            .unwrap()
            .intervals,
    )
    .unwrap();
    let scale = num_bigint::BigInt::from(1) << source.grain;
    values
        .chunks_exact(2)
        .map(|x| {
            W::new(
                Rat::new(x[0].into(), scale.clone()),
                Rat::new(x[1].into(), scale.clone()),
            )
        })
        .collect()
}

#[test]
#[ignore = "requires CUDA; operative carrier preserves actual roots, birth phase and numerical uncertainty"]
fn native_mount_matches_the_actual_field_and_empty_population() {
    let r = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&r).unwrap();
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(), ResidentGrain(72))
            .unwrap();
    {
        let view = field.stage_operative_contacts().unwrap();
        let read = view.inspect().unwrap();
        assert!(read.births.is_empty());
        contains(&read, &[], &[]);
    }
    populate(&mut field);
    let exact = field.inspect_internal_currents().unwrap().unwrap();
    let count = field.occurrence_count();
    let before = field.census();
    let view = field.stage_operative_contacts().unwrap();
    let after = view.field.census();
    assert_eq!(after.section_read_outs, before.section_read_outs);
    assert_eq!(view.field_cut(), count);
    let read = view.inspect().unwrap();
    assert_eq!(
        read.births
            .iter()
            .map(|b| (b.source, b.receiving))
            .collect::<Vec<_>>(),
        exact
            .iter()
            .map(|b| (b.source_occurrence, b.receiving_occurrence))
            .collect::<Vec<_>>()
    );
    contains(
        &read,
        &exact.iter().map(|b| b.contact.clone()).collect::<Vec<_>>(),
        &exact.iter().map(|b| b.current.clone()).collect::<Vec<_>>(),
    );
}

#[test]
#[ignore = "requires CUDA; native rank-two staging retains mixed terms and the complete predecessor after a late refusal"]
fn coupled_return_stages_map_current_and_moments_without_partial_publication() {
    let r = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&r).unwrap();
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(), ResidentGrain(72))
            .unwrap();
    populate(&mut field);
    let exact = field.inspect_internal_currents().unwrap().unwrap();
    let view = field.stage_operative_contacts().unwrap();
    let original = serde_json::to_value(view.inspect().unwrap()).unwrap();
    // The map update fits wide words, but its squared moment does not. The second lane refuses.
    assert!(view.stage_return(returned(&view, true)).is_err());
    assert_eq!(
        serde_json::to_value(view.inspect().unwrap()).unwrap(),
        original
    );
    assert!(view.returns.is_empty());
    let delta = returned(&view, false);
    let p = decode(&view, &delta.ports);
    let r = decode(&view, &delta.currents);
    let db = decode(&view, delta.b.as_deref().unwrap());
    let m = 3 * view.field.nodes();
    let k = view.births.len();
    let mut d = exact.iter().map(|i| i.contact.clone()).collect::<Vec<_>>();
    let mut b = exact.iter().map(|i| i.current.clone()).collect::<Vec<_>>();
    for i in 0..k {
        for j in 0..m {
            d[i][j] = d[i][j]
                .add(&p[j].multiply(&r[i].conjugate()))
                .add(&p[m + j].multiply(&r[k + i].conjugate()));
        }
        b[i] = b[i].add(&db[i]);
    }
    let before = view.field.census();
    let next = view.stage_return(Rc::clone(&delta)).unwrap();
    assert_eq!(
        next.field.census().section_read_outs,
        before.section_read_outs
    );
    let read = next.inspect().unwrap();
    contains(&read, &d, &b);
    assert_eq!(read.staged_returns, 1);
    assert_ne!(read.covariance, view.inspect().unwrap().covariance);
    assert_ne!(
        read.aggregate.center,
        view.inspect().unwrap().aggregate.center
    );
    assert!(matches!(
        next.stage_return(delta),
        Err(Error::ForeignOccurrence)
    ));
    assert_eq!(
        serde_json::to_value(view.inspect().unwrap()).unwrap(),
        original
    );
    // A second admitted return in the same declared enclosure: perturb one port factor
    // and every internal increment. The full covariance/aggregate must enclose the mixed terms.
    let mut uncertain = returned(&view, false);
    Rc::get_mut(&mut uncertain).unwrap().bounds = Rc::new(packed(
        view.field.relation.surface,
        1,
        4,
        vec![
            (1i128 << view.grain) / 4,
            (k as i128) * (1i128 << view.grain) / 32,
        ],
    ));
    let eta = W::new(Rat::new(1.into(), 16.into()), Rat::from_integer(0.into()));
    let mu = W::new(Rat::from_integer(0.into()), Rat::new(1.into(), 32.into()));
    for i in 0..k {
        d[i][0] = d[i][0].add(&eta.multiply(&r[i].conjugate()));
        b[i] = b[i].add(&mu);
    }
    let staged = view.stage_return(uncertain).unwrap();
    contains(&staged.inspect().unwrap(), &d, &b);
}

#[test]
#[ignore = "requires CUDA; ordinary field publication uses changed operative contacts and a joint reflection error"]
fn changed_contacts_conduct_through_the_same_field_successor() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(), ResidentGrain(72))
            .unwrap();
    populate(&mut field);
    let old = field.inspect_internal_currents().unwrap().unwrap();
    let mut d = old.iter().map(|i| i.contact.clone()).collect::<Vec<_>>();
    let mut b = old.iter().map(|i| i.current.clone()).collect::<Vec<_>>();
    let owned = {
        let view = field.stage_operative_contacts().unwrap();
        let delta = returned(&view, false);
        let ports = decode(&view, &delta.ports);
        let rows = decode(&view, &delta.currents);
        let db = decode(&view, delta.b.as_deref().unwrap());
        let k = view.births.len();
        for i in 0..k {
            for j in 0..3 {
                d[i][j] = d[i][j]
                    .add(&ports[j].multiply(&rows[i].conjugate()))
                    .add(&ports[3 + j].multiply(&rows[k + i].conjugate()));
            }
            b[i] = b[i].add(&db[i]);
        }
        view.stage_return(delta).unwrap().into_owned()
    };
    field.junction.as_mut().unwrap().operative = Some(owned);
    let mut last = None;
    let mut anchor = None;
    for at in 4..8 {
        if at == 6 {
            field
                .rechart(&[NativePhaseCurrent::new(0, 1, 1).unwrap()])
                .unwrap();
        }
        let before = field.stage_operative_contacts().unwrap().inspect().unwrap();
        let input = vec![NativePhaseCurrent::new(at as i64 - 2, 2, 3).unwrap()];
        let mut occurrence = if at == 7 {
            NativeFieldOccurrence::through_anchor(anchor.as_ref().unwrap(), input)
        } else if let Some(s) = last.take() {
            NativeFieldOccurrence::through(s, input)
        } else {
            NativeFieldOccurrence::entering(input)
        };
        let census = field.census();
        let next = field.advance_resident(&mut occurrence).unwrap();
        assert_eq!(field.census().section_read_outs, census.section_read_outs);
        assert_fresh_moments(&field);
        if at == 4 {
            anchor = Some(field.retain_source(&next.source).unwrap());
        }
        last = Some(next.source);
        if let Some(contact) = field.junction_contact(at).unwrap() {
            d.push(contact);
            b.push(W::zero());
        }
        let mut u = field.root_junction_source(at).unwrap();
        u.push(W::zero());
        let exact = PairedJunctionLinearization::at(d.clone(), &u, &b).unwrap();
        let reading = field.inspect_operative_reflection(at).unwrap().unwrap();
        let contacts = field
            .inspect_internal_current_enclosures()
            .unwrap()
            .unwrap();
        assert_eq!(contacts[0].contact, old[0].contact);
        assert!(contacts[0]
            .operative_contact
            .as_ref()
            .unwrap()
            .contains(&d[0]));
        assert_ne!(
            contacts[0].contact,
            contacts[0].operative_contact.as_ref().unwrap().center
        );
        if at == 4 {
            let unchanged = PairedJunctionLinearization::at(
                old.iter().map(|i| i.contact.clone()).collect(),
                &u,
                &b,
            )
            .unwrap();
            assert!(
                !reading.outgoing.contains(unchanged.outgoing()),
                "the operative response must distinguish the changed contact map"
            );
        }
        assert!(reading.potential.contains(exact.potential()));
        assert!(
            norm(&sub(&reading.outgoing.center, exact.outgoing()))
                + norm(&sub(&reading.internal.center, exact.internal()))
                <= &reading.joint_current_radius * &reading.joint_current_radius
        );
        b = exact.internal().to_vec();
        let state = field.stage_operative_contacts().unwrap().inspect().unwrap();
        contains(&state, &d, &b);
        let mut b_hat = before.internal.center;
        if state.births.len() > b_hat.len() {
            b_hat.push(W::zero());
        }
        let q = state
            .contacts
            .iter()
            .map(|d| {
                d.iter()
                    .zip(&reading.potential.center)
                    .fold(W::zero(), |s, (a, b)| s.add(&a.conjugate().multiply(b)))
            })
            .collect::<Vec<_>>();
        let lhs = reading
            .potential
            .center
            .iter()
            .zip(aggregate(&state.contacts, &q, 3))
            .map(|(v, h)| v.add(&h))
            .collect::<Vec<_>>();
        let rhs = reading
            .source
            .center
            .iter()
            .zip(aggregate(&state.contacts, &b_hat, 3))
            .map(|(u, h)| u.add(&h).scaled(&Rat::from_integer(2.into())))
            .collect::<Vec<_>>();
        assert_eq!(reading.numerical_residual, sub(&lhs, &rhs));
        assert!(
            norm(&reading.numerical_residual)
                <= &reading.residual_norm_upper * &reading.residual_norm_upper
        );
        assert_eq!(field.occurrence_count(), at + 1);
    }
    let expected =
        serde_json::to_value(field.stage_operative_contacts().unwrap().inspect().unwrap()).unwrap();
    let expected_history = (4..8)
        .map(|at| field.inspect_operative_reflection(at).unwrap().unwrap())
        .collect::<Vec<_>>();
    let saved = field.rest(&[last.as_ref()], &[anchor.as_ref()]).unwrap();
    let mut bytes = Vec::new();
    saved.write(&mut bytes).unwrap();
    let saved = NativeFieldRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    drop(field);
    drop(last);
    drop(anchor);
    let archive = std::env::temp_dir().join(format!(
        "holonics-operative-{}-{}.history",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let (mut field, mut sources, anchors) =
        NativeConstitutiveField::remount_with_history_archive(&surface, saved, &archive).unwrap();
    assert_eq!(
        serde_json::to_value(field.stage_operative_contacts().unwrap().inspect().unwrap()).unwrap(),
        expected
    );
    for (offset, expected) in expected_history.into_iter().enumerate() {
        assert_eq!(
            field
                .inspect_operative_reflection(4 + offset)
                .unwrap()
                .unwrap(),
            expected
        );
    }
    let mut occurrence = NativeFieldOccurrence::through(
        sources[0].take().unwrap(),
        vec![NativePhaseCurrent::new(2, -1, 3).unwrap()],
    );
    field.advance_resident(&mut occurrence).unwrap();
    d.push(field.junction_contact(8).unwrap().unwrap());
    b.push(W::zero());
    let mut u = field.root_junction_source(8).unwrap();
    u.push(W::zero());
    let exact = PairedJunctionLinearization::at(d.clone(), &u, &b).unwrap();
    let reading = field.inspect_operative_reflection(8).unwrap().unwrap();
    assert!(
        norm(&sub(&reading.outgoing.center, exact.outgoing()))
            + norm(&sub(&reading.internal.center, exact.internal()))
            <= &reading.joint_current_radius * &reading.joint_current_radius
    );
    assert_eq!(anchors.len(), 1);
    drop(field);
    std::fs::remove_file(archive).unwrap();
}

#[test]
#[ignore = "requires CUDA; operative current and the existing contextual material law share a durable successor"]
fn material_continuation_matches_after_operative_rest() {
    let r = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&r).unwrap();
    fn steps<'c>(
        field: &mut NativeConstitutiveField<'c>,
        last: &mut Option<NativeFieldEmission>,
        from: usize,
        to: usize,
    ) {
        for at in from..to {
            let input =
                vec![NativePhaseCurrent::new((at % 3) as i64, ((at + 1) % 2) as i64, 1).unwrap()];
            let mut occurrence = if let Some(source) = last.take() {
                NativeFieldOccurrence::through(source, input)
            } else {
                NativeFieldOccurrence::entering(input)
            };
            *last = Some(field.advance_resident(&mut occurrence).unwrap().source);
            let m = field
                .inspect_contextual_material_transport(at)
                .unwrap()
                .unwrap();
            let p = field.inspect_operative_reflection(at).unwrap().unwrap();
            assert_eq!(
                m.context.as_ref().unwrap().source_radius,
                p.joint_current_radius
            );
        }
    }
    let make = || {
        let mut f = NativeConstitutiveField::found_with_enclosed_junction(
            &surface,
            seed(),
            ResidentGrain(72),
        )
        .unwrap();
        f.enable_material_transport_source(NativeMaterialTransportSource::BilinearContextual)
            .unwrap();
        f.enable_operative_contacts().unwrap();
        f
    };
    let mut field = make();
    let mut last = None;
    steps(&mut field, &mut last, 0, 9);
    let expected = field.rest(&[last.as_ref()], &[]).unwrap();
    drop(field);
    drop(last);
    let mut field = make();
    let mut last = None;
    steps(&mut field, &mut last, 0, 4);
    let rest = field.rest(&[last.as_ref()], &[]).unwrap();
    let mut bytes = vec![];
    rest.write(&mut bytes).unwrap();
    drop(field);
    drop(last);
    let saved = NativeFieldRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    let (mut field, mut sources, _) = NativeConstitutiveField::remount(&surface, saved).unwrap();
    let mut last = sources[0].take();
    steps(&mut field, &mut last, 4, 9);
    assert_eq!(field.rest(&[last.as_ref()], &[]).unwrap(), expected);
    // The operative reaction succeeds before this malformed material bound is encountered.
    // No raw field, operative current, material state, birth or capability may publish partly.
    let transport = field.transport.as_ref().unwrap();
    let width = transport.state.width();
    let mut values = wides(
        &surface
            .detach_section(&transport.state, 64)
            .unwrap()
            .intervals,
    )
    .unwrap();
    values[6 * field.nodes() + 4] = -1;
    let replacement = packed(&surface, 1, width, values);
    let original = std::mem::replace(&mut field.transport.as_mut().unwrap().state, replacement);
    let mut failed =
        NativeFieldOccurrence::through(last.take().unwrap(), vec![NativePhaseCurrent::unit()]);
    assert!(field.advance_resident(&mut failed).is_err());
    assert_eq!(field.occurrence_count(), 9);
    field.transport.as_mut().unwrap().state = original;
    assert_eq!(
        field.rest(&[failed.source.as_ref()], &[]).unwrap(),
        expected
    );
    field.advance_resident(&mut failed).unwrap();
    assert_eq!(field.occurrence_count(), 10);
}

#[test]
#[ignore = "requires CUDA; material source follows complete operative currents after a contact change"]
fn operative_material_reads_changed_contacts_and_keeps_the_source_through_restart() {
    fn dot(a: &[W], b: &[W]) -> W {
        a.iter()
            .zip(b)
            .fold(W::zero(), |s, (a, b)| s.add(&a.conjugate().multiply(b)))
    }
    fn kernel(a: &[W], b: &[W]) -> Rat {
        let one = W::new(Rat::from_integer(1.into()), Rat::from_integer(0.into()));
        one.add(&dot(a, b)).norm_square()
            / ((Rat::from_integer(1.into()) + norm(a)) * (Rat::from_integer(1.into()) + norm(b)))
    }
    fn verify(field: &NativeConstitutiveField<'_>) {
        let readings = (0..field.occurrence_count())
            .map(|at| {
                field
                    .inspect_contextual_material_transport(at)
                    .unwrap()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let contexts = readings
            .iter()
            .map(|r| {
                assert!(r.context.is_none());
                let c = r.operative_context.as_ref().unwrap();
                let mut v = c.outgoing_center.clone();
                v.extend_from_slice(&c.internal_center);
                assert_eq!(norm(&v), c.numerical_norm_square);
                v
            })
            .collect::<Vec<_>>();
        for at in 0..readings.len() {
            let mut expected = vec![W::zero(); field.nodes()];
            let query = &readings[at];
            for i in 1..=at {
                let r = &readings[i];
                let Some(input) = r.input_source.as_ref() else {
                    continue;
                };
                let k = kernel(&input.center, &query.visible_source.center)
                    * kernel(&contexts[i - 1], &contexts[at]);
                let reference = r.reference_receiving_occurrence.unwrap();
                let kr = if reference < i {
                    kernel(
                        &readings[reference].input_source.as_ref().unwrap().center,
                        &query.visible_source.center,
                    ) * kernel(&contexts[reference - 1], &contexts[at])
                } else {
                    Rat::from_integer(0.into())
                };
                for j in 0..field.nodes() {
                    expected[j] = expected[j]
                        .add(&r.ordinary_factor[j].add(&r.contextual_factor[j]).scaled(&k))
                        .subtract(&r.contextual_factor[j].scaled(&kr));
                }
            }
            assert!(
                norm(&sub(&expected, &query.forward.center))
                    <= &query.forward_evaluation_error * &query.forward_evaluation_error
            );
        }
    }
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(), ResidentGrain(72))
            .unwrap();
    field
        .enable_material_transport_source(NativeMaterialTransportSource::OperativeContextual)
        .unwrap();
    populate(&mut field);
    verify(&field);
    let old = field
        .inspect_contextual_material_transport(3)
        .unwrap()
        .unwrap();
    let old = json_compatible(&old);
    let update = {
        let view = field.stage_operative_contacts().unwrap();
        let mut delta = returned(&view, false);
        Rc::get_mut(&mut delta).unwrap().b = None;
        view.stage_return(delta).unwrap().into_update()
    };
    {
        let o = field.junction.as_mut().unwrap().operative.as_mut().unwrap();
        o.sections = update.0;
        o.origin = update.1;
        o.returns = update.2;
    }
    assert_eq!(
        json_compatible(
            &field
                .inspect_contextual_material_transport(3)
                .unwrap()
                .unwrap()
        ),
        old
    );
    let mut last = None;
    let mut anchor = None;
    for at in 4..9 {
        if at == 6 {
            field
                .rechart(&[NativePhaseCurrent::new(0, 1, 1).unwrap()])
                .unwrap();
        }
        let input = vec![NativePhaseCurrent::new((at % 3) as i64, 1, 3).unwrap()];
        let mut occurrence = if at == 8 {
            NativeFieldOccurrence::through_anchor(anchor.as_ref().unwrap(), input)
        } else if let Some(s) = last.take() {
            NativeFieldOccurrence::through(s, input)
        } else {
            NativeFieldOccurrence::entering(input)
        };
        let before = field.census();
        let next = field.advance_resident(&mut occurrence).unwrap();
        assert_eq!(field.census().section_read_outs, before.section_read_outs);
        if at == 4 {
            anchor = Some(field.retain_source(&next.source).unwrap());
        }
        last = Some(next.source);
    }
    verify(&field);
    let expected = field.rest(&[last.as_ref()], &[anchor.as_ref()]).unwrap();
    let mut bytes = vec![];
    expected.write(&mut bytes).unwrap();
    let rest = NativeFieldRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    drop(field);
    drop(last);
    drop(anchor);
    let (mut field, mut sources, anchors) =
        NativeConstitutiveField::remount(&surface, rest).unwrap();
    verify(&field);
    assert_eq!(
        field
            .rest(&[sources[0].as_ref()], &[anchors[0].as_ref()])
            .unwrap(),
        expected
    );
    let mut occurrence = NativeFieldOccurrence::through(
        sources[0].take().unwrap(),
        vec![NativePhaseCurrent::new(1, -1, 3).unwrap()],
    );
    field.advance_resident(&mut occurrence).unwrap();
    verify(&field);
}
fn json_compatible(v: &impl serde::Serialize) -> serde_json::Value {
    serde_json::to_value(v).unwrap()
}

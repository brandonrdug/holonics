use super::*;

fn w(r: i64, i: i64) -> Wave {
    Wave::new(Rat::from_integer(r.into()), Rat::from_integer(i.into()))
}
fn norm(v: &[Wave]) -> Rat {
    v.iter().map(Wave::norm_square).sum()
}
fn reference() -> PairedJunctionLinearization {
    PairedJunctionLinearization::at(
        vec![vec![w(1, 1), w(2, -1)], vec![w(-1, 2), w(1, 0)]],
        &[w(2, 1), w(-1, 3)],
        &[w(1, -2), w(3, 1)],
    )
    .unwrap()
}

#[test]
fn full_complex_differential_and_rank_two_contact_return_are_dual() {
    let p = reference();
    let du = vec![w(-1, 1), w(3, 2)];
    let db = vec![w(2, 3), w(-2, 1)];
    let dd = vec![vec![w(1, 2), w(-3, 1)], vec![w(2, -1), w(1, -2)]];
    let go = vec![w(2, -2), w(1, 3)];
    let gi = vec![w(-1, 4), w(2, 1)];
    let forward = p.pushforward(&du, &db, &dd).unwrap();
    let back = p.pullback(&go, &gi).unwrap();
    let lhs = dot(&go, &forward.outgoing).real + dot(&gi, &forward.internal).real;
    let rhs = dot(&back.source, &du).real
        + dot(&back.incoming_internal, &db).real
        + (0..dd.len())
            .map(|i| dot(&back.contacts.contact(i).unwrap(), &dd[i]).real)
            .sum::<Rat>();
    assert_eq!(lhs, rhs);
    assert!(back
        .contacts
        .port_factors
        .iter()
        .all(|p| norm(p) > Rat::zero()));
    assert!(back
        .contacts
        .contact_factors
        .iter()
        .all(|p| norm(p) > Rat::zero()));
}

#[test]
fn fixed_morphology_reflection_is_its_own_adjoint_and_preserves_full_current() {
    let p = reference();
    let du = vec![w(1, 2), w(3, -1)];
    let db = vec![w(-2, 4), w(0, 1)];
    let zero = vec![vec![Wave::zero(); 2]; 2];
    let f = p.pushforward(&du, &db, &zero).unwrap();
    let b = p.pullback(&f.outgoing, &f.internal).unwrap();
    assert_eq!(b.source, du);
    assert_eq!(b.incoming_internal, db);
    assert_eq!(norm(&f.outgoing) + norm(&f.internal), norm(&du) + norm(&db));
    // Zero incoming on a new row is a constraint. The adjoint still exposes its reaction.
    let q = p
        .pullback(&[w(0, 0), w(0, 0)], &[w(0, 0), w(1, 1)])
        .unwrap();
    assert_ne!(q.incoming_internal[1], Wave::zero());
}

#[test]
fn contact_phase_rechart_carries_the_complete_morphology_cotangent() {
    let p = reference();
    let phase = Wave::new(Rat::new(3.into(), 5.into()), Rat::new(4.into(), 5.into()));
    let phases = [phase, w(0, -1)];
    let contacts = p
        .contacts
        .iter()
        .zip(&phases)
        .map(|(d, g)| d.iter().map(|v| v.multiply(&g.conjugate())).collect())
        .collect();
    let source = sub(&p.potential, &p.outgoing);
    let internal = p
        .incoming_internal
        .iter()
        .zip(&phases)
        .map(|(b, g)| b.multiply(g))
        .collect::<Vec<_>>();
    let q = PairedJunctionLinearization::at(contacts, &source, &internal).unwrap();
    assert_eq!(q.outgoing, p.outgoing);
    let go = vec![w(1, -1), w(2, 3)];
    let gi = vec![w(2, 1), w(-1, 1)];
    let gq = gi
        .iter()
        .zip(&phases)
        .map(|(b, g)| b.multiply(g))
        .collect::<Vec<_>>();
    let a = p.pullback(&go, &gi).unwrap();
    let b = q.pullback(&go, &gq).unwrap();
    assert_eq!(a.source, b.source);
    for i in 0..2 {
        assert_eq!(
            b.incoming_internal[i],
            a.incoming_internal[i].multiply(&phases[i])
        );
        assert_eq!(
            b.contacts.contact(i).unwrap(),
            a.contacts
                .contact(i)
                .unwrap()
                .iter()
                .map(|v| v.multiply(&phases[i].conjugate()))
                .collect::<Vec<_>>()
        );
    }
}

#[test]
fn scalar_reflection_has_its_analytic_contact_derivative_and_empty_family() {
    let p = PairedJunctionLinearization::at(vec![vec![w(2, 0)]], &[w(1, 0)], &[w(0, 0)]).unwrap();
    let g = p.pullback(&[w(1, 0)], &[w(0, 0)]).unwrap();
    assert_eq!(
        g.contacts.contact(0).unwrap()[0].real,
        Rat::new((-8).into(), 25.into())
    );
    let g = p.pullback(&[w(0, 0)], &[w(1, 0)]).unwrap();
    assert_eq!(
        g.contacts.contact(0).unwrap()[0].real,
        Rat::new((-6).into(), 25.into())
    );
    let p = PairedJunctionLinearization::at(vec![], &[w(1, 2)], &[]).unwrap();
    assert_eq!(p.outgoing, vec![w(1, 2)]);
    assert!(p.internal.is_empty());
    assert!(p.pullback(&[], &[]).is_err());
    assert!(p.pushforward(&[w(1, 0)], &[], &[vec![]]).is_err());
}

#[test]
#[ignore = "requires CUDA; exact producer follows the actual paired field through source reuse and phase rechart"]
fn producer_primal_matches_native_field_and_complete_internal_decoder() {
    use crate::embedding_fiber::ResidentReadout;
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let seed = vec![NativeJunctionSeed {
        incoming_admittance: 1,
        held_admittance: 1,
        incoming_transport: NativePhaseCurrent::unit(),
        initial_held: NativePhaseCurrent::zero(),
    }];
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed, ResidentGrain(72))
            .unwrap();
    let mut latest = None;
    let mut anchor = None;
    for at in 0..4 {
        let mut internal = field
            .inspect_internal_currents()
            .unwrap()
            .unwrap()
            .into_iter()
            .map(|i| i.current)
            .collect::<Vec<_>>();
        if at == 2 {
            field
                .rechart(&[NativePhaseCurrent::new(3, 4, 5).unwrap()])
                .unwrap();
        }
        let arriving = vec![NativePhaseCurrent::new(at as i64 + 1, 1, 1).unwrap()];
        let mut occurrence = if at == 3 {
            NativeFieldOccurrence::through_anchor(anchor.as_ref().unwrap(), arriving)
        } else if let Some(source) = latest.take() {
            NativeFieldOccurrence::through(source, arriving)
        } else {
            NativeFieldOccurrence::entering(arriving)
        };
        let step = field.advance_resident(&mut occurrence).unwrap();
        if at == 0 {
            anchor = Some(field.retain_source(&step.source).unwrap());
        }
        latest = Some(step.source);
        let complete = field.inspect_internal_currents().unwrap().unwrap();
        if field.lineage(at).unwrap().received_from.is_some() {
            internal.push(Wave::zero());
        }
        let mut source = field.root_junction_source(at).unwrap();
        source.push(Wave::zero());
        let p = PairedJunctionLinearization::at(
            complete.iter().map(|i| i.contact.clone()).collect(),
            &source,
            &internal,
        )
        .unwrap();
        let exact = field.inspect_exact_junction(at).unwrap().unwrap();
        assert_eq!(p.potential, exact.potential);
        assert_eq!(p.outgoing, exact.outgoing);
        assert_eq!(
            p.internal,
            complete.into_iter().map(|i| i.current).collect::<Vec<_>>()
        );
    }
}

#[test]
fn joint_material_reduction_matches_the_complete_two_receiver_normal_system() {
    let q = |n: i64, d: i64| Rat::new(n.into(), d.into());
    let l = ExactRatMatrix::new(vec![
        vec![q(1, 2), q(-2, 3), q(1, 1)],
        vec![q(3, 2), q(1, 4), q(-1, 3)],
    ])
    .unwrap();
    let r = vec![q(2, 3), q(-1, 2)];
    let t = vec![q(-3, 4), q(4, 3)];
    let g = l.multiply(&l.transpose().unwrap()).unwrap();
    for k in [q(0, 1), q(2, 5), q(1, 1)] {
        let result = joint_material_contact(&l, &r, Some((&t, &k))).unwrap();
        let mut rows = vec![vec![q(0, 1); 4]; 4];
        for i in 0..2 {
            for j in 0..2 {
                let eye = if i == j { q(1, 1) } else { q(0, 1) };
                rows[i][j] = g.get(i, j).unwrap() + q(2, 1) * &eye;
                rows[i][j + 2] = g.get(i, j).unwrap() + (q(1, 1) - &k) * &eye;
                rows[i + 2][j] = rows[i][j + 2].clone();
                rows[i + 2][j + 2] = g.get(i, j).unwrap() + (q(3, 1) - q(2, 1) * &k) * eye;
            }
        }
        let full = ExactRatMatrix::new(rows)
            .unwrap()
            .inverse()
            .unwrap()
            .apply(&r.iter().chain(&t).cloned().collect::<Vec<_>>())
            .unwrap();
        assert_eq!(&full[..2], result.ordinary.as_slice());
        assert_eq!(&full[2..], result.contrast.as_ref().unwrap().as_slice());
        assert!(result.normal_scalar >= q(2, 1));
    }
    let z = ExactRatMatrix::zero(2, 3).unwrap();
    let result = joint_material_contact(&z, &r, Some((&t, &q(1, 1)))).unwrap();
    // Equal source currents leave the contradictory target contrast explicit; the two
    // material factors cancel it rather than pretending to fit a zero source difference.
    assert_eq!(
        result.ordinary,
        r.iter().map(|r| r / q(2, 1)).collect::<Vec<_>>()
    );
    assert_eq!(result.contrast, Some(t));
    assert!(result.producer_change.iter().all(|x| x.is_zero()));
    assert!(joint_material_contact(&l, &r, Some((&r, &q(3, 2)))).is_err());
}

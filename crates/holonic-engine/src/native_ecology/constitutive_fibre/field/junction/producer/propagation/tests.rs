use super::*;
use crate::{causal_reflection::RationalCirclePoint, ExactWavePhaseTransport};

fn w(real: i64, imaginary: i64) -> Wave {
    Wave::new(
        Rat::from_integer(real.into()),
        Rat::from_integer(imaginary.into()),
    )
}
fn norm(v: &[Wave]) -> Rat {
    v.iter().map(Wave::norm_square).sum()
}
fn births() -> Vec<NativeOperativeContactBirth> {
    [(0, 1), (1, 2), (2, 3), (1, 4)]
        .into_iter()
        .map(|(source, receiving)| NativeOperativeContactBirth { source, receiving })
        .collect()
}
fn contacts() -> Vec<Vec<Wave>> {
    vec![
        vec![w(1, 0), w(0, 0)],
        vec![w(1, 0), w(0, 1)],
        vec![w(1, 0), w(1, 0)],
        vec![w(0, 1), w(2, 0)],
    ]
}

#[test]
fn joined_reflections_preserve_current_and_retain_actual_source_joins() {
    let d = contacts();
    let b = vec![w(1, 1), w(0, 1), w(1, 0), w(0, 0)];
    let p = CausalContactPropagation::at(&births(), d.clone(), &b).unwrap();
    assert_eq!(p.joins().collect::<Vec<_>>(), [(0, 1), (1, 2), (0, 3)]);
    assert_eq!(norm(&b), norm(p.internal()));
    assert_ne!(b, p.internal());
    let reflected = PairedJunctionLinearization::at(d, &[w(0, 0), w(1, 0)], p.internal()).unwrap();
    assert_eq!(
        norm(reflected.outgoing()) + norm(reflected.internal()),
        norm(&b) + Rat::one()
    );

    let orthogonal = CausalContactPropagation::at(
        &births()[..2],
        vec![vec![w(1, 0), w(0, 0)], vec![w(0, 0), w(1, 0)]],
        &b[..2],
    )
    .unwrap();
    assert_eq!(orthogonal.internal(), &b[..2]);
    let orphan =
        CausalContactPropagation::at(&births()[..1], contacts()[..1].to_vec(), &b[..1]).unwrap();
    assert_eq!(orphan.internal(), &b[..1]);
    assert!(orphan.joins().next().is_none());
}

#[test]
fn overlap_derivative_and_complete_reflected_adjoint_agree() {
    let d = contacts();
    let b = vec![w(1, 1), w(0, 1), w(1, 0), w(0, 0)];
    let dd = vec![
        vec![w(0, 1), w(1, 0)],
        vec![w(1, 0), w(1, 1)],
        vec![w(1, -1), w(0, 0)],
        vec![w(0, 1), w(1, 0)],
    ];
    let db = vec![w(1, 0), w(1, 1), w(0, -1), w(1, 0)];
    let p = CausalContactPropagation::at(&births(), d.clone(), &b).unwrap();
    let tangent = p.pushforward(&db, &dd).unwrap();

    // Independent derivative of the rational two-branch formula, including its denominator.
    let mut current = b.clone();
    let mut change = db.clone();
    let two = Rat::one() + Rat::one();
    for (e, f) in p.joins() {
        let g = dot(&d[e], &d[f]);
        let dg = dot(&dd[e], &d[f]).add(&dot(&d[e], &dd[f]));
        let squared = g.norm_square();
        let den = Rat::one() + &squared;
        let dden = &two * g.conjugate().multiply(&dg).real;
        let c = (Rat::one() - squared) / &den;
        let dc = -&two * &dden / (&den * &den);
        let s = g.scaled(&(&two / &den));
        let ds = dg
            .scaled(&den)
            .subtract(&g.scaled(&dden))
            .scaled(&(&two / (&den * &den)));
        let left = current[e].scaled(&c).subtract(&s.multiply(&current[f]));
        let right = s
            .conjugate()
            .multiply(&current[e])
            .add(&current[f].scaled(&c));
        let dleft = change[e]
            .scaled(&c)
            .add(&current[e].scaled(&dc))
            .subtract(&ds.multiply(&current[f]))
            .subtract(&s.multiply(&change[f]));
        let dright = ds
            .conjugate()
            .multiply(&current[e])
            .add(&s.conjugate().multiply(&change[e]))
            .add(&change[f].scaled(&c))
            .add(&current[f].scaled(&dc));
        current[e] = left;
        current[f] = right;
        change[e] = dleft;
        change[f] = dright;
    }
    assert_eq!(current, p.internal());
    assert_eq!(change, tangent);
    let fixed = p
        .pushforward(&db, &vec![vec![Wave::zero(); 2]; d.len()])
        .unwrap();
    assert_ne!(
        fixed, tangent,
        "the learned overlap has a material derivative"
    );

    let u = vec![w(1, 1), w(0, 1)];
    let du = vec![w(0, 1), w(1, -1)];
    let reflected = PairedJunctionLinearization::at(d, &u, p.internal()).unwrap();
    let forward = reflected.pushforward(&du, &tangent, &dd).unwrap();
    let out_cov = vec![w(1, -1), w(0, 1)];
    let held_cov = vec![w(0, 1), w(1, 0), w(1, -1), w(0, 1)];
    let outer_return = reflected.pullback(&out_cov, &held_cov).unwrap();
    let path_return = p.pullback(&outer_return.incoming_internal).unwrap();
    let pairing = dot(&out_cov, &forward.outgoing).real + dot(&held_cov, &forward.internal).real;
    let mut returned =
        dot(&outer_return.source, &du).real + dot(&path_return.incoming_internal, &db).real;
    for (at, variation) in dd.iter().enumerate() {
        let total = add(
            &outer_return.contacts.contact(at).unwrap(),
            &path_return.contacts[at],
        );
        returned += dot(&total, variation).real;
    }
    assert_eq!(pairing, returned);
}

#[test]
fn current_and_contact_rechart_preserve_the_propagated_receiver() {
    let d = contacts();
    let b = vec![w(1, 1), w(0, 1), w(1, 0), w(0, 0)];
    let p = CausalContactPropagation::at(&births(), d.clone(), &b).unwrap();
    let point = RationalCirclePoint::from_slope(&Rat::new(1.into(), 2.into()));
    let phase =
        ExactWavePhaseTransport::new(point.real().clone(), point.imaginary().clone()).unwrap();
    let charts = [
        phase.clone(),
        phase.inverse(),
        ExactWavePhaseTransport::identity(),
        phase,
    ];
    let moved_d = d
        .iter()
        .zip(&charts)
        .map(|(d, chart)| d.iter().map(|v| chart.transport(v)).collect())
        .collect();
    let moved_b = b
        .iter()
        .zip(&charts)
        .map(|(b, chart)| chart.inverse().transport(b))
        .collect::<Vec<_>>();
    let moved = CausalContactPropagation::at(&births(), moved_d, &moved_b).unwrap();
    let expected = p
        .internal()
        .iter()
        .zip(&charts)
        .map(|(v, chart)| chart.inverse().transport(v))
        .collect::<Vec<_>>();
    assert_eq!(moved.internal(), expected);
}

#[test]
fn invalid_chronology_is_not_a_new_propagation_edge() {
    let mut changed = births();
    changed[2].receiving = changed[1].receiving;
    assert!(
        CausalContactPropagation::at(&changed, contacts(), &vec![w(0, 0); changed.len()]).is_err()
    );
    changed = births();
    changed[1].source = changed[1].receiving;
    assert!(
        CausalContactPropagation::at(&changed, contacts(), &vec![w(0, 0); changed.len()]).is_err()
    );
}

#[test]
fn propagated_family_retains_contact_and_current_uncertainty() {
    let d = contacts();
    let b = vec![w(1, 1), w(0, 1), w(1, 0), w(0, 0)];
    let p = CausalContactPropagation::at(&births(), d.clone(), &b).unwrap();
    // Declared test apertures on one contact component and one internal component.
    let dr = Rat::new(1.into(), (1 << 3).into());
    let br = Rat::new(1.into(), (1 << 2).into());
    let bound = p.enclosed_internal(&dr, &br).unwrap();
    let mut other_d = d;
    other_d[0][0].imaginary += &dr;
    let mut other_b = b;
    other_b[0].real += &br;
    let other = CausalContactPropagation::at(&births(), other_d, &other_b).unwrap();
    assert!(bound.contains(other.internal()));
    assert_eq!(p.enclosed_internal(&Rat::zero(), &br).unwrap().radius, br);
    assert!(p.enclosed_internal(&(-dr), &Rat::zero()).is_err());

    // Independent point witness for the exact local difference identity used by the bound.
    let g = w(1, 1).scaled(&Rat::new(1.into(), 2.into()));
    let h = w(1, -1).scaled(&Rat::new(1.into(), 3.into()));
    let input = [w(1, 1), w(2, -1)];
    let left = PairedJunctionLinearization::at(
        vec![vec![g.clone()]],
        &input[..1],
        &[Wave::zero().subtract(&input[1])],
    )
    .unwrap();
    let right = PairedJunctionLinearization::at(
        vec![vec![h.clone()]],
        &input[..1],
        &[Wave::zero().subtract(&input[1])],
    )
    .unwrap();
    let difference = norm(&sub(left.outgoing(), right.outgoing()))
        + norm(&sub(left.internal(), right.internal()));
    let two = Rat::one() + Rat::one();
    assert_eq!(
        difference,
        &two * &two * g.subtract(&h).norm_square() * norm(&input)
            / ((Rat::one() + g.norm_square()) * (Rat::one() + h.norm_square()))
    );
}

#[test]
fn a_joined_path_exposes_current_invisible_to_the_fixed_boundary() {
    let births = (0..3)
        .map(|source| NativeOperativeContactBirth {
            source,
            receiving: source + 1,
        })
        .collect::<Vec<_>>();
    let d = vec![vec![w(1, 0)]; births.len()];
    let b = vec![w(1, 0), w(-1, 0), w(0, 0)];
    let plain = PairedJunctionLinearization::at(d.clone(), &[w(0, 0)], &b).unwrap();
    assert_eq!(plain.outgoing(), &[w(0, 0)]);
    let p = CausalContactPropagation::at(&births, d.clone(), &b).unwrap();
    assert_eq!(p.internal(), &[w(1, 0), w(0, 0), w(1, 0)]);
    let continued = PairedJunctionLinearization::at(d, &[w(0, 0)], p.internal()).unwrap();
    assert_eq!(continued.outgoing(), &[w(1, 0)]);
    assert_eq!(
        norm(&b),
        norm(continued.outgoing()) + norm(continued.internal())
    );
    let returned = continued
        .pullback(&[w(1, 0)], &vec![w(0, 0); births.len()])
        .unwrap();
    assert_eq!(
        returned.contacts.contact_factors[0],
        sub(p.internal(), continued.internal())
    );
    assert_ne!(
        returned.contacts.contact_factors[0],
        sub(&b, continued.internal()),
        "the source-current generator owes the propagated input boundary"
    );
}

#[test]
fn dyadic_word_keeps_the_complete_rational_current_and_its_family() {
    let d = contacts();
    let b = vec![w(1, 1), w(0, 1), w(1, 0), w(0, 0)];
    let exact = CausalContactPropagation::at(&births(), d.clone(), &b).unwrap();
    // Different declared numerical receiver grains, without changing the propagation word.
    for grain in [0, 3, 7] {
        let input = NativeFieldCurrentBall {
            center: b.clone(),
            radius: Rat::zero(),
        };
        let bounded =
            CausalContactPropagation::at_enclosed(&births(), &d, &Rat::zero(), &input, grain)
                .unwrap();
        assert!(bounded.internal.contains(exact.internal()));
        assert_eq!(bounded.joins, exact.joins().collect::<Vec<_>>());
        let radius = Rat::new(1.into(), (1 << 3).into());
        let family = CausalContactPropagation::at_enclosed(
            &births(),
            &d,
            &radius,
            &NativeFieldCurrentBall {
                center: b.clone(),
                radius: radius.clone(),
            },
            grain,
        )
        .unwrap();
        let mut changed_d = d.clone();
        changed_d[0][0].imaginary += &radius;
        let mut changed_b = b.clone();
        changed_b[1].imaginary -= &radius;
        let changed = CausalContactPropagation::at(&births(), changed_d, &changed_b).unwrap();
        assert!(family.internal.contains(changed.internal()));
    }
}

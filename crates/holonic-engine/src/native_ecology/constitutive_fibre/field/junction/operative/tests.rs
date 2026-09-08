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
        origin: Rc::clone(&source.origin),
        ports: packed(surface, 2, 2 * d, ports),
        currents: packed(surface, 2, 4 * k.max(1), rows),
        b: packed(surface, k.max(1), 4, db),
        bounds: packed(surface, 1, 4, vec![0, 0]),
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
    let db = decode(&view, &delta.b);
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
    Rc::get_mut(&mut uncertain).unwrap().bounds = packed(
        view.field.relation.surface,
        1,
        4,
        vec![
            (1i128 << view.grain) / 4,
            (k as i128) * (1i128 << view.grain) / 32,
        ],
    );
    let eta = W::new(Rat::new(1.into(), 16.into()), Rat::from_integer(0.into()));
    let mu = W::new(Rat::from_integer(0.into()), Rat::new(1.into(), 32.into()));
    for i in 0..k {
        d[i][0] = d[i][0].add(&eta.multiply(&r[i].conjugate()));
        b[i] = b[i].add(&mu);
    }
    let staged = view.stage_return(uncertain).unwrap();
    contains(&staged.inspect().unwrap(), &d, &b);
}

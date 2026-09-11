use super::super::super::comparison_tests::{current, point};
use super::super::super::family::tests::{body, law};
use super::*;
use crate::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConditionContactMetric, ResidentConstitutiveCurrent, ResidentNormalMaterial,
    },
};
fn r(v: i64) -> Rat {
    Rat::from_integer(v.into())
}
fn reference(a: &[Rat], n: usize, h: &[Rat], v: &[Rat], unit: bool) -> Vec<Rat> {
    let l = &a[0];
    let mut p = a[2 + 4 * n..2 + 6 * n].to_vec();
    let mut c = a[2 + 6 * n..].to_vec();
    if unit {
        let sp = (p.iter().step_by(2).cloned().sum::<Rat>() - l) / r(n as i64);
        let sc = (c.iter().step_by(2).cloned().sum::<Rat>() - l) / r(n as i64);
        for i in 0..n {
            p[2 * i] -= &sp;
            c[2 * i] -= &sc;
        }
    }
    let mut x = c.iter().zip(&p).map(|(c, p)| c - p).collect::<Vec<_>>();
    x.extend(c.clone());
    x.extend(p);
    let mut out = x.clone();
    out.extend(h.iter().map(|h| h * l));
    for h in h.chunks_exact(2) {
        for x in x.chunks_exact(2) {
            out.push(&x[0] * &h[0] - &x[1] * &h[1]);
            out.push(&x[0] * &h[1] + &x[1] * &h[0]);
        }
    }
    out.extend(v.iter().zip(c).map(|(v, c)| l * v - c));
    out
}
fn check(packet: &NormalCoupledComparison<'_>, h: &[Rat], v: &[Rat]) {
    let (a, d) = match packet
        .source()
        .affine_relation()
        .inspect()
        .unwrap()
        .predecessor_reading
    {
        ConstitutiveReading::Plural {
            particular,
            directions,
        } => (particular, directions),
        other => panic!("unexpected family {other:?}"),
    };
    // Cold reading drops zero generator rows; retain their positions from the exact report.
    let rest = packet.source().affine_relation().rest().unwrap();
    let json = serde_json::to_value(rest).unwrap();
    let raw = json["words"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_i64().unwrap())
        .collect::<Vec<_>>();
    let ps = json["source_width"].as_u64().unwrap() as usize;
    let t = json["target_width"].as_u64().unwrap() as usize;
    let mut rows = vec![a];
    for row in raw[ps + t + 4..].chunks_exact(t) {
        rows.push(row.iter().map(|v| r(*v)).collect());
    }
    assert!(!d.is_empty());
    assert_eq!(rows.len(), packet.parameter_rows());
    for (i, a) in rows.iter().enumerate() {
        let got = packet.inspect_row(i).unwrap();
        let mut actual = got.features;
        actual.extend(got.observed_difference);
        assert_eq!(
            actual,
            reference(
                a,
                packet.relation().roots(),
                h,
                v,
                packet.relation().source_receiver() == WaveSourceReceiver::UnitRealSum
            ),
            "source parameter {i}"
        );
    }
}
#[test]
#[ignore = "requires CUDA; delayed comparisons preserve old condition, full joint factors and producing image"]
fn coupled_producing_comparison_survives_intervening_condition_and_material() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let h = point(&s, &[1, 1]);
    let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![law(&s, false)],
        current(&h),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let mut wave = body(&s).with_neighborhood(neighborhood).unwrap();
    let contact = wave.admit_contact(0).unwrap();
    let prediction = wave.predict_contact(&contact).unwrap();
    let v = point(&s, &[3, 5]);
    let before = wave.rest().unwrap();
    let reads = s.census().section_read_outs;
    let paired = wave
        .compare_coupled_prediction(&prediction.handle, current(&v))
        .unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert_eq!(wave.rest().unwrap(), before);
    check(&paired, &[r(1), r(1)], &[r(3), r(5)]);
    let source = point(&s, &[1, 0, 1, 0, 0, 0]);
    let response = point(&s, &[2, 0]);
    let contact = wave.admit_contact(0).unwrap();
    wave.receive_contact_source(&contact, current(&source), current(&response))
        .unwrap();
    let again = wave
        .compare_coupled_prediction(&prediction.handle, current(&v))
        .unwrap();
    assert_eq!(
        s.detach_section(paired.coefficients(), 64).unwrap(),
        s.detach_section(again.coefficients(), 64).unwrap()
    );
    check(&again, &[r(1), r(1)], &[r(3), r(5)]);
    let saved = wave.rest().unwrap();
    let mut bytes = Vec::new();
    saved.write(&mut bytes).unwrap();
    assert!(saved.has_coupled_prediction(prediction.handle.id()));
    let mut restored = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64)
        .unwrap()
        .remount_coupled(&s, |_| {})
        .unwrap();
    assert!(restored
        .compare_coupled_prediction(&prediction.handle, current(&v))
        .is_err());
    let h = restored
        .pending_coupled_prediction(prediction.handle.id())
        .unwrap();
    let next = restored
        .compare_coupled_prediction(&h, current(&v))
        .unwrap();
    assert_eq!(
        s.detach_section(paired.coefficients(), 64).unwrap(),
        s.detach_section(next.coefficients(), 64).unwrap()
    );
    restored.release_coupled_prediction(&h).unwrap();
    assert!(restored
        .compare_coupled_prediction(&h, current(&v))
        .is_err());
    check(&next, &[r(1), r(1)], &[r(3), r(5)]);
}
#[test]
#[ignore = "requires CUDA; unit source and observed lift use exact fractional offsets and correlated rows"]
fn coupled_producing_comparison_unit_lift_is_exact() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let h = point(&s, &[1, 0]);
    let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![super::super::tests::unit_swap(&s)],
        current(&h),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let p = point(&s, &[4, 0, 1, 0]);
    let c = point(&s, &[1, 0, 4, 0]);
    let mut wave = ResidentNormalMaterial::found(&s, 2, 2, ResidentGrain(32))
        .unwrap()
        .into_applied_difference_wave(current(&p), current(&c))
        .unwrap()
        .with_neighborhood(neighborhood)
        .unwrap();
    let contact = wave
        .admit_contact_in_chart(0, WaveSourceReceiver::UnitRealSum)
        .unwrap();
    let pred = wave.predict_contact(&contact).unwrap();
    let v = point(&s, &[1, 0, 2, 0, 3]);
    let packet = wave
        .compare_coupled_prediction(
            &pred.handle,
            ResidentConstitutiveCurrent::rational(&v).unwrap(),
        )
        .unwrap();
    check(
        &packet,
        &[r(1), r(0)],
        &[r(1) / r(3), r(0), r(2) / r(3), r(0)],
    );
    for i in 0..packet.parameter_rows() {
        assert_eq!(
            packet
                .inspect_row(i)
                .unwrap()
                .observed_difference
                .iter()
                .step_by(2)
                .cloned()
                .sum::<Rat>(),
            r(0)
        );
    }
    let bad = point(&s, &[1, 0, 1, 0]);
    let before = wave.rest().unwrap();
    assert!(wave
        .compare_coupled_prediction(&pred.handle, current(&bad))
        .is_err());
    assert_eq!(wave.rest().unwrap(), before);
}

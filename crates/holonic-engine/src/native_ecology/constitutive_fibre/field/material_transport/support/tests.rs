use super::*;
use crate::embedding_fiber::ResidentReadout;
fn phase(r: i64, i: i64) -> NativePhaseCurrent {
    NativePhaseCurrent::new(r, i, 1).unwrap()
}
#[test]
#[ignore = "requires CUDA; native support restriction, full decoder and independent packet continuation"]
fn material_report_support_preserves_phase_defects_and_future_receivers() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let seeds = vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: phase(1, 0),
            initial_held: phase(0, 0)
        };
        6
    ];
    let mut f = NativeConstitutiveField::found_with_enclosed_junction(&s, seeds, ResidentGrain(72))
        .unwrap();
    f.enable_material_transport_chart(
        NativeMaterialTransportSource::OperativeContextual,
        NativeMaterialTarget::TensorProduct { factor_width: 2 },
    )
    .unwrap();
    let mut last = None;
    for (at, word) in [3, 5, 3, 6].into_iter().enumerate() {
        let input = (0..6)
            .map(|j| {
                if (word >> (j / 2)) & 1 == j % 2 {
                    phase(1, if at == 2 { 1 } else { 0 })
                } else {
                    phase(0, 0)
                }
            })
            .collect();
        let mut event = if let Some(source) = last.take() {
            NativeFieldOccurrence::through(source, input)
        } else {
            NativeFieldOccurrence::entering(input)
        };
        last = Some(f.advance_resident(&mut event).unwrap().source);
        let dense = f.inspect_material_transport_wire(at).unwrap().unwrap();
        let before = s.census();
        let packing = f.pack_material_report(at).unwrap();
        assert_eq!(
            s.census().section_read_outs - before.section_read_outs,
            1,
            "only the coordinate inventory crosses the boundary"
        );
        assert_eq!(packing.unfold().unwrap(), dense);
        let cold = NativeMaterialReportPackingRest::from_report(
            packing.lineage.clone(),
            packing.target_chart,
            packing.nodes,
            &dense,
        )
        .unwrap();
        assert_eq!(packing.rest().unwrap(), cold);
        assert_eq!(cold.unfold_rest().unwrap(), dense);
        assert_eq!(
            packing.read_packet().unwrap(),
            f.read_material_packet(at).unwrap().unwrap()
        );
        assert!(packing.packed_report_words() < packing.dense_report_words());
        if at == 0 {
            assert_eq!(packing.coordinates(), &[3]);
        }
        if at == 3 {
            assert_eq!(packing.coordinates(), &[3, 5, 6]);
        }
    }
    let saved = f.rest(&[last.as_ref()], &[]).unwrap();
    let mut wire = vec![];
    saved.write(&mut wire).unwrap();
    assert!(wire.starts_with(b"HNA-NATIVE-FIELD-REST\x02"));
    let restored = NativeFieldRest::read(&mut wire.as_slice(), wire.len() as u64).unwrap();
    assert_eq!(saved, restored);
    let expected = f.inspect_material_transport_wire(3).unwrap().unwrap();
    let packing = f.pack_material_report(3).unwrap();
    let packet = packing.read_packet().unwrap();
    let rest = packing.rest().unwrap();
    let mut bytes = vec![];
    rest.write(&mut bytes).unwrap();
    let restored =
        NativeMaterialReportPackingRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    assert_eq!(rest, restored);
    drop(packing);
    drop(f);
    let packing = NativeMaterialReportPacking::remount(&s, restored).unwrap();
    assert_eq!(packing.unfold().unwrap(), expected);
    assert_eq!(packing.read_packet().unwrap(), packet);
    let mut bad = packing.rest().unwrap();
    bad.coordinates.push(3);
    assert!(bad.write(&mut vec![]).is_err());
}

#[test]
#[ignore = "requires CUDA; all report words and empty/dense coordinate support"]
fn material_report_support_covers_every_word_without_aliasing() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let n = 2;
    let t = 2;
    for empty in [false, true] {
        let width = 82 * t + 68 * n + 96;
        let words = (0..width)
            .map(|j| {
                let v = if empty {
                    0
                } else {
                    (j as i64 + 1) * if j % 2 == 0 { -1 } else { 1 }
                };
                (v, v)
            })
            .collect();
        let input = s
            .mount_section_rest(
                &ResidentSectionRest::found(1, width, ResidentGrain(0), 64, words).unwrap(),
            )
            .unwrap();
        let support = s.fresh_section(1, t + 1, ResidentGrain(0)).unwrap();
        let mut p = s.begin_passage(&[vec![]]).unwrap();
        {
            let lane = p.open(0, &[]).unwrap();
            s.record_material_support(&lane, 0, &input, &support, n, t, 0, &support)
                .unwrap();
        }
        p.close(0, &support, 64).unwrap();
        assert!(p.finish().unwrap().launch().unwrap().obstruction.is_empty());
        let count = if empty { 0 } else { t };
        assert_eq!(s.read_out(&support).unwrap()[0].0, count as i64);
        let packed = s
            .fresh_section(1, 68 * n + 96 + 82 * count, ResidentGrain(0))
            .unwrap();
        let unfolded = s.fresh_section(1, width, ResidentGrain(0)).unwrap();
        let mut p = s.begin_passage(&[vec![]]).unwrap();
        {
            let lane = p.open(0, &[]).unwrap();
            s.record_material_support(&lane, 1, &input, &support, n, t, count, &packed)
                .unwrap();
            s.record_material_support(&lane, 2, &packed, &support, n, t, count, &unfolded)
                .unwrap();
        }
        p.close(0, &unfolded, 64).unwrap();
        assert!(p.finish().unwrap().launch().unwrap().obstruction.is_empty());
        assert_eq!(s.read_out(&unfolded).unwrap(), s.read_out(&input).unwrap());
    }
}

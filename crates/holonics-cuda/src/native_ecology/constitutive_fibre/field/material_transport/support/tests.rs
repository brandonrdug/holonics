use super::*;
use crate::embedding_fiber::ResidentReadout;

/// Parity law (material support kernel): unfold(pack(x)) = x word for word on dense and empty support.
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

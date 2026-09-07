use super::*;
use crate::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConditionPreimageReading, ConstitutiveReading, ResidentConstitutiveFibre,
    },
    phase_current::{convolve_phase_current, ExactPhaseCurrentSection},
    resident_section::ResidentSectionRest,
    CpuExecutor,
};
use num_traits::Zero;

fn q(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
fn mount<'c>(s: &'c ResidentSurface<'c>, words: &[i64]) -> ResidentSection<'c> {
    s.mount_section_rest(
        &ResidentSectionRest::found(
            1,
            words.len(),
            ResidentGrain(0),
            64,
            words.iter().map(|v| (*v, *v)).collect(),
        )
        .unwrap(),
    )
    .unwrap()
}
fn view<'a, 'c>(
    s: &'a ResidentSection<'c>,
    raw: usize,
    id: u64,
) -> ResidentPhaseCurrentView<'a, 'c> {
    ResidentPhaseCurrentView::new(
        ResidentConstitutiveCurrent::rational(s).unwrap(),
        PhaseCurrentReceiverId(id),
        PhaseCurrentLineageId(id),
        q(id as i64, 10),
        q(1, 16000),
        2,
        raw,
    )
    .unwrap()
}
fn product<'a, 'c>(
    s: &'c ResidentSurface<'c>,
    x: &'a ResidentSection<'c>,
    c: &'a ResidentSection<'c>,
    n: usize,
    k: usize,
) -> Result<ResidentPhaseConvolution<'a, 'c>, ResidentPhaseCurrentError> {
    convolve_resident(
        s,
        view(x, n, 1),
        view(c, k, 2),
        PhaseCurrentReceiverId(3),
        PhaseCurrentLineageId(4),
    )
}
fn values(s: &ResidentSurface<'_>, output: &ResidentSection<'_>) -> Vec<Rat> {
    let pairs = s.read_out(output).unwrap();
    assert!(pairs.iter().all(|(lo, hi)| lo == hi));
    let den = pairs.last().unwrap().0;
    pairs[..pairs.len() - 1]
        .iter()
        .map(|p| q(p.0, den))
        .collect()
}

#[test]
#[ignore = "requires native GPU; exact causal tail agrees with the independent cold owner"]
fn complete_carry_matches_cold_reference_and_retains_operand_charts() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let x = mount(&s, &[1, 0, 2, 0, 3, 0, 0, 0, 1]);
    let c = mount(&s, &[4, 0, 5, 0, 1]);
    let before = s.census();
    let out = product(&s, &x, &c, 3, 2).unwrap();
    assert_eq!(s.census().section_read_outs, before.section_read_outs);
    assert_eq!(s.census().ingress_octets, before.ingress_octets);
    assert_eq!(out.source().lineage(), PhaseCurrentLineageId(1));
    assert_eq!(out.response().lineage(), PhaseCurrentLineageId(2));
    let chart = out.view().unwrap();
    assert_eq!(chart.receiver(), PhaseCurrentReceiverId(3));
    assert_eq!(chart.lineage(), PhaseCurrentLineageId(4));
    assert_eq!(chart.origin(), &q(3, 10));
    assert_eq!(chart.sample_step(), &q(1, 16000));
    assert_eq!(chart.raw_extent(), 4);
    let cold = |id, values: &[i32]| {
        ExactPhaseCurrentSection::from_i32(
            PhaseCurrentReceiverId(id),
            PhaseCurrentLineageId(id),
            q(id as i64, 10),
            q(1, 16000),
            2,
            values,
        )
        .unwrap()
    };
    let reference = convolve_phase_current(
        &cold(1, &[1, 2, 3]),
        &cold(2, &[4, 5]),
        PhaseCurrentReceiverId(3),
        PhaseCurrentLineageId(4),
        CpuExecutor::serial(),
    )
    .unwrap();
    let expected: Vec<_> = reference
        .output
        .flat_values()
        .into_iter()
        .flat_map(|v| [Rat::from_integer(v), Rat::zero()])
        .collect();
    assert_eq!(values(&s, out.section()), expected);
}

#[test]
#[ignore = "requires native GPU; complex rational results continue without remount"]
fn rational_complex_products_continue_resident() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let x = mount(&s, &[1, 2, -3, 4, 2]);
    let c = mount(&s, &[2, -1, 5, 3, 3]);
    let before = s.census();
    let first = product(&s, &x, &c, 2, 2).unwrap();
    let second = convolve_resident(
        &s,
        first.view().unwrap(),
        view(&c, 2, 2),
        PhaseCurrentReceiverId(5),
        PhaseCurrentLineageId(6),
    )
    .unwrap();
    assert_eq!(s.census().section_read_outs, before.section_read_outs);
    assert_eq!(s.census().ingress_octets, before.ingress_octets);
    assert_eq!(
        values(&s, first.section()),
        vec![q(4, 6), q(3, 6), q(-3, 6), q(24, 6), q(-27, 6), q(11, 6)]
    );
    assert_eq!(
        values(&s, second.section()),
        vec![
            q(11, 18),
            q(2, 18),
            q(29, 18),
            q(78, 18),
            q(-130, 18),
            q(160, 18),
            q(-168, 18),
            q(-26, 18)
        ]
    );
}

#[test]
#[ignore = "requires native GPU; normalization precedes the final i64 carrier conversion"]
fn wide_products_normalize_before_word_publication() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let m = i64::MAX;
    let x = mount(&s, &[m, 0, m]);
    let c = mount(&s, &[m, 0, m]);
    let out = product(&s, &x, &c, 1, 1).unwrap();
    assert_eq!(values(&s, out.section()), vec![q(1, 1), q(0, 1)]);
}

#[test]
#[ignore = "requires native GPU; malformed carriers and overflow refuse without changing sources"]
fn malformed_numeric_carriers_and_late_overflow_preserve_inputs() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let c = mount(&s, &[2, 0, 1]);
    for words in [
        vec![1, 0, 0],
        vec![1, 0, -1],
        vec![1, 0, 9, 0, 1],
        vec![1, 0, i64::MAX, 0, 1],
    ] {
        let x = mount(&s, &words);
        let original = s.read_out(&x).unwrap();
        let raw = if words.get(2) == Some(&i64::MAX) {
            2
        } else {
            1
        };
        assert!(product(&s, &x, &c, raw, 1).is_err());
        assert_eq!(s.read_out(&x).unwrap(), original);
    }
    let x = s
        .mount_section_rest(
            &ResidentSectionRest::found(1, 3, ResidentGrain(0), 64, vec![(1, 2), (0, 0), (1, 1)])
                .unwrap(),
        )
        .unwrap();
    assert!(product(&s, &x, &c, 1, 1).is_err());
    assert_eq!(s.read_out(&x).unwrap(), vec![(1, 2), (0, 0), (1, 1)]);
}

#[test]
#[ignore = "requires native GPU; chart and surface refusals precede output allocation"]
fn incompatible_charts_and_surface_refuse_before_allocation() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let foreign = ResidentSurface::on(&r).unwrap();
    let x = mount(&s, &[1, 0, 1]);
    let c = mount(&foreign, &[1, 0, 1]);
    let before = s.census();
    assert!(product(&s, &x, &c, 1, 1).is_err());
    for (step, phase) in [(q(1, 8000), 2), (q(1, 16000), 3)] {
        let mismatched = ResidentPhaseCurrentView::new(
            ResidentConstitutiveCurrent::rational(&x).unwrap(),
            PhaseCurrentReceiverId(2),
            PhaseCurrentLineageId(2),
            q(0, 1),
            step,
            phase,
            1,
        )
        .unwrap();
        assert!(matches!(
            convolve_resident(
                &s,
                view(&x, 1, 1),
                mismatched,
                PhaseCurrentReceiverId(3),
                PhaseCurrentLineageId(3)
            ),
            Err(ResidentPhaseCurrentError::Chart(
                PhaseCurrentError::ChartMismatch
            ))
        ));
    }
    assert!(ResidentPhaseCurrentView::new(
        ResidentConstitutiveCurrent::rational(&x).unwrap(),
        PhaseCurrentReceiverId(1),
        PhaseCurrentLineageId(1),
        q(0, 1),
        q(0, 1),
        2,
        1
    )
    .is_err());
    assert_eq!(s.census(), before);
}

#[test]
#[ignore = "requires native GPU; the full admitted scratch tail is retained and the next extent refuses"]
fn scratch_boundary_uses_actual_target_carriers() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let available = s.declaration().max_sectiond_bytes as usize;
    let mut n = 1;
    while ResidentSurface::constitutive_wide_scratch(2 * (n + 1)).unwrap() <= available {
        n += 1;
    }
    let mut words = vec![0; 2 * n + 1];
    words[2 * n - 2] = 7;
    words[2 * n] = 1;
    let x = mount(&s, &words);
    let c = mount(&s, &[1, 0, 1]);
    let out = product(&s, &x, &c, n, 1).unwrap();
    assert_eq!(values(&s, out.section())[2 * n - 2], q(7, 1));
    let too_wide = mount(&s, &vec![0; 2 * (n + 1) + 1]);
    let before = s.census();
    assert!(matches!(
        product(&s, &too_wide, &c, n + 1, 1),
        Err(ResidentPhaseCurrentError::Native(
            ConstitutiveFibreError::ScratchAperture { .. }
        ))
    ));
    assert_eq!(s.census(), before);
}

#[test]
#[ignore = "requires native GPU; a plural returned current cannot silently become a temporal point"]
fn temporal_point_consumer_preserves_a_plural_fibre() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut body = ResidentConstitutiveFibre::found(&s, 2, 2).unwrap();
    body.advance(&[0, 0], Some(&[1, 0])).unwrap();
    let zero = mount(&s, &[0, 0, 1]);
    let plural = body
        .advance_resident(ResidentConstitutiveCurrent::rational(&zero).unwrap(), None)
        .unwrap();
    let original = plural.inspect().unwrap();
    assert!(matches!(
        original.predecessor_reading,
        ConstitutiveReading::Plural { .. }
    ));
    let response = mount(&s, &[1, 0, 1]);
    let source = ResidentPhaseCurrentView::new(
        plural.current(),
        PhaseCurrentReceiverId(1),
        PhaseCurrentLineageId(1),
        q(0, 1),
        q(1, 16000),
        2,
        1,
    )
    .unwrap();
    let before = s.census();
    assert!(convolve_resident(
        &s,
        source,
        view(&response, 1, 2),
        PhaseCurrentReceiverId(3),
        PhaseCurrentLineageId(3)
    )
    .is_err());
    assert_eq!(s.census().section_read_outs, before.section_read_outs);
    assert_eq!(plural.inspect().unwrap(), original);
    assert_eq!(body.occurrences(), 2);
}

#[test]
#[ignore = "requires native GPU; one native learner recovers a causal action and an unprovided response"]
fn native_temporal_observations_develop_the_shared_conditional_relation() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 2, 2, 3).unwrap();
    let mut population = vec![vec![0, 0, 0, 0, 1]];
    for coordinate in 0..4 {
        let mut words = vec![0, 0, 0, 0, 1];
        words[coordinate] = 1;
        population.push(words);
    }
    let inputs: Vec<_> = population.iter().map(|v| mount(&s, v)).collect();
    let before = s.census();
    // Independent source and response impulses expose the declared causal polynomial world.
    // Only its resident observations enter the existing learner; no target is calculated here.
    for x in &inputs {
        for c in &inputs {
            let measured = product(&s, x, c, 2, 2).unwrap();
            body.advance_bilinear_contact(
                view(x, 2, 1).current(),
                view(c, 2, 2).current(),
                Some(measured.current().unwrap()),
            )
            .unwrap();
        }
    }
    assert_eq!(s.census().section_read_outs, before.section_read_outs);
    let x = mount(&s, &[1, 2, -3, 4, 2]);
    let hidden = mount(&s, &[2, -1, 5, 3, 3]);
    let later = mount(&s, &[-2, 3, 4, 1, 5]);
    let before = s.census();
    let observed = product(&s, &x, &hidden, 2, 2).unwrap();
    let cut = body.occurrences();
    let inferred = body
        .read_condition_preimage(view(&x, 2, 1).current(), observed.current().unwrap())
        .unwrap();
    assert_eq!(body.occurrences(), cut);
    let predicted = body
        .advance_bilinear_contact(view(&later, 2, 1).current(), inferred.current(), None)
        .unwrap();
    let actual = product(&s, &later, &hidden, 2, 2).unwrap();
    assert_eq!(s.census().section_read_outs, before.section_read_outs);
    match predicted.inspect().unwrap().predecessor_reading {
        ConstitutiveReading::Unique { current } => {
            assert_eq!(current, values(&s, actual.section()))
        }
        other => panic!("unresolved learned action: {other:?}"),
    }
    match inferred.inspect().unwrap() {
        ConditionPreimageReading::Compatible {
            particular,
            directions,
        } => {
            assert!(directions.is_empty());
            assert_eq!(particular, vec![q(2, 3), q(-1, 3), q(5, 3), q(1, 1)]);
        }
        other => panic!("unexpected response fibre: {other:?}"),
    }
    assert_eq!(body.occurrences(), 26);
}

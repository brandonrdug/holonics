use super::*;
use crate::embedding_fiber::ResidentReadout;

fn make<'c>(surface: &'c ResidentSurface<'c>) -> NativeConstitutiveField<'c> {
    let mut field = NativeConstitutiveField::found_with_enclosed_junction(
        surface,
        vec![NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        }],
        ResidentGrain(72),
    )
    .unwrap();
    field
        .enable_material_transport_source(NativeMaterialTransportSource::OperativeNormal)
        .unwrap();
    field
}

/// Causal-propagation parity: the device word equals the exact host
/// `CausalContactPropagation::at_enclosed` joins, overlaps and centre, within one ulp of radius.
#[test]
#[ignore = "requires CUDA; full native word, exact overlaps, family enclosure and unchanged source"]
fn resident_causal_propagation_matches_the_enclosed_word_and_retains_the_source() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field = make(&surface);
    {
        let view = field.stage_operative_contacts().unwrap();
        let empty = view.propagate_causal_contacts().unwrap().inspect().unwrap();
        assert!(empty.joins.is_empty());
        assert!(empty.internal.center.is_empty());
    }
    let mut latest = None;
    let mut anchor = None;
    for (at, (real, imaginary)) in [(1, 1), (0, 1), (1, -1), (-1, 0), (1, 0)]
        .into_iter()
        .enumerate()
    {
        let input = vec![NativePhaseCurrent::new(real, imaginary, 3).unwrap()];
        let mut occurrence = if at == 3 {
            NativeFieldOccurrence::through_anchor(anchor.as_ref().unwrap(), input)
        } else if let Some(source) = latest.take() {
            NativeFieldOccurrence::through(source, input)
        } else {
            NativeFieldOccurrence::entering(input)
        };
        let next = field.advance_resident(&mut occurrence).unwrap();
        if at == 1 {
            anchor = Some(field.retain_source(&next.source).unwrap());
        }
        if let Some(query) = field.pull_back_material_current(at).unwrap() {
            let response = field.material_contact_response(query).unwrap();
            field
                .apply_material_contact_realization(
                    &response,
                    NativeContactRealization::DyadicDeposit,
                )
                .unwrap();
        }
        latest = Some(next.source);
    }
    let before = field.rest(&[latest.as_ref()], &[anchor.as_ref()]).unwrap();
    {
        let view = field.stage_operative_contacts().unwrap();
        let original = view.inspect().unwrap();
        let census = view.field.census();
        let native = view.propagate_causal_contacts().unwrap();
        assert_eq!(
            native.field.census().section_read_outs,
            census.section_read_outs
        );
        let result = native.inspect().unwrap();
        let reference = CausalContactPropagation::at_enclosed(
            &original.births,
            &original.contacts,
            &original.contacts_radius,
            &original.internal,
            original.fractional_bits,
        )
        .unwrap();
        assert_eq!(result.internal.center, reference.internal.center);
        assert_eq!(result.rounding_radius, reference.rounding_radius);
        assert!(result.internal.radius >= reference.internal.radius);
        let ulp = Rat::new(1.into(), BigInt::one() << original.fractional_bits);
        assert!(&result.internal.radius - &reference.internal.radius < ulp);
        assert_eq!(
            result
                .joins
                .iter()
                .map(|j| (j.before, j.after))
                .collect::<Vec<_>>(),
            reference.joins
        );
        assert_eq!(result.contact_radius, original.contacts_radius);
        for join in result.joins {
            let overlap = original.contacts[join.before]
                .iter()
                .zip(&original.contacts[join.after])
                .fold(ExactComplexWaveCurrent::zero(), |a, (e, f)| {
                    a.add(&e.conjugate().multiply(f))
                });
            assert_eq!(join.overlap, overlap);
            assert_eq!(join.incoming_pair.len(), 2);
            assert_eq!(join.joining_occurrence, original.births[join.after].source);
            assert!(join.incoming_radius >= original.internal.radius);
        }
    }
    assert_eq!(
        field.rest(&[latest.as_ref()], &[anchor.as_ref()]).unwrap(),
        before
    );
}

/// Causal-pullback parity: the device return contains the exact host
/// `CausalContactPropagation::pullback` of the same covector, at zero and positive radius.
#[test]
#[ignore = "requires CUDA; source-qualified sparse overlap return contains the complete exact adjoint"]
fn resident_causal_propagation_returns_the_source_current_and_learned_overlap() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field = make(&surface);
    let mut latest = None;
    for (at, (real, imaginary)) in [(1, 1), (-1, 0), (0, 1), (1, -1)].into_iter().enumerate() {
        let input = vec![NativePhaseCurrent::new(real, imaginary, 3).unwrap()];
        let mut occurrence = if let Some(source) = latest.take() {
            NativeFieldOccurrence::through(source, input)
        } else {
            NativeFieldOccurrence::entering(input)
        };
        latest = Some(field.advance_resident(&mut occurrence).unwrap().source);
        if let Some(query) = field.pull_back_material_current(at).unwrap() {
            let response = field.material_contact_response(query).unwrap();
            field
                .apply_material_contact_realization(
                    &response,
                    NativeContactRealization::DyadicDeposit,
                )
                .unwrap();
        }
    }
    let before = field.rest(&[latest.as_ref()], &[]).unwrap();
    {
        let view = field.stage_operative_contacts().unwrap();
        let original = view.inspect().unwrap();
        let propagated = view.propagate_causal_contacts().unwrap();
        let exact = CausalContactPropagation::at(
            &original.births,
            original.contacts.clone(),
            &original.internal.center,
        )
        .unwrap();
        let values = [(1i64, 1i64), (-1, 0), (0, 1)];
        assert_eq!(values.len(), original.births.len());
        let lambda = values
            .iter()
            .map(|(r, i)| {
                ExactComplexWaveCurrent::new(
                    Rat::from_integer((*r).into()),
                    Rat::from_integer((*i).into()),
                )
            })
            .collect::<Vec<_>>();
        let expected = exact.pullback(&lambda).unwrap();
        // Zero and positive declared receiver uncertainty exercise the same native return.
        for radius in [0i128, 1i128 << (original.fractional_bits - 4)] {
            let mut raw = values
                .iter()
                .flat_map(|(r, i)| {
                    [
                        i128::from(*r) << original.fractional_bits,
                        i128::from(*i) << original.fractional_bits,
                    ]
                })
                .collect::<Vec<_>>();
            raw.push(radius);
            let words = raw
                .iter()
                .flat_map(|v| {
                    let lo = *v as i64;
                    let hi = (*v >> u64::BITS) as i64;
                    [(lo, lo), (hi, hi)]
                })
                .collect::<Vec<_>>();
            let covector = surface
                .mount_section_rest(
                    &ResidentSectionRest::found(1, words.len(), ResidentGrain(0), 64, words)
                        .unwrap(),
                )
                .unwrap();
            let census = propagated.field.census();
            let returned = propagated.pull_back(&covector).unwrap();
            assert_eq!(
                propagated.field.census().section_read_outs,
                census.section_read_outs
            );
            let returned = returned.inspect().unwrap();
            assert!(returned
                .incoming_internal
                .contains(&expected.incoming_internal));
            let difference = returned
                .contact_covector
                .iter()
                .zip(&expected.contacts)
                .flat_map(|(a, b)| a.iter().zip(b))
                .map(|(a, b)| a.subtract(b).norm_square())
                .sum::<Rat>();
            assert!(
                difference <= &returned.contact_covector_radius * &returned.contact_covector_radius
            );
            assert!(returned
                .overlaps
                .iter()
                .any(|v| v != &ExactComplexWaveCurrent::zero()));
            if radius > 0 {
                let aperture = Rat::new(radius.into(), BigInt::one() << original.fractional_bits);
                assert!(returned.incoming_internal.radius >= aperture);
                assert!(returned.incoming_internal.radius < &aperture + &aperture);
                let mut changed = lambda.clone();
                changed[0].real += aperture;
                let changed = exact.pullback(&changed).unwrap();
                assert!(returned
                    .incoming_internal
                    .contains(&changed.incoming_internal));
            }
        }
    }
    assert_eq!(field.rest(&[latest.as_ref()], &[]).unwrap(), before);
}

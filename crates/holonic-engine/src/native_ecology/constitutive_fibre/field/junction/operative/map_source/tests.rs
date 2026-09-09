use super::super::propagation::return_path::NativeCausalContactReturn;
use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::native_ecology::constitutive_fibre::NativeFieldRest;
use num_bigint::BigInt;
use num_traits::One;
use std::collections::BTreeMap;

fn packed<'c>(
    surface: &'c ResidentSurface<'c>,
    rows: usize,
    width: usize,
    values: Vec<i128>,
) -> Rc<ResidentSection<'c>> {
    let words = values
        .into_iter()
        .flat_map(|v| {
            let lo = v as i64;
            let hi = (v >> u64::BITS) as i64;
            [(lo, lo), (hi, hi)]
        })
        .collect::<Vec<_>>();
    assert_eq!(words.len(), rows * width);
    Rc::new(
        surface
            .mount_section_rest(
                &ResidentSectionRest::found(rows, width, ResidentGrain(0), 64, words).unwrap(),
            )
            .unwrap(),
    )
}

fn covector<'c>(surface: &'c ResidentSurface<'c>, count: usize, grain: u32) -> ResidentSection<'c> {
    let unit = 1i128 << grain;
    let mut values = (0..count)
        .flat_map(|i| [unit, if i % 2 == 0 { unit } else { -unit }])
        .collect::<Vec<_>>();
    values.push(0);
    let words = values
        .into_iter()
        .flat_map(|v| {
            let lo = v as i64;
            let hi = (v >> u64::BITS) as i64;
            [(lo, lo), (hi, hi)]
        })
        .collect::<Vec<_>>();
    surface
        .mount_section_rest(
            &ResidentSectionRest::found(1, words.len(), ResidentGrain(0), 64, words).unwrap(),
        )
        .unwrap()
}
fn combined<'c>(
    surface: &'c ResidentSurface<'c>,
    base: &Rc<OperativeReturn<'c>>,
    source: usize,
    h: &NativeCausalContactReturn<'c>,
    count: usize,
) -> Rc<OperativeReturn<'c>> {
    let bounds = Rc::new(surface.fresh_section(1, 4, ResidentGrain(0)).unwrap());
    let mut passage = surface.begin_passage(&[vec![]]).unwrap();
    {
        let lane = passage.open(0, &[]).unwrap();
        surface
            .record_joined_operative_return_bounds(&lane, &base.bounds, &h.bounds, &bounds)
            .unwrap();
    }
    passage.close(0, &bounds, 64).unwrap();
    assert!(passage
        .finish()
        .unwrap()
        .launch()
        .unwrap()
        .obstruction
        .is_empty());
    Rc::new(OperativeReturn {
        at_cut: base.at_cut,
        contact_count: base.contact_count,
        factor_count: base.factor_count,
        realization: base.realization,
        origin: Rc::clone(&base.origin),
        ports: Rc::clone(&base.ports),
        currents: Rc::clone(&base.currents),
        current_difference_source: base.current_difference_source,
        b: base.b.clone(),
        bounds,
        source_overlap: Some(OperativeSourceOverlap {
            source,
            count,
            coefficients: Rc::clone(&h.overlaps),
            errors: Rc::clone(&h.errors),
        }),
    })
}

#[test]
#[ignore = "requires CUDA; source-dependent coefficient expressions, historical producers, birth genes and restart"]
fn source_map_program_keeps_actual_producers_across_returns_archive_and_restart() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let archive = std::env::temp_dir().join(format!(
        "holonics-map-source-{}-{}.history",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let mut field = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
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
    field.enable_history_archive(&archive).unwrap();
    let mut expected = BTreeMap::new();
    let mut overlaps = BTreeMap::<usize, NativeCausalContactReturn<'_>>::new();
    let mut latest = None;
    let mut anchor = None;
    for (at, (r, i)) in [
        (1, 1),
        (-1, 0),
        (0, 1),
        (1, -1),
        (1, 0),
        (0, -1),
        (-1, 1),
        (1, 1),
        (0, 1),
        (1, 0),
    ]
    .into_iter()
    .enumerate()
    {
        let input = vec![NativePhaseCurrent::new(r, i, 3).unwrap()];
        let mut event = if at == 8 {
            NativeFieldOccurrence::through_anchor(anchor.as_ref().unwrap(), input)
        } else if let Some(source) = latest.take() {
            NativeFieldOccurrence::through(source, input)
        } else {
            NativeFieldOccurrence::entering(input)
        };
        let next = field.advance_resident(&mut event).unwrap();
        let observed = next.lineage.observed_source();
        if at == 2 {
            anchor = Some(field.retain_source(&next.source).unwrap());
        }
        // Inspect the actual producing map before its material response. The native sparse
        // return is a declared coefficient-operation control, not a second fixture learner.
        {
            let view = field.stage_operative_contacts().unwrap();
            expected.insert(at, surface.detach_section(&view.sections.map, 64).unwrap());
            let p = view.propagate_causal_contacts().unwrap();
            overlaps.insert(
                at,
                p.pull_back(&covector(&surface, view.births.len(), view.grain))
                    .unwrap(),
            );
        }
        if let Some(query) = field.pull_back_material_current(at).unwrap() {
            let response = field.material_contact_response(query).unwrap();
            if at >= 5 {
                let source = observed.unwrap();
                let h = &overlaps[&source];
                let base = field
                    .prepare_material_contact_return(
                        &response,
                        NativeContactRealization::DyadicDeposit,
                    )
                    .unwrap();
                let returned = combined(&surface, &base, source, h, base.factor_count);
                if at == 5 {
                    // A product fits the wider hand, but its projected value exceeds the
                    // signed current hand. Refusal must precede publication of the anchor.
                    let preserved = field
                        .rest(&[Some(&next.source)], &[anchor.as_ref()])
                        .unwrap();
                    let d = 6 * field.nodes();
                    let exponent = (i128::BITS - 1 + field.transport_grain().unwrap()) / 2 + 1;
                    let mut ports = vec![0i128; 2 * d];
                    ports[0] = 1i128 << exponent;
                    let mut factors = vec![0i128; 4 * base.factor_count];
                    factors[0] = 1i128 << exponent;
                    let mut bad = combined(&surface, &base, source, h, base.factor_count);
                    let b = Rc::get_mut(&mut bad).unwrap();
                    b.current_difference_source = None;
                    b.ports = packed(&surface, 2, 2 * d, ports);
                    b.currents = packed(&surface, 2, 4 * base.factor_count, factors);
                    assert!(field
                        .stage_operative_contacts()
                        .unwrap()
                        .stage_return(bad)
                        .is_err());
                    assert_eq!(
                        field
                            .rest(&[Some(&next.source)], &[anchor.as_ref()])
                            .unwrap(),
                        preserved
                    );
                }
                let before = field.stage_operative_contacts().unwrap().inspect().unwrap();
                let ordinary = response.inspect().unwrap().contact_covector;
                let extra = h.inspect().unwrap().contact_covector;
                let scale = Rat::from_integer(BigInt::one() << before.fractional_bits);
                let mut expected_after = before.contacts.clone();
                for row in 0..base.factor_count {
                    for (j, (a, b)) in ordinary
                        .contact(row)
                        .unwrap()
                        .iter()
                        .zip(&extra[row])
                        .enumerate()
                    {
                        let gradient = a.add(b);
                        let q = |v: &Rat| {
                            Rat::new(
                                (v * &scale).to_integer(),
                                BigInt::one() << before.fractional_bits,
                            )
                        };
                        expected_after[row][j] =
                            expected_after[row][j].add(&ExactComplexWaveCurrent::new(
                                q(&gradient.real),
                                q(&gradient.imaginary),
                            ));
                    }
                }
                let update = field
                    .stage_operative_contacts()
                    .unwrap()
                    .stage_return(returned)
                    .unwrap()
                    .into_update();
                let op = field.junction.as_mut().unwrap().operative.as_mut().unwrap();
                op.sections = update.0;
                op.origin = update.1;
                op.returns = update.2;
                op.program = update.3;
                assert_eq!(
                    field
                        .stage_operative_contacts()
                        .unwrap()
                        .inspect()
                        .unwrap()
                        .contacts,
                    expected_after
                );
                field
                    .inspect_contact_deposit(field.operative_return_count().unwrap() - 1)
                    .unwrap();
            } else {
                field
                    .apply_material_contact_realization(
                        &response,
                        NativeContactRealization::DyadicDeposit,
                    )
                    .unwrap();
            }
        }
        latest = Some(next.source);
        field
            .junction
            .as_mut()
            .unwrap()
            .operative
            .as_mut()
            .unwrap()
            .recent_producers
            .clear();
        for (&source, expected) in &expected {
            let before = field.census();
            let map = field.operative_producing_map(source).unwrap();
            assert_eq!(field.census().section_read_outs, before.section_read_outs);
            assert_eq!(
                surface.detach_section(&map, 64).unwrap(),
                *expected,
                "source {source} at cut {at}"
            );
        }
    }
    let program = field
        .junction
        .as_ref()
        .unwrap()
        .operative
        .as_ref()
        .unwrap()
        .program
        .as_ref()
        .unwrap();
    assert_eq!(program.at_cut, 6);
    assert_eq!(program.births.len(), 4);
    let storage = field.operative_return_storage().unwrap();
    assert!(storage.source_overlap_octets > 0);
    assert!(storage.map_source_octets > 0);
    {
        // A different earlier source can satisfy the numeric domain and still be the wrong
        // causal source. The complete cold field checks the actual receiving lineage.
        let op = field.junction.as_ref().unwrap().operative.as_ref().unwrap();
        let index = op
            .returns
            .iter()
            .position(|r| r.source_overlap.as_ref().is_some_and(|h| h.source == 2))
            .unwrap();
        let original = Rc::clone(&op.returns[index]);
        let mut changed = original.source_overlap.clone().unwrap();
        changed.source = 3;
        let bad = Rc::new(OperativeReturn {
            at_cut: original.at_cut,
            contact_count: original.contact_count,
            factor_count: original.factor_count,
            realization: original.realization,
            origin: Rc::clone(&original.origin),
            ports: Rc::clone(&original.ports),
            currents: Rc::clone(&original.currents),
            current_difference_source: original.current_difference_source,
            b: original.b.clone(),
            bounds: Rc::clone(&original.bounds),
            source_overlap: Some(changed),
        });
        field
            .junction
            .as_mut()
            .unwrap()
            .operative
            .as_mut()
            .unwrap()
            .returns[index] = bad;
        assert!(field.rest(&[latest.as_ref()], &[anchor.as_ref()]).is_err());
        field
            .junction
            .as_mut()
            .unwrap()
            .operative
            .as_mut()
            .unwrap()
            .returns[index] = original;
    }
    field
        .archive_history_before(field.occurrence_count())
        .unwrap();
    for (&source, expected) in &expected {
        let map = field.operative_producing_map(source).unwrap();
        assert_eq!(surface.detach_section(&map, 64).unwrap(), *expected);
    }
    let saved = field.rest(&[latest.as_ref()], &[anchor.as_ref()]).unwrap();
    let mut bytes = Vec::new();
    saved.write(&mut bytes).unwrap();
    drop(overlaps);
    drop(latest);
    drop(anchor);
    drop(field);
    let saved = NativeFieldRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    let (field, _, _) = NativeConstitutiveField::remount(&surface, saved).unwrap();
    for (source, expected) in expected {
        let map = field.operative_producing_map(source).unwrap();
        assert_eq!(surface.detach_section(&map, 64).unwrap(), expected);
    }
}

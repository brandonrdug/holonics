use super::*;
use holonic_engine::native_ecology::constitutive_fibre::{
    NativeContactRealization, NativeFieldCurrentBall, NativeFieldEmission, NativeFieldOccurrence,
    NativeFieldRest, NativeMaterialPullbackMetric, NativeMaterialResponseChart, NativePhaseCurrent,
};
use holonic_engine::resident_section::SeriesAperture;

fn spec() -> NativeFieldModelSpec {
    // Two declared interacting ports, each with its own retained standing. These are a finite
    // current comparison, not characters, acoustic samples or an intrinsic semantic dimension.
    NativeFieldModelSpec {
        material: vec![
            NativeJunctionSeed {
                incoming_admittance: 1,
                held_admittance: 1,
                incoming_transport: NativePhaseCurrent::unit(),
                initial_held: NativePhaseCurrent::zero(),
            };
            2
        ],
        junction: Some(NativeFieldJunctionSpec {
            representation: NativeFieldJunctionRepresentation::EnclosedDyadic {
                fractional_bits: 72,
            },
            solver: NativeFieldJunctionSolver::Full,
        }),
        material_transport: Some(NativeFieldMaterialSpec {
            source: NativeMaterialTransportSource::OperativeContextual,
            target: NativeMaterialTarget::DirectCurrent,
        }),
    }
}

fn receive(field: &mut NativeConstitutiveField<'_>) -> NativeFieldEmission {
    let mut previous = None;
    let mut anchor = None;
    for (at, components) in [
        [(1, 1), (0, 1)],
        [(0, 1), (1, 0)],
        [(1, 0), (0, -1)],
        [(0, 0), (1, 1)],
        [(1, 0), (0, 0)],
    ]
    .into_iter()
    .enumerate()
    {
        let incoming = components
            .into_iter()
            .map(|(r, i)| NativePhaseCurrent::new(r, i, 1).unwrap())
            .collect();
        let mut occurrence = if at == 2 {
            NativeFieldOccurrence::through_anchor(anchor.as_ref().unwrap(), incoming)
        } else if let Some(source) = previous.take() {
            NativeFieldOccurrence::through(source, incoming)
        } else {
            NativeFieldOccurrence::entering(incoming)
        };
        let before = field.census();
        let next = field.advance_resident(&mut occurrence).unwrap();
        assert_eq!(field.census().section_read_outs, before.section_read_outs);
        if at == 0 {
            anchor = Some(field.retain_source(&next.source).unwrap());
            let (response, seen) = field
                .respond_to_material_observation(
                    0,
                    NativeMaterialResponseChart::ComplexCurrent,
                    NativeContactRealization::DyadicDeposit,
                    |_, _| panic!("unobserved source"),
                )
                .unwrap();
            assert!(response.is_none() && seen.is_none());
        }
        previous = Some(next.source);
    }
    assert_eq!(field.lineage(2).unwrap().received_from, Some(0));
    assert_eq!(field.lineage(2).unwrap().predecessor_state, Some(1));
    previous.unwrap()
}

fn conduct(
    chart: NativeMaterialResponseChart,
    composed: bool,
    develop: bool,
) -> (NativeFieldRest, NativeFieldCurrentBall) {
    with_native_field(&spec(), |field| -> Result<_, NativeSessionError> {
        let source = receive(field);
        let receiving = field.occurrence_count() - 1;
        let retained = field.rest(&[Some(&source)], &[])?;
        assert!(field
            .respond_to_material_observation(
                receiving - 1,
                chart,
                NativeContactRealization::DyadicDeposit,
                |_, _| (),
            )
            .is_err());
        assert_eq!(field.rest(&[Some(&source)], &[])?, retained);
        let before = field.census();
        if !develop {
            // Matched source/material history with this one local contact return withheld.
        } else if composed {
            let returns = field.operative_return_count();
            let (response, seen) = field.respond_to_material_observation(
                receiving,
                chart,
                NativeContactRealization::DyadicDeposit,
                |old, _| {
                    assert_eq!(old.operative_return_count(), returns);
                    old.occurrence_count()
                },
            )?;
            assert!(response.is_some());
            assert_eq!(seen, Some(receiving + 1));
        } else {
            let query = match chart {
                NativeMaterialResponseChart::ComplexCurrent => {
                    field.pull_back_material_current(receiving)?.unwrap()
                }
                NativeMaterialResponseChart::RelativeEntropy {
                    group_width,
                    series,
                }
                | NativeMaterialResponseChart::SquaredProbability {
                    group_width,
                    series,
                } => {
                    let returned = field
                        .normalized_material_return(receiving, group_width, series)?
                        .unwrap();
                    let metric =
                        if matches!(chart, NativeMaterialResponseChart::RelativeEntropy { .. }) {
                            NativeMaterialPullbackMetric::RelativeEntropy
                        } else {
                            NativeMaterialPullbackMetric::SquaredProbability
                        };
                    field.pull_back_material_source(&returned, metric)?
                }
            };
            let response = field.material_contact_response(query)?;
            field.apply_material_contact_realization(
                &response,
                NativeContactRealization::DyadicDeposit,
            )?;
        }
        assert_eq!(field.census().section_read_outs, before.section_read_outs);
        assert_eq!(field.operative_return_count(), Some(usize::from(develop)));
        let mut followup = NativeFieldOccurrence::through(
            source,
            vec![
                NativePhaseCurrent::unit(),
                NativePhaseCurrent::new(0, 1, 1)?,
            ],
        );
        field.advance_resident(&mut followup)?;
        let forward = field
            .inspect_contextual_material_transport(field.occurrence_count() - 1)?
            .unwrap()
            .forward;
        Ok((field.rest(&[], &[])?, forward))
    })
    .unwrap()
}

#[test]
#[ignore = "requires CUDA; generic assembly/return must preserve the complete conditioned successor"]
fn field_assembly_matches_explicit_current_and_normalized_returns() {
    for chart in [
        NativeMaterialResponseChart::ComplexCurrent,
        NativeMaterialResponseChart::RelativeEntropy {
            group_width: 2,
            series: SeriesAperture(32),
        },
        NativeMaterialResponseChart::SquaredProbability {
            group_width: 2,
            series: SeriesAperture(32),
        },
    ] {
        assert_eq!(conduct(chart, true, true), conduct(chart, false, true));
    }
}

#[test]
#[ignore = "requires CUDA; a field recipe cannot silently replace its declared solver"]
fn operative_recipe_refuses_an_incompatible_solver() {
    let mut seed = spec();
    seed.junction.as_mut().unwrap().solver = NativeFieldJunctionSolver::BalancedPairs;
    let result = with_native_field(&seed, |_| -> Result<(), NativeSessionError> {
        panic!("incompatible recipe reached the operation")
    });
    assert!(result.is_err());
}

#[test]
#[ignore = "requires CUDA; scalar, rational-paired and enclosed factories retain their admitted laws"]
fn field_recipe_preserves_all_existing_junction_representations() {
    for representation in [
        None,
        Some(NativeFieldJunctionRepresentation::RationalWords),
        Some(NativeFieldJunctionRepresentation::EnclosedDyadic {
            fractional_bits: 72,
        }),
    ] {
        let mut seed = spec();
        seed.material_transport = None;
        seed.junction = representation.map(|representation| NativeFieldJunctionSpec {
            representation,
            solver: NativeFieldJunctionSolver::Full,
        });
        with_native_field(&seed, |field| -> Result<(), NativeSessionError> {
            assert_eq!(field.junction_representation(), representation);
            let first = field.advance_resident(&mut NativeFieldOccurrence::entering(vec![
                NativePhaseCurrent::unit(),
                NativePhaseCurrent::zero(),
            ]))?;
            assert_eq!(first.lineage.occurrence, 0);
            assert_eq!(first.lineage.received_from, None);
            Ok(())
        })
        .unwrap();
    }
}

#[test]
#[ignore = "requires CUDA; one source-qualified local return changes a later material-current family"]
fn local_return_has_a_separated_later_consequence() {
    let (_, before) = conduct(NativeMaterialResponseChart::ComplexCurrent, true, false);
    let (_, after) = conduct(NativeMaterialResponseChart::ComplexCurrent, true, true);
    let distance_square: num_rational::BigRational = before
        .center
        .iter()
        .zip(&after.center)
        .map(|(a, b)| a.subtract(b).norm_square())
        .sum();
    let radius = &before.radius + &after.radius;
    assert!(distance_square > &radius * &radius);
    println!(
        "{}",
        serde_json::json!({
            "grade":"established-bounded", "evidence":["implemented-exact","computational-witness"],
            "scope":"Two independently founded matched fields; same situated current occurrences, one local contact return withheld. Complete later material balls separate. No medium or semantic label is supplied.",
            "source_profile":"operative-contextual", "current_chart":"complex-current",
            "before":before,"after":after,"distance_square":distance_square,
            "sum_radius_square":&radius*&radius,
        })
    );
}

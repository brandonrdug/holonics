use super::*;
use crate::{HnaStream, HnaStreamCommand, HnaStreamRequest, HNA_STREAM_REQUEST_SCHEMA};
use num_traits::Zero;
use std::io::Cursor;

fn row(values: &[i64]) -> Vec<RationalWire> {
    values.iter().map(|v| RationalWire::integer(*v)).collect()
}
fn rows(values: &[&[i64]]) -> RationalMatrixWire {
    values.iter().map(|r| row(r)).collect()
}
fn construct() -> MathematicalRequest {
    MathematicalRequest::ConstructBilinear {
        target: BilinearTargetWire {
            left_extent: 2,
            right_extent: 2,
            coefficients: rows(&[&[1, 0, 0, -1], &[0, 1, 1, 0]]),
        },
        construction: BilinearConstructionWire::Search {
            left_forms: rows(&[&[1, 0], &[0, 1], &[1, 1], &[1, -1]]),
            right_forms: rows(&[&[1, 0], &[0, 1], &[1, 1], &[1, -1]]),
            min_products: 1,
            max_products: 3,
            max_candidates: 1000,
        },
    }
}
fn send(
    session: &mut NativeMathematicalSession<'_>,
    stream: &mut HnaStream,
    request: MathematicalRequest,
) -> Value {
    let request = HnaStreamRequest {
        schema: HNA_STREAM_REQUEST_SCHEMA.into(),
        command: HnaStreamCommand::MathematicalRequest { request },
    };
    let mut bytes = serde_json::to_vec(&request).unwrap();
    bytes.push(b'\n');
    let mut output = Vec::new();
    stream
        .pump_mathematical(session, &mut Cursor::new(bytes), &mut output)
        .unwrap();
    serde_json::from_slice(&output).unwrap()
}
fn output(value: &Value) -> Vec<BigRational> {
    vector(&serde_json::from_value::<Vec<RationalWire>>(value["value"]["output"].clone()).unwrap())
        .unwrap()
}

fn calibrated_sum_products() -> MathematicalRequest {
    // Caller-supplied chart F(x,h)=x0*h0+x1*h1. These rows specify the action;
    // h remains unknown. Inference of h is performed by the native joint-image owner.
    let mut calibration = Vec::new();
    for axis in 0..4 {
        let mut basis = [0; 4];
        basis[axis] = 1;
        calibration.push(RelationCalibrationWire {
            source: row(&[0; 4]),
            condition: row(&basis),
            observed: row(&[0, 0]),
        });
        calibration.push(RelationCalibrationWire {
            source: row(&basis),
            condition: row(&[0; 4]),
            observed: row(&[0, 0]),
        });
    }
    for i in 0..2 {
        for j in 0..2 {
            for phase in 0..2 {
                let mut source = [0; 4];
                source[2 * i + phase] = 1;
                let mut condition = [0; 4];
                condition[2 * j] = 1;
                let mut observed = [0; 2];
                if i == j {
                    observed[phase] = 1;
                }
                calibration.push(RelationCalibrationWire {
                    source: row(&source),
                    condition: row(&condition),
                    observed: row(&observed),
                });
            }
        }
    }
    MathematicalRequest::ConstructRelation {
        source_complex: 2,
        condition_complex: 2,
        target_complex: 1,
        calibration,
        initial_source: row(&[1, 0, 0, 0]),
        initial_observed: row(&[2, 3]),
    }
}

#[test]
#[ignore = "requires CUDA; native parameter inference preserves the unresolved family and predicts new inputs"]
fn public_relation_refines_unknown_coefficients_and_predicts_new_input() {
    with_mathematical_session(|session| {
        let mut stream = HnaStream::new();
        let constructed = send(session, &mut stream, calibrated_sum_products());
        assert_eq!(constructed["event"], "mathematical-return", "{constructed}");
        let family = &constructed["value"]["condition_family"];
        assert_eq!(family["kind"], "compatible");
        assert_eq!(
            family["directions"].as_array().unwrap().len(),
            2,
            "{family}"
        );
        let prediction = send(
            session,
            &mut stream,
            MathematicalRequest::PredictRelation {
                relation: 0,
                source: MathematicalInputWire::Values {
                    values: row(&[0, 0, 1, 0]),
                },
                retain_prediction: true,
            },
        );
        assert_eq!(prediction["event"], "mathematical-return", "{prediction}");
        assert_eq!(
            prediction["value"]["reading"]["supported_outputs"]["kind"],
            "plural"
        );
        assert_eq!(
            prediction["value"]["reading"]["coverage"]["kind"],
            "complete"
        );
        let pending = prediction["value"]["prediction"].as_u64().unwrap();
        let overwritten = send(
            session,
            &mut stream,
            MathematicalRequest::PredictRelation {
                relation: 0,
                source: MathematicalInputWire::Values {
                    values: row(&[1, 0, 0, 0]),
                },
                retain_prediction: true,
            },
        );
        assert_eq!(overwritten["event"], "refused");
        // Pure prediction is not blocked by a live observation cut or a plural coefficient family.
        let known = send(
            session,
            &mut stream,
            MathematicalRequest::PredictRelation {
                relation: 0,
                source: MathematicalInputWire::Values {
                    values: row(&[2, 0, 0, 0]),
                },
                retain_prediction: false,
            },
        );
        assert_eq!(
            known["value"]["reading"]["supported_outputs"]["kind"], "unique",
            "{known}"
        );
        let known_output: Vec<RationalWire> = serde_json::from_value(
            known["value"]["reading"]["supported_outputs"]["current"].clone(),
        )?;
        assert_eq!(vector(&known_output)?, vector(&row(&[4, 6]))?);
        let failed = send(
            session,
            &mut stream,
            MathematicalRequest::ObserveRelation {
                relation: 0,
                prediction: pending,
                observed: row(&[5]),
            },
        );
        assert_eq!(failed["event"], "refused");
        let refined = send(
            session,
            &mut stream,
            MathematicalRequest::ObserveRelation {
                relation: 0,
                prediction: pending,
                observed: row(&[5, -1]),
            },
        );
        assert_eq!(refined["event"], "mathematical-return", "{refined}");
        assert_eq!(
            refined["value"]["condition_family"]["directions"]
                .as_array()
                .unwrap()
                .len(),
            0
        );
        let coefficients: Vec<RationalWire> =
            serde_json::from_value(refined["value"]["condition_family"]["particular"].clone())?;
        assert_eq!(vector(&coefficients)?, vector(&row(&[2, 3, 5, -1]))?);
        let next = send(
            session,
            &mut stream,
            MathematicalRequest::PredictRelation {
                relation: 0,
                source: MathematicalInputWire::Values {
                    values: row(&[2, 0, 0, 1]),
                },
                retain_prediction: false,
            },
        );
        let next_output: Vec<RationalWire> = serde_json::from_value(
            next["value"]["reading"]["supported_outputs"]["current"].clone(),
        )?;
        assert_eq!(vector(&next_output)?, vector(&row(&[5, 11]))?);
        // An actual resident operator output enters this same family without host remounting
        // or padding to a text alphabet. The 4-coordinate rectangular source map is supplied.
        send(
            session,
            &mut stream,
            MathematicalRequest::ConstructLinear {
                coefficients: rows(&[&[1, 0], &[0, 0], &[0, 0], &[0, 1]]),
            },
        );
        send(
            session,
            &mut stream,
            MathematicalRequest::Apply {
                operator: 0,
                left: row(&[2, 1]),
                right: None,
                retain_product: true,
            },
        );
        let native_source = send(
            session,
            &mut stream,
            MathematicalRequest::PredictRelation {
                relation: 0,
                source: MathematicalInputWire::ProductOutput { product: 0 },
                retain_prediction: false,
            },
        );
        assert_eq!(
            native_source["event"], "mathematical-return",
            "{native_source}"
        );
        assert_eq!(native_source["value"]["reading"], next["value"]["reading"]);
        assert_eq!(
            native_source["value"]["cost"]["census_before"]["ingress_octets"],
            native_source["value"]["cost"]["census_after"]["ingress_octets"],
            "no returned source remount: {native_source}"
        );
        // Closed constraints, not the operation word, carry this family's continuation.
        let standing_bytes = session.surface.census().resident_octets_now;
        for _ in 0..8 {
            let p = send(
                session,
                &mut stream,
                MathematicalRequest::PredictRelation {
                    relation: 0,
                    source: MathematicalInputWire::ProductOutput { product: 0 },
                    retain_prediction: true,
                },
            );
            let id = p["value"]["prediction"].as_u64().unwrap();
            let r = send(
                session,
                &mut stream,
                MathematicalRequest::ObserveRelation {
                    relation: 0,
                    prediction: id,
                    observed: row(&[5, 11]),
                },
            );
            assert_eq!(r["event"], "mathematical-return", "{r}");
            assert_eq!(session.surface.census().resident_octets_now, standing_bytes);
        }
        let stale = send(
            session,
            &mut stream,
            MathematicalRequest::ObserveRelation {
                relation: 0,
                prediction: pending,
                observed: row(&[0, 0]),
            },
        );
        assert_eq!(stale["event"], "refused");
        Ok(())
    })
    .unwrap();
}

#[test]
fn mathematical_wire_keeps_exact_coefficients_and_refuses_extra_fields() {
    let request = construct();
    let value = serde_json::to_value(&request).unwrap();
    assert_eq!(
        serde_json::from_value::<MathematicalRequest>(value.clone()).unwrap(),
        request
    );
    let mut bad = value;
    bad["target"]["task_label"] = json!("expected answer");
    assert!(serde_json::from_value::<MathematicalRequest>(bad).is_err());
    assert!(matrix(&vec![row(&[1]), row(&[1, 2])]).is_err());
    assert!(matrix(&vec![vec![RationalWire {
        numerator: "1".into(),
        denominator: "0".into()
    }]])
    .is_err());
}

#[test]
#[ignore = "requires CUDA; caller-controlled construction/application through public JSONL"]
fn public_requests_construct_apply_change_receiver_and_reuse() {
    with_mathematical_session(|session| {
        let mut stream = HnaStream::new();
        let built = send(session, &mut stream, construct());
        assert_eq!(built["event"], "mathematical-return", "{built}");
        assert_eq!(built["value"]["factors"]["products"], 3);
        assert_eq!(built["value"]["operator"], 0);
        for (left, right, expected) in [([2, 3], [4, 5], [-7, 22]), ([-3, 7], [2, -1], [1, 17])] {
            let value = send(
                session,
                &mut stream,
                MathematicalRequest::Apply {
                    operator: 0,
                    left: row(&left),
                    right: Some(row(&right)),
                    retain_product: false,
                },
            );
            assert_eq!(value["event"], "mathematical-return", "{value}");
            assert_eq!(output(&value), vector(&row(&expected)).unwrap());
            assert_eq!(value["value"]["intermediate_section_readouts"], 0);
            assert_eq!(session.products.len(), 0);
        }
        let applied = send(
            session,
            &mut stream,
            MathematicalRequest::Apply {
                operator: 0,
                left: row(&[2, 3]),
                right: Some(row(&[4, 5])),
                retain_product: true,
            },
        );
        let product = applied["value"]["product"].as_u64().unwrap();
        let changed = send(
            session,
            &mut stream,
            MathematicalRequest::BindReceiver {
                operator: 0,
                coefficients: rows(&[&[1, 0, 0, 0], &[0, 1, 1, 0], &[0, 0, 0, 1]]),
            },
        );
        assert_eq!(changed["value"]["operator"], 1, "{changed}");
        let read = send(
            session,
            &mut stream,
            MathematicalRequest::ReadProduct {
                operator: 1,
                product,
            },
        );
        assert_eq!(output(&read), vector(&row(&[8, 22, 15])).unwrap());
        assert_eq!(read["value"]["source_products_recomputed"], false);
        assert_eq!(read["value"]["intermediate_section_readouts"], 0);
        let composed = send(
            session,
            &mut stream,
            MathematicalRequest::ComposeReceiver {
                operator: 1,
                matrix: rows(&[&[0, 1, 0]]),
            },
        );
        assert_eq!(composed["value"]["operator"], 2);
        let read = send(
            session,
            &mut stream,
            MathematicalRequest::ReadProduct {
                operator: 2,
                product,
            },
        );
        assert_eq!(output(&read), vector(&row(&[22])).unwrap());
        send(
            session,
            &mut stream,
            MathematicalRequest::ReleaseProduct { product },
        );
        let absent = send(
            session,
            &mut stream,
            MathematicalRequest::ReadProduct {
                operator: 2,
                product,
            },
        );
        assert_eq!(absent["event"], "refused");
        Ok(())
    })
    .unwrap();
}

#[test]
#[ignore = "requires CUDA; linear rank lowering and zero-map receiver family"]
fn linear_and_zero_actions_have_explicit_unit_port_and_derived_rank() {
    with_mathematical_session(|session| {
        let linear = session.request(&MathematicalRequest::ConstructLinear {
            coefficients: rows(&[&[1, 2], &[2, 4]]),
        })?;
        assert_eq!(linear["derived_rank"], 1);
        let result = session.request(&MathematicalRequest::Apply {
            operator: 0,
            left: row(&[3, 7]),
            right: None,
            retain_product: true,
        })?;
        assert_eq!(
            vector(&serde_json::from_value::<Vec<RationalWire>>(
                result["output"].clone()
            )?)
            .unwrap(),
            vector(&row(&[17, 34])).unwrap()
        );
        let zero = session.request(&MathematicalRequest::ConstructLinear {
            coefficients: rows(&[&[0, 0]]),
        })?;
        assert_eq!(zero["derived_rank"], 0);
        assert_eq!(zero["factors"]["products"], 1);
        assert_eq!(
            zero["factors"]["receiver_family"]["free_row_directions"]
                .as_array()
                .unwrap()
                .len(),
            1
        );
        assert!(
            session
                .request(&MathematicalRequest::ReadProduct {
                    operator: 1,
                    product: 0
                })
                .is_err(),
            "same output/shape does not identify product cores"
        );
        let result = session.request(&MathematicalRequest::Apply {
            operator: 1,
            left: row(&[5, -9]),
            right: None,
            retain_product: false,
        })?;
        assert_eq!(
            vector(&serde_json::from_value::<Vec<RationalWire>>(
                result["output"].clone()
            )?)
            .unwrap(),
            vector(&row(&[0])).unwrap()
        );
        Ok(())
    })
    .unwrap();
}

#[test]
#[ignore = "requires CUDA; finite search continuation and receiver separators"]
fn search_continuation_is_not_exhaustion_and_failed_receiver_does_not_change_material() {
    with_mathematical_session(|session| {
        let mut request = construct();
        if let MathematicalRequest::ConstructBilinear {
            construction: BilinearConstructionWire::Search { max_candidates, .. },
            ..
        } = &mut request
        {
            *max_candidates = 1;
        }
        let first = session.request(&request)?;
        assert_eq!(first["status"], "search-pending");
        let next = session.request(&MathematicalRequest::ResumeConstruction {
            search: 0,
            max_candidates: 1000,
        })?;
        assert_eq!(next["status"], "constructed");
        assert!(next["examined_supports"].as_u64().unwrap() > 1);
        let simple = session.request(&MathematicalRequest::ConstructBilinear {
            target: BilinearTargetWire {
                left_extent: 2,
                right_extent: 1,
                coefficients: rows(&[&[1, 0]]),
            },
            construction: BilinearConstructionWire::Core {
                left_forms: rows(&[&[1, 0]]),
                right_forms: rows(&[&[1]]),
            },
        })?;
        assert_eq!(simple["operator"], 1);
        let obstruction = session.request(&MathematicalRequest::BindReceiver {
            operator: 1,
            coefficients: rows(&[&[0, 1]]),
        })?;
        assert_eq!(obstruction["status"], "obstructed");
        assert_eq!(session.operators.len(), 2);
        assert!(vector(&serde_json::from_value::<Vec<RationalWire>>(
            obstruction["returned"].clone()
        )?)
        .unwrap()
        .iter()
        .any(|q| !q.is_zero()));
        assert!(session
            .request(&MathematicalRequest::Apply {
                operator: 1,
                left: row(&[1]),
                right: Some(row(&[1])),
                retain_product: true
            })
            .is_err());
        assert!(session.products.is_empty());
        Ok(())
    })
    .unwrap();
}

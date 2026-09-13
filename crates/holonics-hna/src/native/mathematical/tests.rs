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

#[test]
#[ignore = "requires CUDA; one preparation feeds source/condition restrictions and the native normal law emits a whole contextual section"]
fn contextual_section_uses_pre_target_restrictions_and_returns_new_input_faces() {
    let readout=ResidentReadout::new().unwrap();
    let surface=ResidentSurface::on(&readout).unwrap();
    let mut session=NativeMathematicalSession::on(&surface);
    let mut stream=HnaStream::new();
    let a=send(&mut session,&mut stream,MathematicalRequest::ConstructLinear {coefficients:rows(&[
        &[1,0,0,0,0,0],&[0,1,0,0,0,0],&[0,0,1,0,0,0],&[0,0,0,1,0,0]])});
    let c=send(&mut session,&mut stream,MathematicalRequest::ConstructLinear {coefficients:rows(&[
        &[0,0,0,0,1,0],&[0,0,0,0,0,1]])});
    let a=a["value"]["operator"].as_u64().unwrap();
    let c=c["value"]["operator"].as_u64().unwrap();
    let built=send(&mut session,&mut stream,MathematicalRequest::ConstructPredictor {
        source_operator:a,condition_operator:c,target_complex:2,fractional_bits:32});
    let id=built["value"]["predictor"].as_u64().unwrap();
    assert_eq!(built["value"]["feature_complex"],5); // not a three-port padding
    let read_ball=|value:&Value| {
        let q=|v:&Value|serde_json::from_value::<RationalWire>(v.clone()).unwrap().rational().unwrap();
        (value["center"].as_array().unwrap().iter().map(|v|(q(&v["real"]),q(&v["imaginary"]))).collect::<Vec<_>>(),q(&value["radius"]))
    };
    // Given examples specify a conditional exchange. Source and condition are read before
    // the corresponding target; the driver supplies no coefficients or fitted answer.
    for (i,(left,right,condition,y0,y1)) in [
        (1,0,1,1,0),(1,0,-1,0,1),(0,1,1,0,1),(0,1,-1,1,0)
    ].into_iter().enumerate() {
        let prediction=send(&mut session,&mut stream,MathematicalRequest::PredictSection {
            predictor:id,preparation:MathematicalInputWire::Values {values:row(&[left,0,right,0,condition,0])},retain_prediction:true});
        assert_eq!(prediction["value"]["observations"],i);
        assert_eq!(prediction["value"]["intermediate_section_readouts"],0);
        if i==0 { let (v,r)=read_ball(&prediction["value"]["output"]); assert!(r.is_zero());assert!(v.iter().all(|(r,i)|r.is_zero()&&i.is_zero())); }
        let pending=prediction["value"]["prediction"].as_u64().unwrap();
        let received=send(&mut session,&mut stream,MathematicalRequest::ObserveSection {predictor:id,prediction:pending,observed:row(&[y0,0,y1,0])});
        assert_eq!(received["value"]["observations"],i+1);
        assert!(session.request(&MathematicalRequest::ObserveSection {predictor:id,prediction:pending,observed:row(&[y0,0,y1,0])}).is_err());
    }
    // Independent consequence of H=I+sum uu*, B=sum vu*: the two nonzero rows
    // are (1,1,0,1,-1)/3 and (1,1,0,-1,1)/3. No solve/readback feeds the model.
    for (condition,want) in [(1,[4,-2]),(-1,[-2,4])] {
        let prediction=send(&mut session,&mut stream,MathematicalRequest::PredictSection {
            predictor:id,preparation:MathematicalInputWire::Values {values:row(&[2,0,-1,0,condition,0])},retain_prediction:false});
        let (v,r)=read_ball(&prediction["value"]["output"]);
        let error:BigRational=v.iter().zip(want).map(|((re,im),w)| {
            let d=re-BigRational::new(w.into(),3.into());&d*&d+im*im
        }).sum();
        assert!(error<=&r*&r,"contextual section missed the normal-system consequence: {prediction}");
        assert!(r<BigRational::new(1.into(),1000.into()));
        assert_eq!(prediction["value"]["intermediate_section_readouts"],0);
    }
    assert!(session.request(&MathematicalRequest::ReleaseOperator {operator:a}).is_err());
    send(&mut session,&mut stream,MathematicalRequest::ReleasePredictor {predictor:id});
    send(&mut session,&mut stream,MathematicalRequest::ReleaseOperator {operator:a});
}

fn calibrated_sum_products() -> MathematicalRequest {
    calibrated_dot(2, &[2, 3])
}
fn calibrated_dot(complex: usize, initial: &[i64]) -> MathematicalRequest {
    // Caller-supplied chart F(x,h)=x0*h0+x1*h1. These rows specify the action;
    // h remains unknown. Inference of h is performed by the native joint-image owner.
    let mut calibration = Vec::new();
    let width = 2 * complex;
    for axis in 0..width {
        let mut basis = vec![0; width];
        basis[axis] = 1;
        calibration.push(RelationCalibrationWire {
            source: row(&vec![0; width]),
            condition: row(&basis),
            observed: row(&[0, 0]),
        });
        calibration.push(RelationCalibrationWire {
            source: row(&basis),
            condition: row(&vec![0; width]),
            observed: row(&[0, 0]),
        });
    }
    for i in 0..complex {
        for j in 0..complex {
            for phase in 0..2 {
                let mut source = vec![0; width];
                source[2 * i + phase] = 1;
                let mut condition = vec![0; width];
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
    let mut initial_source = vec![0; width];
    initial_source[0] = 1;
    MathematicalRequest::ConstructRelation {
        source_complex: complex,
        condition_complex: complex,
        target_complex: 1,
        calibration,
        initial_source: row(&initial_source),
        initial_observed: row(initial),
    }
}

#[test]
#[ignore = "requires CUDA; one uncertain release source produces a joint future and is refined by a landing"]
fn public_joint_release_predicts_correlated_futures_before_selecting_a_source() {
    use holonic_engine::exact_linear::ConstantAccelerationRelease;
    with_mathematical_session(|session| {
        let mut stream = HnaStream::new();
        // One SI chart: h=(position, velocity, acceleration, impulse), each a planar
        // complex pair. Initial position is (0,1); velocity and gravity are supplied
        // by observations of the same calibration law, while impulse remains unknown.
        let declared = send(session, &mut stream, calibrated_dot(4, &[0, 1]));
        assert_eq!(declared["event"], "mathematical-return", "{declared}");
        for (axis, value) in [(1, [0, 0]), (2, [0, -10])] {
            let mut source = vec![0; 8];
            source[2 * axis] = 1;
            let p = send(
                session,
                &mut stream,
                MathematicalRequest::PredictRelation {
                    relation: 0,
                    source: MathematicalInputWire::Values {
                        values: row(&source),
                    },
                    retain_prediction: true,
                },
            );
            let observed = send(
                session,
                &mut stream,
                MathematicalRequest::ObserveRelation {
                    relation: 0,
                    prediction: p["value"]["prediction"].as_u64().unwrap(),
                    observed: row(&value),
                },
            );
            assert_eq!(observed["event"], "mathematical-return", "{observed}");
        }
        let motion =
            ConstantAccelerationRelease::new(2, BigRational::from_integer(2.into())).unwrap();
        let release = send(
            session,
            &mut stream,
            MathematicalRequest::ConstructLinear {
                coefficients: matrix_wire(&motion.release().unwrap()),
            },
        )["value"]["operator"]
            .as_u64()
            .unwrap();
        let mut futures = Vec::new();
        for t in [BigRational::new(1.into(), 2.into()), BigRational::one()] {
            let flow = send(
                session,
                &mut stream,
                MathematicalRequest::ConstructLinear {
                    coefficients: matrix_wire(&motion.flow(&t).unwrap()),
                },
            )["value"]["operator"]
                .as_u64()
                .unwrap();
            let composed = send(
                session,
                &mut stream,
                MathematicalRequest::Compose {
                    operator: release,
                    following: flow,
                    right: None,
                },
            );
            assert_eq!(composed["event"], "mathematical-return", "{composed}");
            futures.push(composed["value"]["operator"].as_u64().unwrap());
        }
        let joined = send(
            session,
            &mut stream,
            MathematicalRequest::JoinReceivers {
                operators: futures.clone(),
            },
        );
        assert_eq!(joined["event"], "mathematical-return", "{joined}");
        assert_eq!(
            joined["value"]["joint_receiver"]["output_extents"],
            json!([6, 6])
        );
        let operator = joined["value"]["operator"].as_u64().unwrap();
        let predict = |session: &mut NativeMathematicalSession<'_>,
                       stream: &mut HnaStream,
                       operator,
                       retain_prediction| {
            send(
                session,
                stream,
                MathematicalRequest::PredictCondition {
                    relation: 0,
                    operator,
                    retain_prediction,
                },
            )
        };
        let before = predict(session, &mut stream, operator, false);
        assert_eq!(before["event"], "mathematical-return", "{before}");
        assert_eq!(before["value"]["reading"]["coverage"]["kind"], "complete");
        let family = &before["value"]["reading"]["supported_outputs"];
        assert_eq!(family["kind"], "plural", "{family}");
        assert_eq!(family["directions"].as_array().unwrap().len(), 2);
        assert_eq!(before["value"]["reading"]["output_width"], 12);
        let condition_before = session.relations[&0].condition().unwrap().inspect()?;
        // The same two unknown impulse components produce both futures. Their joint
        // predicts this exact cross-time relation even though both positions are plural.
        let mut relation_rows = vec![vec![BigRational::zero(); 12]; 2];
        for i in 0..2 {
            relation_rows[i][i] = BigRational::from_integer((-2).into());
            relation_rows[i][6 + i] = BigRational::one();
        }
        let difference = send(
            session,
            &mut stream,
            MathematicalRequest::ComposeReceiver {
                operator,
                matrix: matrix_wire(&ExactRatMatrix::new(relation_rows).unwrap()),
            },
        )["value"]["operator"]
            .as_u64()
            .unwrap();
        let difference = predict(session, &mut stream, difference, false);
        let difference: Vec<RationalWire> = serde_json::from_value(
            difference["value"]["reading"]["supported_outputs"]["current"].clone(),
        )?;
        assert_eq!(
            vector(&difference)?,
            vec![BigRational::zero(), BigRational::new((-7).into(), 2.into())]
        );
        assert_eq!(
            session.relations[&0].condition().unwrap().inspect()?,
            condition_before
        );

        let mut landing_rows = vec![vec![BigRational::zero(); 12]; 2];
        for i in 0..2 {
            landing_rows[i][6 + i] = BigRational::one();
        }
        let landing_operator = send(
            session,
            &mut stream,
            MathematicalRequest::ComposeReceiver {
                operator,
                matrix: matrix_wire(&ExactRatMatrix::new(landing_rows).unwrap()),
            },
        )["value"]["operator"]
            .as_u64()
            .unwrap();
        let landing = predict(session, &mut stream, landing_operator, true);
        let id = landing["value"]["prediction"].as_u64().unwrap();
        let refined = send(
            session,
            &mut stream,
            MathematicalRequest::ObserveRelation {
                relation: 0,
                prediction: id,
                observed: row(&[4, 1]),
            },
        );
        assert_eq!(refined["event"], "mathematical-return", "{refined}");
        let h: Vec<RationalWire> =
            serde_json::from_value(refined["value"]["condition_family"]["particular"].clone())?;
        assert_eq!(vector(&h)?, vector(&row(&[0, 1, 0, 0, 0, -10, 8, 10]))?);
        let result = predict(session, &mut stream, operator, false);
        assert_eq!(result["event"], "mathematical-return", "{result}");
        assert_eq!(result["value"]["family_graph_compiled"], false);
        let actual: Vec<RationalWire> = serde_json::from_value(
            result["value"]["reading"]["supported_outputs"]["current"].clone(),
        )?;
        let mut expected = row(&[2, 0, 4, 0, 0, -10, 4, 1, 4, -5, 0, -10]);
        expected[1] = RationalWire::from_rational(&BigRational::new(9.into(), 4.into()));
        assert_eq!(vector(&actual)?, vector(&expected)?);
        // A derived linear receiver must not relabel the condition's original bilinear
        // chart. Its inferred impulse still enters that original public relation.
        let original = send(
            session,
            &mut stream,
            MathematicalRequest::PredictRelation {
                relation: 0,
                source: MathematicalInputWire::Values {
                    values: row(&[0, 0, 0, 0, 0, 0, 1, 0]),
                },
                retain_prediction: false,
            },
        );
        assert_eq!(original["event"], "mathematical-return", "{original}");
        let impulse: Vec<RationalWire> = serde_json::from_value(
            original["value"]["reading"]["supported_outputs"]["current"].clone(),
        )?;
        assert_eq!(vector(&impulse)?, vector(&row(&[8, 10]))?);
        Ok(())
    })
    .unwrap();
}

#[test]
#[ignore = "requires CUDA; a wide downstream return retains the original condition chart and empty-source obstruction"]
fn wide_prospective_observation_rejoins_the_original_relation() {
    with_mathematical_session(|session| {
        let mut stream = HnaStream::new();
        send(session, &mut stream, calibrated_sum_products());
        let mut coefficients = vec![vec![BigRational::zero(); 4]; 20];
        for (i, row) in coefficients.iter_mut().enumerate() {
            row[i % 4] = BigRational::one();
        }
        let operator = send(
            session,
            &mut stream,
            MathematicalRequest::ConstructLinear {
                coefficients: matrix_wire(&ExactRatMatrix::new(coefficients).unwrap()),
            },
        )["value"]["operator"]
            .as_u64()
            .unwrap();
        let forecast = send(
            session,
            &mut stream,
            MathematicalRequest::PredictCondition {
                relation: 0,
                operator,
                retain_prediction: true,
            },
        );
        let values = [2, 3, 5, -1].repeat(5);
        let received = send(
            session,
            &mut stream,
            MathematicalRequest::ObserveRelation {
                relation: 0,
                prediction: forecast["value"]["prediction"].as_u64().unwrap(),
                observed: row(&values),
            },
        );
        assert_eq!(received["event"], "mathematical-return", "{received}");
        let original = send(
            session,
            &mut stream,
            MathematicalRequest::PredictRelation {
                relation: 0,
                source: MathematicalInputWire::Values {
                    values: row(&[0, 0, 1, 0]),
                },
                retain_prediction: false,
            },
        );
        assert_eq!(original["event"], "mathematical-return", "{original}");
        let actual: Vec<RationalWire> = serde_json::from_value(
            original["value"]["reading"]["supported_outputs"]["current"].clone(),
        )?;
        assert_eq!(vector(&actual)?, vector(&row(&[5, -1]))?);
        let forecast = send(
            session,
            &mut stream,
            MathematicalRequest::PredictCondition {
                relation: 0,
                operator,
                retain_prediction: true,
            },
        );
        let mut impossible = values;
        impossible[19] = 0;
        let outside = send(
            session,
            &mut stream,
            MathematicalRequest::ObserveRelation {
                relation: 0,
                prediction: forecast["value"]["prediction"].as_u64().unwrap(),
                observed: row(&impossible),
            },
        );
        assert_eq!(
            outside["value"]["condition_family"]["kind"], "outside-represented-relation",
            "{outside}"
        );
        let retained = session.relations[&0].condition().unwrap().inspect()?;
        let empty = send(
            session,
            &mut stream,
            MathematicalRequest::PredictRelation {
                relation: 0,
                source: MathematicalInputWire::Values {
                    values: row(&[0, 0, 1, 0]),
                },
                retain_prediction: false,
            },
        );
        assert_eq!(empty["event"], "mathematical-return", "{empty}");
        assert_eq!(
            empty["value"]["reading"]["coverage"]["kind"],
            "empty-condition-fibre"
        );
        assert_eq!(
            session.relations[&0].condition().unwrap().inspect()?,
            retained
        );
        Ok(())
    })
    .unwrap();
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
#[ignore = "requires CUDA; composed operators consume retained interiors without intermediate host readout"]
fn public_composition_uses_shared_resident_input_ports() {
    with_mathematical_session(|session| {
        let mut stream = HnaStream::new();
        let built = send(session, &mut stream, construct());
        assert_eq!(built["value"]["operator"], 0);
        let reads = session.surface.census().section_read_outs;
        let first = send(
            session,
            &mut stream,
            MathematicalRequest::ApplyInputs {
                operator: 0,
                left: MathematicalInputWire::Values {
                    values: row(&[2, 3]),
                },
                right: Some(MathematicalInputWire::Values {
                    values: row(&[4, 5]),
                }),
                retain_product: true,
                emit_output: false,
            },
        );
        assert_eq!(first["event"], "mathematical-return", "{first}");
        assert_eq!(first["value"]["product"], 0);
        assert_eq!(first["value"]["output"], Value::Null);
        assert_eq!(session.surface.census().section_read_outs, reads);
        let composed = send(
            session,
            &mut stream,
            MathematicalRequest::ApplyInputs {
                operator: 0,
                left: MathematicalInputWire::ProductOutput { product: 0 },
                right: Some(MathematicalInputWire::Values {
                    values: row(&[2, -1]),
                }),
                retain_product: false,
                emit_output: true,
            },
        );
        assert_eq!(composed["event"], "mathematical-return", "{composed}");
        assert_eq!(output(&composed), vector(&row(&[8, 51]))?);
        assert_eq!(session.surface.census().section_read_outs, reads + 1);
        let changed = send(
            session,
            &mut stream,
            MathematicalRequest::BindReceiver {
                operator: 0,
                coefficients: rows(&[&[1, 0, 0, 0], &[0, 1, 1, 0], &[0, 0, 0, 1]]),
            },
        );
        assert_eq!(changed["value"]["operator"], 1);
        let sum = send(
            session,
            &mut stream,
            MathematicalRequest::ConstructLinear {
                coefficients: rows(&[&[1, 1, 1]]),
            },
        );
        assert_eq!(sum["value"]["operator"], 2);
        let reprojected = send(
            session,
            &mut stream,
            MathematicalRequest::ApplyInputs {
                operator: 2,
                left: MathematicalInputWire::ProductReceiver {
                    product: 0,
                    operator: 1,
                },
                right: None,
                retain_product: false,
                emit_output: true,
            },
        );
        assert_eq!(reprojected["event"], "mathematical-return", "{reprojected}");
        assert_eq!(output(&reprojected), vector(&row(&[45]))?);
        assert_eq!(session.surface.census().section_read_outs, reads + 2);
        assert_eq!(reprojected["value"]["intermediate_section_readouts"], 0);
        let wrong_shape = send(
            session,
            &mut stream,
            MathematicalRequest::ApplyInputs {
                operator: 2,
                left: MathematicalInputWire::ProductOutput { product: 0 },
                right: None,
                retain_product: true,
                emit_output: false,
            },
        );
        assert_eq!(wrong_shape["event"], "refused");
        assert_eq!(session.products.len(), 1);
        let wrong_core = send(
            session,
            &mut stream,
            MathematicalRequest::ApplyInputs {
                operator: 2,
                left: MathematicalInputWire::ProductReceiver {
                    product: 0,
                    operator: 2,
                },
                right: None,
                retain_product: true,
                emit_output: false,
            },
        );
        assert_eq!(wrong_core["event"], "refused");
        assert_eq!(session.products.len(), 1);
        send(
            session,
            &mut stream,
            MathematicalRequest::ReleaseProduct { product: 0 },
        );
        assert!(session.products.is_empty());
        Ok(())
    })
    .unwrap();
}

#[test]
#[ignore = "requires CUDA; a repeated fixed section compiles into reusable factors and shares native coefficients"]
fn public_fixed_section_compilation_reuses_the_resident_core() {
    with_mathematical_session(|session| {
        let mut stream = HnaStream::new();
        send(session, &mut stream, construct());
        let first = send(
            session,
            &mut stream,
            MathematicalRequest::ApplyInputs {
                operator: 0,
                left: MathematicalInputWire::Values {
                    values: row(&[2, 3]),
                },
                right: Some(MathematicalInputWire::Values {
                    values: row(&[4, 5]),
                }),
                retain_product: true,
                emit_output: false,
            },
        );
        assert_eq!(first["value"]["product"], 0);
        let serial = send(
            session,
            &mut stream,
            MathematicalRequest::ApplyInputs {
                operator: 0,
                left: MathematicalInputWire::ProductOutput { product: 0 },
                right: Some(MathematicalInputWire::Values {
                    values: row(&[2, -1]),
                }),
                retain_product: false,
                emit_output: true,
            },
        );
        assert_eq!(output(&serial), vector(&row(&[8, 51]))?);
        let difference = |value: &Value, key: &str| {
            value["value"]["cost"]["census_after"][key]
                .as_u64()
                .unwrap()
                - value["value"]["cost"]["census_before"][key]
                    .as_u64()
                    .unwrap()
        };
        let serial_launches =
            difference(&first, "captured_launches") + difference(&serial, "captured_launches");
        let serial_deeds =
            difference(&first, "deed_launches") + difference(&serial, "deed_launches");
        let before = session.surface.census();
        let compiled = send(
            session,
            &mut stream,
            MathematicalRequest::Compose {
                operator: 0,
                following: 0,
                right: Some(row(&[2, -1])),
            },
        );
        assert_eq!(compiled["event"], "mathematical-return", "{compiled}");
        assert_eq!(compiled["value"]["operator"], 1);
        assert_eq!(compiled["value"]["factors"]["products"], 3);
        // Only the new 2x3 receiver and its denominator are uploaded. A/B packets are shared.
        assert_eq!(
            session.surface.census().ingress_octets - before.ingress_octets,
            (2 * 3 + 1) * 2 * std::mem::size_of::<i64>() as u64
        );
        let read = send(
            session,
            &mut stream,
            MathematicalRequest::ReadProduct {
                operator: 1,
                product: 0,
            },
        );
        assert_eq!(output(&read), vector(&row(&[8, 51]))?);
        assert_eq!(read["value"]["source_products_recomputed"], false);
        let before = session.surface.census();
        let fresh = send(
            session,
            &mut stream,
            MathematicalRequest::Apply {
                operator: 1,
                left: row(&[2, 3]),
                right: Some(row(&[4, 5])),
                retain_product: false,
            },
        );
        assert_eq!(output(&fresh), output(&serial));
        assert_eq!(
            2 * (session.surface.census().deed_launches - before.deed_launches),
            serial_deeds
        );
        // Count the complete recorded passage, including its closure kernels, not only four
        // numerical contractions/products. Compilation halves both complete counts here.
        assert_eq!(
            2 * (session.surface.census().captured_launches - before.captured_launches),
            serial_launches
        );
        let new_input = send(
            session,
            &mut stream,
            MathematicalRequest::Apply {
                operator: 1,
                left: row(&[3, 1]),
                right: Some(row(&[1, 2])),
                retain_product: false,
            },
        );
        assert_eq!(output(&new_input), vector(&row(&[9, 13]))?);
        Ok(())
    })
    .unwrap();
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
#[ignore = "requires CUDA; exact reduced power and resident linear construction"]
fn power_reuses_exact_recurrence_and_linear_resident_constructor() {
    with_mathematical_session(|session| {
        let l5 = rows(&[
            &[2, -1, 0, 0, -1],
            &[-1, 2, -1, 0, 0],
            &[0, -1, 2, -1, 0],
            &[0, 0, -1, 2, -1],
            &[-1, 0, 0, -1, 2],
        ]);
        let linear = session.request(&MathematicalRequest::ConstructLinear { coefficients: l5 })?;
        assert_eq!(linear["operator"], 0);
        assert_eq!(linear["derived_rank"], 4);

        let power = session.request(&MathematicalRequest::Power {
            operator: 0,
            exponent: 16,
        })?;
        assert_eq!(power["power_of"], 0);
        assert_eq!(power["exponent"], 16);
        assert_eq!(power["power_scope"]["source_shape"], json!([5, 5]));
        assert!(power["power_construction_work"].is_object());
        assert!(power["source_reconstruction_work"].is_object());
        assert_eq!(power["operator"], 1);
        assert_eq!(power["derived_rank"], 4);

        let applied = session.request(&MathematicalRequest::Apply {
            operator: 1,
            left: row(&[2, -1, 3, 5, -4]),
            right: None,
            retain_product: false,
        })?;
        assert_eq!(
            vector(&serde_json::from_value::<Vec<RationalWire>>(
                applied["output"].clone()
            )?)
            .unwrap(),
            vector(&row(&[
                2_937_109_375,
                -1_633_203_125,
                -294_531_250,
                2_109_765_625,
                -3_119_140_625,
            ]))
            .unwrap()
        );

        let identity = session.request(&MathematicalRequest::Power {
            operator: 0,
            exponent: 0,
        })?;
        assert_eq!(identity["operator"], 2);
        assert_eq!(identity["exponent"], 0);
        let applied_identity = session.request(&MathematicalRequest::Apply {
            operator: 2,
            left: row(&[2, -1, 3, 5, -4]),
            right: None,
            retain_product: false,
        })?;
        assert_eq!(
            vector(&serde_json::from_value::<Vec<RationalWire>>(
                applied_identity["output"].clone()
            )?)
            .unwrap(),
            vector(&row(&[2, -1, 3, 5, -4])).unwrap()
        );

        let bilinear = session.request(&MathematicalRequest::ConstructBilinear {
            target: BilinearTargetWire {
                left_extent: 1,
                right_extent: 1,
                coefficients: rows(&[&[1]]),
            },
            construction: BilinearConstructionWire::Core {
                left_forms: rows(&[&[1]]),
                right_forms: rows(&[&[1]]),
            },
        })?;
        assert_eq!(bilinear["operator"], 3);
        let refused = session.request(&MathematicalRequest::Power {
            operator: 3,
            exponent: 2,
        });
        assert!(refused.is_err());
        assert!(refused
            .unwrap_err()
            .to_string()
            .contains("retained linear operator"));
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

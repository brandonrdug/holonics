//! The cultivated mathematical carrier: a compressed coordinate orbit of rank-one metric
//! reflections on the exact Soddy--Gossett bend quadric.

use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::receiver_history_cultivation::{
    CausalAdjointReceipt, CultivatedReceiverHistoryRest, RankOneMetricMorphology,
};
use relational_geometry::Rat;
use serde::Serialize;

use super::native::NativeTrainingMount;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ProblemSpecification {
    pub exact_formula: String,
    pub indexed_form: String,
    pub nested_fraction_face: String,
    pub carrier: String,
    pub dimensions: Vec<String>,
    pub tensor_indices: Vec<String>,
    pub ambiguous_raster_fibre: Vec<String>,
    pub domain: String,
    pub singularities_and_chart_exclusions: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExactDerivationRoute {
    pub occurrence: String,
    pub steps: Vec<String>,
    pub result: Vec<Rat>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MathematicalReturn {
    pub training_input: Vec<Rat>,
    pub training_output: Vec<Rat>,
    pub training_defect_before: Rat,
    pub training_defect_after: Rat,
    pub held_out_outer_to_inner_word: Vec<usize>,
    pub held_out_conduct_order: Vec<usize>,
    pub held_out_input: Vec<Rat>,
    pub held_out_trace: Vec<Vec<Rat>>,
    pub held_out_output: Vec<Rat>,
    pub held_out_exact_enclosure: Vec<[Rat; 2]>,
    pub held_out_defect_before: Rat,
    pub held_out_defect_after: Rat,
    pub noncommuting_other_order: Vec<Rat>,
    pub ordered_words_separated: bool,
    pub routes: Vec<ExactDerivationRoute>,
    pub invalid_candidate_refusal: String,
}

pub struct CultivationProduct {
    pub problem: ProblemSpecification,
    pub rest: CultivatedReceiverHistoryRest,
    pub rest_bytes: Vec<u8>,
    pub adjoint: CausalAdjointReceipt,
    pub mathematical: MathematicalReturn,
}

pub fn cultivate(native: &NativeTrainingMount) -> Result<CultivationProduct, String> {
    let metric = soddy_metric()?;
    let seed_left = vec![integer(1), integer(0), integer(0), integer(0), integer(0)];
    let seed_right = vec![integer(-2), integer(1), integer(1), integer(1), integer(1)];
    // `out[i] = in[transport[i]]`: this sends the seed support 0 -> 1 and closes after the
    // dimension derived from the metric.
    let coordinate_transport = vec![4, 0, 1, 2, 3];
    let morphology = RankOneMetricMorphology {
        left: seed_left,
        right: seed_right,
        receiver_metric: metric.clone(),
        coordinate_transport: coordinate_transport.clone(),
    };
    let (rest, adjoint) = CultivatedReceiverHistoryRest::seal(
        &native.rest_bytes,
        native.leader.port,
        native.leader.leader_word.clone(),
        morphology,
    )
    .map_err(|error| error.to_string())?;
    if adjoint.return_word != native.leader.return_word
        || adjoint.leader_endpoint != native.leader.leader_endpoint
        || adjoint.orbit_extent != metric.rows()
        || adjoint.measured_delta_ranks.iter().any(|rank| *rank != 1)
    {
        return Err("the cultivated orbit or adjoint left the addressed M3 return".to_owned());
    }
    let rest_bytes = rest.canonical_bytes().map_err(|error| error.to_string())?;
    let mounted = CultivatedReceiverHistoryRest::mount(&rest_bytes, &native.rest_bytes)
        .map_err(|error| error.to_string())?;

    let training_input = integers(&[-1, 2, 2, 3, 3]);
    let training_output = mounted
        .apply_exact(0, &training_input)
        .map_err(|error| error.to_string())?;
    if training_output != integers(&[11, 2, 2, 3, 3]) {
        return Err("the seed reflection left its exact exchanged root".to_owned());
    }
    let held_out_conduct_order = vec![0, 1];
    let held_out_outer_to_inner_word = vec![1, 0];
    let mut held_out_trace = vec![training_input.clone()];
    for member in &held_out_conduct_order {
        let next = mounted
            .apply_exact(*member, held_out_trace.last().expect("trace has root"))
            .map_err(|error| error.to_string())?;
        held_out_trace.push(next);
    }
    let held_out_output = held_out_trace.last().cloned().expect("trace has output");
    if held_out_output != integers(&[11, 17, 2, 3, 3]) {
        return Err("the held-out ordered word disagrees with the exact bend orbit".to_owned());
    }
    let mut other_order = training_input.clone();
    for member in [1, 0] {
        other_order = mounted
            .apply_exact(member, &other_order)
            .map_err(|error| error.to_string())?;
    }
    let ordered_words_separated = other_order != held_out_output;
    if !ordered_words_separated {
        return Err("the sphere-packing control falsely commuted the two reflections".to_owned());
    }

    let invalid_morphology = RankOneMetricMorphology {
        left: vec![integer(1), integer(0), integer(0), integer(0), integer(0)],
        right: vec![integer(-2), integer(1), integer(1), integer(1), integer(0)],
        receiver_metric: metric.clone(),
        coordinate_transport,
    };
    let invalid_candidate_refusal = CultivatedReceiverHistoryRest::seal(
        &native.rest_bytes,
        native.leader.port,
        native.leader.leader_word.clone(),
        invalid_morphology,
    )
    .expect_err("the truncated reflection must refuse")
    .to_string();

    let training_defect_before = form_value(&metric, &training_input)?;
    let training_defect_after = form_value(&metric, &training_output)?;
    let held_out_defect_before = training_defect_before.clone();
    let held_out_defect_after = form_value(&metric, &held_out_output)?;
    if training_defect_before != integer(0)
        || training_defect_after != integer(0)
        || held_out_defect_after != integer(0)
    {
        return Err("the exact reflection orbit left the tangency quadric".to_owned());
    }
    let held_out_exact_enclosure = held_out_output
        .iter()
        .cloned()
        .map(|value| [value.clone(), value])
        .collect();
    let routes = vec![
        ExactDerivationRoute {
            occurrence: "coordinate-root-exchange-route".to_owned(),
            steps: vec![
                "hold four bends and read the other quadratic root".to_owned(),
                "replace b_0 by b_1+b_2+b_3+b_4-b_0".to_owned(),
                "replace b_1 by b_0+b_2+b_3+b_4-b_1 on the returned standing".to_owned(),
            ],
            result: held_out_output.clone(),
        },
        ExactDerivationRoute {
            occurrence: "metric-rank-one-route".to_owned(),
            steps: vec![
                "derive R_i = I + e_i v_i^T as a rank-one morphology".to_owned(),
                "check R_i^T G R_i = G and R_i^2 = I exactly".to_owned(),
                "compose the ordered matrices right-to-left through the retained word".to_owned(),
            ],
            result: held_out_output.clone(),
        },
    ];
    let problem = ProblemSpecification {
        exact_formula: "(sum_{i=0}^{4} b_i)^2 = 3 sum_{i=0}^{4} b_i^2".to_owned(),
        indexed_form: "b_i G^{ij} b_j = 0, with G = J - 3 I".to_owned(),
        nested_fraction_face:
            "b_i = (r_i)^{-1}; therefore ((sum_i (r_i)^{-1})^2)/(sum_i (r_i)^{-2}) = 3".to_owned(),
        carrier: "five oriented integral bends on the Soddy--Gossett quadric".to_owned(),
        dimensions: vec![
            "[r_i] = length".to_owned(),
            "[b_i] = length^{-1}".to_owned(),
            "[b_i G^{ij} b_j] = length^{-2}".to_owned(),
        ],
        tensor_indices: vec![
            "i is the covariant bend slot".to_owned(),
            "j is the paired slot contracted through G^{ij}".to_owned(),
        ],
        ambiguous_raster_fibre: vec![
            "b_1: indexed bend occurrence".to_owned(),
            "b_l: a distinct letter-face admitted by raster testimony until context separates it"
                .to_owned(),
        ],
        domain: "integral bends for the exact orbit; nonzero rational bends for the radius chart"
            .to_owned(),
        singularities_and_chart_exclusions: vec![
            "b_i = 0 is excluded from the reciprocal-radius chart r_i = b_i^{-1}".to_owned(),
            "negative bend is an oriented enclosing sphere, not a negative Euclidean radius"
                .to_owned(),
            "bend incidence alone does not construct centres or prove non-overlap".to_owned(),
        ],
    };
    let mathematical = MathematicalReturn {
        training_input,
        training_output,
        training_defect_before,
        training_defect_after,
        held_out_outer_to_inner_word,
        held_out_conduct_order,
        held_out_input: held_out_trace[0].clone(),
        held_out_trace,
        held_out_output,
        held_out_exact_enclosure,
        held_out_defect_before,
        held_out_defect_after,
        noncommuting_other_order: other_order,
        ordered_words_separated,
        routes,
        invalid_candidate_refusal,
    };
    Ok(CultivationProduct {
        problem,
        rest,
        rest_bytes,
        adjoint,
        mathematical,
    })
}

fn soddy_metric() -> Result<ExactRatMatrix, String> {
    ExactRatMatrix::new(
        (0..5)
            .map(|row| {
                (0..5)
                    .map(|column| integer(if row == column { -2 } else { 1 }))
                    .collect()
            })
            .collect(),
    )
    .map_err(|error| error.to_string())
}

fn form_value(metric: &ExactRatMatrix, vector: &[Rat]) -> Result<Rat, String> {
    let carried = metric.apply(vector).map_err(|error| error.to_string())?;
    Ok(vector
        .iter()
        .zip(carried)
        .fold(integer(0), |sum, (left, right)| sum + left * right))
}

fn integer(value: i64) -> Rat {
    Rat::from_integer(value.into())
}

fn integers(values: &[i64]) -> Vec<Rat> {
    values.iter().copied().map(integer).collect()
}

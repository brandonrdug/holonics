//! L0 apparatus: compose the situated-difference owner over two consecutive admitted K3 sections.
//! The driver only mounts prior artifacts, invokes the public owner, and writes its receipts.

use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
};

use holonic_engine::{
    native_spool::{NativeCollapsedFibre, NativePullbackOccurrence},
    EventId, ExactComplexWaveCurrent, ExactRatMatrix,
};
use life::athena_native::{
    CausalAdjointStepInput, NativeConductedSection, SituatedDifferenceError,
    SituatedDifferenceInput, SituatedDifferenceSection,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::Serialize;

const K3_SECTIONS: &str =
    "output/the_one_connected_athena_native_ecology_returns_dependent_sections_k3/01-conducted-sections.json";
const OUTPUT: &str = "output/the_situated_difference_returns_through_perspective_charts_l0";

#[derive(Serialize)]
struct Grade {
    truth_status: &'static str,
    phase: &'static str,
    predecessor_k3_wire_sha256: &'static str,
    situated_difference_identity_sha256: String,
    candidate_occurrence: EventId,
    returned_occurrence: EventId,
    lawful_rebase_preserved_identity: bool,
    physical_constitutive_intervention_changed_identity: bool,
    chart_defect_control_returned_concrete_sample: bool,
    adjoint_reverse_order: Vec<String>,
    morphology_applied: bool,
    shortest_open_fibre: &'static str,
}

fn main() -> Result<(), String> {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .ok_or("cannot locate repository root")?
        .to_path_buf();
    let sections = read_k3_sections(&repository.join(K3_SECTIONS))?;
    let (candidate, returned) = consecutive_pair(&sections)?;

    let identity_chart = ExactRatMatrix::identity(2).map_err(|error| error.to_string())?;
    let base = SituatedDifferenceSection::found(input(
        candidate.clone(),
        returned.clone(),
        identity_chart.clone(),
        identity_chart.clone(),
        identity_chart.clone(),
    ))
    .map_err(|error| error.to_string())?;

    let nontrivial_chart = matrix(&[&[(2, 1), (0, 1)], &[(0, 1), (3, 1)]])?;
    let rebased = SituatedDifferenceSection::found(input(
        candidate.clone(),
        returned.clone(),
        nontrivial_chart.clone(),
        nontrivial_chart.clone(),
        identity_chart.clone(),
    ))
    .map_err(|error| error.to_string())?;

    let mut intervened_return = returned.clone();
    let intervention = intervened_return
        .emitting_current
        .add(&ExactComplexWaveCurrent::one());
    intervened_return.emitting_current = intervention.clone();
    intervened_return.constitutive_response.stored = intervention;
    let intervened = SituatedDifferenceSection::found(input(
        candidate.clone(),
        intervened_return,
        identity_chart.clone(),
        identity_chart.clone(),
        identity_chart.clone(),
    ))
    .map_err(|error| error.to_string())?;

    let obstruction = SituatedDifferenceSection::found(input(
        candidate.clone(),
        returned.clone(),
        identity_chart.clone(),
        nontrivial_chart,
        identity_chart,
    ))
    .expect_err("the deliberately noncommuting perspective control must refuse");
    let chart_defect_control_returned_concrete_sample = matches!(
        &obstruction,
        SituatedDifferenceError::NoncommutingChart(defect)
            if !defect.is_zero && defect.sample.is_some()
    );

    let output = repository.join(OUTPUT);
    fs::create_dir_all(&output).map_err(|error| error.to_string())?;
    write_json(output.join("01-situated-difference.json"), &base)?;
    write_json(output.join("02-lawful-rebase.json"), &rebased)?;
    write_json(
        output.join("03-constitutive-intervention.json"),
        &intervened,
    )?;
    let chart_obstruction = match &obstruction {
        SituatedDifferenceError::NoncommutingChart(defect) => defect.as_ref(),
        _ => return Err("the perspective control returned the wrong obstruction".to_owned()),
    };
    write_json(
        output.join("04-noncommuting-chart-obstruction.json"),
        chart_obstruction,
    )?;
    let grade = Grade {
        truth_status: "established-bounded; implemented-exact; measured",
        phase: "L0",
        predecessor_k3_wire_sha256:
            "f3388c19a97df45ecb9b62b078045d8a095b28e76e61c9e3146efc463771a13a",
        situated_difference_identity_sha256: base.identity_sha256.clone(),
        candidate_occurrence: candidate.address.occurrence,
        returned_occurrence: returned.address.occurrence,
        lawful_rebase_preserved_identity: base.identity_sha256 == rebased.identity_sha256,
        physical_constitutive_intervention_changed_identity: base.identity_sha256
            != intervened.identity_sha256,
        chart_defect_control_returned_concrete_sample,
        adjoint_reverse_order: base.causal_adjoint.reverse_order.clone(),
        morphology_applied: false,
        shortest_open_fibre:
            "the causal-adjoint return ends at the declared L2 morphology-deposition boundary",
    };
    if !grade.lawful_rebase_preserved_identity
        || !grade.physical_constitutive_intervention_changed_identity
        || !grade.chart_defect_control_returned_concrete_sample
    {
        return Err("one L0 primary consequence failed".to_owned());
    }
    write_json(output.join("00-grade.json"), &grade)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&grade).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn input(
    candidate: NativeConductedSection,
    returned: NativeConductedSection,
    source_chart: ExactRatMatrix,
    target_chart: ExactRatMatrix,
    rebased_transport: ExactRatMatrix,
) -> SituatedDifferenceInput {
    let candidate_coordinates = vec![
        candidate.emitting_current.real.clone(),
        candidate.emitting_current.imaginary.clone(),
    ];
    let returned_coordinates = vec![
        returned.emitting_current.real.clone(),
        returned.emitting_current.imaginary.clone(),
    ];
    let source_transport = ExactRatMatrix::identity(2).expect("declared two-dimensional chart");
    let domain_metric = current_metric(&candidate.entering_current);
    let overlap_metric = pair_metric(&candidate.emitting_current, &returned.entering_current);
    let codomain_metric = current_metric(&returned.emitting_current);
    let candidate_forward = phase_incidence(
        &candidate.relative_phase.cosine,
        &candidate.relative_phase.sine,
        candidate.incidence.coefficient,
    );
    let returned_forward = phase_incidence(
        &returned.relative_phase.cosine,
        &returned.relative_phase.sine,
        returned.incidence.coefficient,
    );
    SituatedDifferenceInput {
        carrying_occurrence: NativePullbackOccurrence {
            left: candidate.address.occurrence,
            right: returned.address.occurrence,
            joining_native: candidate.emitting_native,
        },
        occurrence_fibres: vec![NativeCollapsedFibre {
            native: candidate.emitting_native,
            occurrences: BTreeSet::from([
                candidate.address.occurrence,
                returned.address.occurrence,
            ]),
        }],
        candidate,
        returned,
        source_transport,
        rebased_transport,
        source_chart,
        target_chart,
        candidate_coordinates,
        returned_coordinates: returned_coordinates.clone(),
        adjoint_steps: vec![
            CausalAdjointStepInput {
                name: "candidate-native-phase-incidence".to_owned(),
                forward: candidate_forward,
                domain_metric,
                codomain_metric: overlap_metric.clone(),
            },
            CausalAdjointStepInput {
                name: "returned-native-phase-incidence".to_owned(),
                forward: returned_forward,
                domain_metric: overlap_metric,
                codomain_metric,
            },
        ],
        terminal_covector: returned_coordinates.clone(),
        native_obstructions: Vec::new(),
        open_deposition_boundary: "L2-morphology-deposition-not-yet-applied".to_owned(),
        open_exterior: vec!["future-receiver-and-successor-history-family".to_owned()],
    }
}

fn current_metric(current: &ExactComplexWaveCurrent) -> ExactRatMatrix {
    let one = q(1, 1);
    let real = &one + &current.real * &current.real;
    let imaginary = &one + &current.imaginary * &current.imaginary;
    ExactRatMatrix::new(vec![vec![real, q(0, 1)], vec![q(0, 1), imaginary]])
        .expect("positive diagonal receiver constitution")
}

fn pair_metric(left: &ExactComplexWaveCurrent, right: &ExactComplexWaveCurrent) -> ExactRatMatrix {
    let one = q(1, 1);
    let real = &one + &left.real * &left.real + &right.real * &right.real;
    let imaginary = &one + &left.imaginary * &left.imaginary + &right.imaginary * &right.imaginary;
    ExactRatMatrix::new(vec![vec![real, q(0, 1)], vec![q(0, 1), imaginary]])
        .expect("positive diagonal overlap constitution")
}

fn phase_incidence(cosine: &Rat, sine: &Rat, coefficient: i64) -> ExactRatMatrix {
    let coefficient = q(coefficient, 1);
    ExactRatMatrix::new(vec![
        vec![&coefficient * cosine, -(&coefficient * sine)],
        vec![&coefficient * sine, &coefficient * cosine],
    ])
    .expect("two-dimensional exact phase-incidence transport")
}

fn read_k3_sections(path: &Path) -> Result<Vec<NativeConductedSection>, String> {
    let values: Vec<serde_json::Value> = serde_json::from_slice(
        &fs::read(path).map_err(|error| format!("{}: {error}", path.display()))?,
    )
    .map_err(|error| error.to_string())?;
    values
        .into_iter()
        .map(|value| {
            serde_json::from_value(value.get("section").cloned().ok_or("missing K3 section")?)
                .map_err(|error| error.to_string())
        })
        .collect()
}

fn consecutive_pair(
    sections: &[NativeConductedSection],
) -> Result<(NativeConductedSection, NativeConductedSection), String> {
    for candidate in sections {
        if let Some(returned) = sections.iter().find(|returned| {
            returned.predecessor == Some(candidate.address.occurrence)
                && returned.entering_native == candidate.emitting_native
        }) {
            return Ok((candidate.clone(), returned.clone()));
        }
    }
    Err("K3 has no addressed consecutive section pair".to_owned())
}

fn matrix(rows: &[&[(i64, i64)]]) -> Result<ExactRatMatrix, String> {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| row.iter().map(|&(n, d)| q(n, d)).collect())
            .collect(),
    )
    .map_err(|error| error.to_string())
}

fn q(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn write_json(path: PathBuf, value: &impl Serialize) -> Result<(), String> {
    let bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    fs::write(&path, bytes).map_err(|error| format!("{}: {error}", path.display()))
}

//! A complete finite kernel request: infer independent modes, retain mass/current, reuse and
//! transport the summary, and exhibit a new receiver that cannot factor through it.
use holonic_engine::exact_linear::{
    ExactRatMatrix, KernelModeError, KernelModeReduction, ReceiverFactorization,
};
use num_traits::Zero;
use relational_geometry::Rat;
use serde_json::json;
type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
fn q(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
fn m(rows: &[&[i64]]) -> Result<ExactRatMatrix> {
    Ok(ExactRatMatrix::new(
        rows.iter()
            .map(|row| row.iter().map(|x| q(*x, 1)).collect())
            .collect(),
    )?)
}
fn strings(values: &[Rat]) -> Vec<String> {
    values.iter().map(ToString::to_string).collect()
}
fn main() -> Result<()> {
    let kernel = m(&[
        &[1, 1, 2, 2, 3, 3],
        &[2, 2, 1, 1, 3, 3],
        &[3, 3, 3, 3, 6, 6],
        &[4, 4, 5, 5, 9, 9],
    ])?;
    let values = m(&[&[1, 0], &[3, 1], &[0, 2], &[4, -1], &[2, 3], &[-1, 2]])?;
    let weights = vec![q(1, 1), q(2, 1), q(1, 1), q(1, 1), q(3, 1), q(1, 1)];
    let reduction = KernelModeReduction::new(&kernel)?;
    assert_eq!(reduction.modes(), 2);
    assert_eq!(reduction.decoder().multiply(reduction.encoder())?, kernel);
    let (mut summary, preparation) = reduction.summarize(&weights, &values)?;
    let retained = summary.moments().to_rows();
    let packed = ExactRatMatrix::new(
        weights
            .iter()
            .enumerate()
            .map(|(i, w)| {
                let mut row = vec![w.clone()];
                row.extend(values.row(i).unwrap().iter().map(|x| w * x));
                row
            })
            .collect(),
    )?;
    let (full, mut full_work) = kernel.multiply_with_work(&packed)?;
    let mut reduced_work = holonic_engine::exact_work::ExactWork::nothing();
    let mut outputs = Vec::new();
    for query in 0..kernel.rows() {
        let (face, work) = reduction.read(&summary, query)?;
        let direct: Vec<_> = full.row(query)?[1..]
            .iter()
            .map(|n| {
                let value = n / full.get(query, 0).unwrap();
                full_work.divided(1);
                full_work.wrote(&value);
                value
            })
            .collect();
        assert_eq!(face, direct);
        reduced_work = reduced_work.then(&work);
        outputs.push(strings(&face));
    }
    assert_eq!(outputs[0], vec!["30/19", "37/19"]);
    // Signed value/phase transport acts in the retained modal carrier.
    summary.transport_values(&m(&[&[0, -1], &[1, 0]])?)?;
    assert_eq!(reduction.read(&summary, 0)?.0, vec![q(-37, 19), q(30, 19)]);
    // Repetition of a source action is allowed; its amplitudes are retained.
    let scale = ExactRatMatrix::identity(6)?.scaled(&q(2, 1));
    let scaled = reduction.compile_source_action(&scale)?;
    summary.transport(&scaled)?;
    assert_eq!(reduction.read(&summary, 0)?.0, vec![q(-37, 19), q(30, 19)]);
    let new_receiver = m(&[&[1, 0, 0, 0, 0, 0]])?;
    let ReceiverFactorization::Obstructed {
        source_null,
        returned,
    } = reduction.encoder().factor_receiver(&new_receiver)?
    else {
        return Err("this receiver must distinguish a collapsed source mode".into());
    };
    assert!(
        reduction
            .encoder()
            .apply(&source_null)?
            .iter()
            .all(Zero::is_zero)
    );
    assert!(returned.iter().any(|x| !x.is_zero()));
    let mut separating_action = ExactRatMatrix::identity(6)?.to_rows();
    separating_action[0][0] = q(2, 1);
    let Err(KernelModeError::SeparatedFibre { .. }) =
        reduction.compile_source_action(&ExactRatMatrix::new(separating_action)?)
    else {
        return Err("source action must expose the same separating mode".into());
    };
    // A simple exact telephone/unstable-transport instance of the finite Gronwall law.
    let mut defect = Rat::zero();
    let one_step = q(1, 8);
    for _ in 0..3 {
        defect = q(2, 1) * defect + &one_step;
    }
    assert_eq!(defect, q(7, 8));
    let mean_bad_left = ((q(0, 1) + q(0, 1)) / q(2, 1) + q(4, 1)) / q(2, 1);
    let mean_bad_right = (q(0, 1) + (q(0, 1) + q(4, 1)) / q(2, 1)) / q(2, 1);
    assert_ne!(mean_bad_left, mean_bad_right);
    let report = json!({"schema":"holonics.kernel-mode-compression.v1",
        "scope":"complete supplied finite nonnegative query kernel; real and imaginary currents as paired columns",
        "kernel":kernel.to_rows().iter().map(|r|strings(r)).collect::<Vec<_>>(),
        "derived_modes":reduction.modes(),"source_ports":kernel.columns(),
        "encoder":reduction.encoder().to_rows().iter().map(|r|strings(r)).collect::<Vec<_>>(),
        "decoder":reduction.decoder().to_rows().iter().map(|r|strings(r)).collect::<Vec<_>>(),
        "retained_mass_current":retained.iter().map(|r|strings(r)).collect::<Vec<_>>(),
        "decoded_queries":outputs,"phase_rotated_first_query":["-37/19","30/19"],
        "full_query_work_including_divisions":full_work,"reduced_query_work_including_divisions":reduced_work,
        "source_packing_and_summary_work":preparation,
        "work_scope":"counted exact matrix arithmetic; rank-factorization setup, allocation time and physical/device cost are separate",
        "separating_new_receiver":{"source_null":strings(&source_null),"returned":strings(&returned)},
        "unweighted_mean_bracketing":[mean_bad_left.to_string(),mean_bad_right.to_string()],
        "three_stage_defect":{"gain":"2","per_stage":"1/8","returned":defect.to_string()},
        "native_ecology_changed":false});
    let text = serde_json::to_string_pretty(&report)?;
    if let Some(path) = std::env::args().nth(1) {
        std::fs::write(path, format!("{text}\n"))?;
    }
    println!("{text}");
    Ok(())
}

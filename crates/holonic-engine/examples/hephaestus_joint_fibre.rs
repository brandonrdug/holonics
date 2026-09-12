//! Shared source, condition, junction and material parameters; no independent tensor relaxation.
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    exact_linear::{
        BilinearOperator, BilinearProductCore, ExactRatMatrix, JointBilinearFibre,
        JointBilinearSystem, JointPreimageReduction,
    },
    resident_section::{ResidentBilinearMap, ResidentJointBilinearFibre, ResidentSurface},
};
use relational_geometry::Rat;
use serde_json::json;
use std::sync::Arc;
fn q(v: i64) -> Rat {
    Rat::from_integer(v.into())
}
fn m(rows: &[&[i64]]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|r| r.iter().map(|&v| q(v)).collect())
            .collect(),
    )
    .unwrap()
}
fn strings(v: &[Rat]) -> Vec<String> {
    v.iter().map(ToString::to_string).collect()
}
fn decode<'c>(
    s: &ResidentSurface<'c>,
    section: &holonic_engine::resident_section::ResidentSection<'c>,
) -> Result<Vec<Rat>, Box<dyn std::error::Error>> {
    let words = s.read_out(section)?;
    assert!(words.iter().all(|(a, b)| a == b));
    let den = words.last().unwrap().0;
    assert!(den > 0);
    Ok(words[..words.len() - 1]
        .iter()
        .map(|(v, _)| Rat::new((*v).into(), den.into()))
        .collect())
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let core = Arc::new(BilinearProductCore::new(m(&[&[1]]), m(&[&[1]]))?);
    let action = core
        .bind(&BilinearOperator::new(1, 1, m(&[&[1]]))?)?
        .map_err(|_| "multiplication realization")?;
    let source = Arc::new(JointBilinearFibre::with_affine_return(
        action.clone(),
        m(&[&[1, 0, 0, 0, 0]]),
        m(&[&[0, 1, 0, 0, 0]]),
        m(&[&[0, 0, 1, 0, 0]]),
    )?);
    let material = Arc::new(JointBilinearFibre::new(
        action.clone(),
        m(&[&[0, 0, 0, 1, 0]]),
        m(&[&[0, 0, 1, 0, 0]]),
        vec![q(24)],
    )?);
    let readout = ResidentReadout::new()?;
    let s = ResidentSurface::on(&readout)?;
    let system = Arc::new(JointBilinearSystem::new(vec![
        source.clone(),
        material.clone(),
    ])?);
    let native = ResidentJointBilinearFibre::mount_system(&s, system.clone())?;
    let mut probes = Vec::new();
    for theta in [[2, 3, 6, 4], [2, 3, 8, 3], [3, 2, 6, 4]] {
        let theta = theta.map(q);
        let packet = s.mount_exact_rational_packet(&theta)?;
        let before = s.census().section_read_outs;
        let result = native.evaluate(&packet)?;
        let reads = s.census().section_read_outs - before;
        assert_eq!(reads, 0);
        let result = decode(&s, result.output())?;
        assert_eq!(result, system.evaluate(&theta)?);
        let a = &result[..1];
        let b = &result[1..];
        probes.push(json!({"parameters":strings(&theta),"source_junction_residual":strings(&a),"material_return_residual":strings(&b),"intermediate_readouts":reads}));
    }
    // Actual supplied source/condition/junction cut leaves m as the retained unknown coordinate.
    let parameter_cut = m(&[&[0, 2], &[0, 3], &[0, 6], &[1, 0], &[0, 1]]);
    let source_slice = source.restrict(&parameter_cut)?;
    let material_slice = system.restrict(&parameter_cut)?;
    let JointPreimageReduction::Affine {
        particular,
        directions,
    } = material_slice.affine_preimage()?
    else {
        return Err("affine material slice required".into());
    };
    assert!(directions.is_empty());
    assert!(source_slice.contains(&particular)?);
    let broken = system.restrict(&m(&[&[0, 2], &[0, 3], &[0, 8], &[1, 0], &[0, 1]]))?;
    let JointPreimageReduction::Empty { equation_separator } = broken.affine_preimage()? else {
        return Err("the broken junction must have no compatible material".into());
    };
    let native_action = ResidentBilinearMap::mount(&s, &action)?;
    let coefficient = s.mount_exact_rational_packet(&particular)?;
    let next_source = s.mount_exact_rational_packet(&[q(15)])?;
    let next = native_action.apply(&coefficient, &next_source)?;
    let next = decode(&s, next.output())?;
    assert_eq!(next, vec![q(60)]);
    let out = json!({"schema":"holonics.hephaestus.joint-fibre.v1","parameter_order":["x","h","z","m"],"equations":["x*h=z","m*z=24"],
  "source_constraint_coefficients":source.polynomial().to_rows().iter().map(|r|strings(r)).collect::<Vec<_>>(),
  "material_constraint_coefficients":material.polynomial().to_rows().iter().map(|r|strings(r)).collect::<Vec<_>>(),
  "probes":probes,"affine_material_slice":{"particular":strings(&particular),"null_directions":directions.iter().map(|v|strings(v)).collect::<Vec<_>>()},
  "inconsistent_source_cut":{"equation_separator":strings(&equation_separator)},
  "native_continuation":{"junction":"15","output":strings(&next)},"native_athena_material_deposited":false,
  "scope":"exact joint equation representation, exterior affine solve and resident execution; no coupled-wave material transaction"});
    let text = serde_json::to_string_pretty(&out)?;
    if let Some(path) = std::env::args().nth(1) {
        std::fs::write(path, format!("{text}\n"))?;
    }
    println!("{text}");
    Ok(())
}

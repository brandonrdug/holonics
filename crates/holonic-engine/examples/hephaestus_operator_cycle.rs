//! A caller of reusable mathematical owners: construction, changed receiver, source return,
//! and a separating future. The native material-incorporation binding has its separate scope.
use holonic_engine::exact_linear::{
    BilinearOperator, BilinearSupportSearch, ContextualFactorization, ExactRatMatrix,
    ReceiverFactorization,
};
use num_traits::Zero;
use relational_geometry::Rat;
use serde_json::json;
fn q(n: i64) -> Rat {
    Rat::from_integer(n.into())
}
fn m(rows: &[&[i64]]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|r| r.iter().map(|&x| q(x)).collect())
            .collect(),
    )
    .unwrap()
}
fn values(v: &[Rat]) -> Vec<String> {
    v.iter().map(ToString::to_string).collect()
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let complex = BilinearOperator::new(2, 2, m(&[&[1, 0, 0, -1], &[0, 1, 1, 0]]))?;
    let polynomial =
        BilinearOperator::new(2, 2, m(&[&[1, 0, 0, 0], &[0, 1, 1, 0], &[0, 0, 0, 1]]))?;
    let grammar = m(&[&[1, 0], &[0, 1], &[1, 1], &[1, -1]]);
    let mut examined = 0;
    let mut chosen = None;
    for candidate in BilinearSupportSearch::new(complex.clone(), grammar.clone(), grammar, 1..=3)? {
        examined += 1;
        if let Ok(realized) = candidate?.into_realization() {
            chosen = Some(realized);
            break;
        }
    }
    let first = chosen.ok_or("no realization in declared support aperture")?;
    let second = first
        .core()
        .bind(&polynomial)?
        .map_err(|_| "new receiver is unavailable")?;
    let left = vec![q(2), q(3)];
    let right = vec![q(4), q(5)];
    let source = first.core().apply(&left, &right)?;
    let first_face = first.apply(&left, &right)?;
    let second_face = second.apply(&left, &right)?;
    assert_eq!(first_face, complex.apply(&left, &right)?);
    assert_eq!(second_face, polynomial.apply(&left, &right)?);
    let middle = second.then_receiver(&m(&[&[0, 1, 0]]))?;
    assert_eq!(middle.apply(&left, &right)?, vec![q(22)]);
    let lost = complex
        .coefficients()
        .factor_receiver(polynomial.coefficients())?;
    let ReceiverFactorization::Obstructed {
        source_null,
        returned,
    } = lost
    else {
        return Err("expected separating receiver".into());
    };
    // Restore precisely the carried product contrasts needed by the requested polynomial receiver.
    let lift = complex
        .coefficients()
        .contextual_factorization(first.core().tensor_image(), polynomial.coefficients())?;
    let ContextualFactorization::Lifted(lift) = lift else {
        return Err("retained core must permit the receiver".into());
    };
    let monomials: Vec<_> = left
        .iter()
        .flat_map(|a| right.iter().map(move |b| a * b))
        .collect();
    let lifted = lift.lifted_source.apply(&monomials)?;
    assert_eq!(lift.returned_map.particular.apply(&lifted)?, second_face);
    let inverse = complex
        .left_family_preimage(
            &right,
            &[q(0), q(0)],
            &ExactRatMatrix::identity(2)?,
            &first_face,
        )?
        .ok_or("actual input must remain compatible")?;
    assert_eq!(inverse.0, left);
    assert!(inverse.1.is_empty());
    assert!(
        first
            .tensor_residual(&complex)?
            .entries()
            .iter()
            .all(Zero::is_zero)
    );
    // The productive exact primitive now consumes the same returned factors. Only terminal
    // receivers cross to this exterior caller; source products remain resident for the next use.
    let readout = holonic_engine::embedding_fiber::ResidentReadout::new()?;
    let surface = holonic_engine::resident_section::ResidentSurface::on(&readout)?;
    let native = holonic_engine::resident_section::ResidentBilinearMap::mount(&surface, &first)?;
    let native_second =
        holonic_engine::resident_section::ResidentBilinearMap::mount(&surface, &second)?;
    let x = surface.mount_exact_rational_packet(&left)?;
    let y = surface.mount_exact_rational_packet(&right)?;
    let read_count = surface.census().section_read_outs;
    let native_return = native.apply(&x, &y)?;
    let native_polynomial = native_second.read_product(&native_return)?;
    let intermediate_reads = surface.census().section_read_outs - read_count;
    assert_eq!(intermediate_reads, 0);
    let decode = |section| -> Result<Vec<Rat>, Box<dyn std::error::Error>> {
        let packet = surface.read_out(section)?;
        assert!(packet.iter().all(|(lo, hi)| lo == hi));
        let denominator = packet.last().unwrap().0;
        Ok(packet[..packet.len() - 1]
            .iter()
            .map(|(v, _)| Rat::new((*v).into(), denominator.into()))
            .collect())
    };
    let native_complex = decode(native_return.output())?;
    let native_polynomial = decode(&native_polynomial)?;
    assert_eq!(native_complex, first_face);
    assert_eq!(native_polynomial, second_face);
    let report = json!({"schema":"holonics.hephaestus.operator-cycle.v1","source":{"left":values(&left),"right":values(&right)},
  "construction":{"examined_supports":examined,"products":first.core().products(),"scope":"first available support in declared enumeration, not global optimum"},
  "retained_product_face":values(&source),"complex_receiver":values(&first_face),"polynomial_receiver":values(&second_face),
  "composed_middle_receiver":values(&middle.apply(&left,&right)?),"shared_immutable_core":std::sync::Arc::ptr_eq(first.core(),second.core()),
  "lost_distinction":{"source_null":values(&source_null),"returned":values(&returned)},
  "restored_context_rank":lift.demonstrated_context_rank,"lifted_face":values(&lifted),
  "observed_source_parameter_fibre":{"particular":values(&inverse.0),"null_directions":inverse.1.iter().map(|r|values(r)).collect::<Vec<_>>()},
  "native":{"complex":values(&native_complex),"polynomial":values(&native_polynomial),"intermediate_readouts":intermediate_reads,"retained_product_reused":true},
        "native_material_deposited":false,"scope":"reusable exact engine owners and pure resident execution; developing family incorporation remains unbound"});
    let text = serde_json::to_string_pretty(&report)?;
    if let Some(path) = std::env::args().nth(1) {
        std::fs::write(path, format!("{text}\n"))?;
    }
    println!("{text}");
    Ok(())
}

//! A table of integration methods is not a list of heuristics. It is an atlas
//! of transport mechanisms, and membership is **decidable**.
//!
//! This driver runs `elementary_chart` over a declared family of exponential
//! integrands and reports two things that are usually conflated:
//!
//! 1. **The recognition** — what the signature of the integrand commits to
//!    before any system is built. Read off the object: the degree of the
//!    exponent, the degree of the coefficient, whether the denominator is
//!    squarefree, whether it divides.
//! 2. **The computation** — what the exact rational linear system returned.
//!
//! Grading them separately is the point. A recognition that reported what the
//! solver found would be a check whose material cannot vary the property under
//! test. This one is written down first, and the driver counts how often it was
//! enough on its own.
//!
//! # The claim
//!
//! ```text
//! ∫ R e^g is elementary  ⟺  ∃ rational a with  a' + a·g' = R
//! ```
//!
//! and `deg a = deg R − deg g + 1` is FORCED. One degree, not a search space.
//! So the candidate population is finite and exhaustible, and the answer is a
//! decision. **Non-elementarity comes back as a rank deficiency with an
//! exhibited annihilating combination, never as a search that gave up.**
//!
//! `∫ e^{−x²}` is not hard. It is a linear system whose constant monomial
//! demands `0 = 1`, and this driver prints the row.
//!
//! # The two controls, and why each is here
//!
//! **The exponent alone decides.** `∫ 1·e^x` and `∫ 1·e^{x²}` have the SAME
//! coefficient `R = 1`. The first admits with realizer `1`; the second is
//! refused. Nothing about the numerator separates them — only `g'`, which is
//! the transport. If the reading were about the integrand's size or shape
//! rather than about the transport, these two would not split.
//!
//! **The degree bound is necessary and not sufficient.** `∫(1+x)e^{x²}` and
//! `∫(1+x+x²)e^{x²}` both satisfy it, and both are refused. Without them the
//! recognition would look decisive everywhere, which would mean it was secretly
//! the solver.
//!
//! # What would refute the claim
//!
//! A returned realizer that fails to differentiate back to its declared
//! coefficient; a recognition the system contradicts; a witness that does not
//! annihilate the system it came from; or a family in which the recognition is
//! decisive on every member, which would prove the signature and the solver are
//! not two frames but one.
//!
//! # What this may not be reported as
//!
//! This is not integration. It decides membership in one declared chart and
//! returns the realizer when there is one. `R = P/Q` with `Q` squarefree and
//! `g` a non-constant polynomial is the whole aperture; a repeated denominator
//! factor is refused by name. Risch's algorithm in general is far larger, and
//! nothing here touches logarithmic or algebraic extensions.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_integral_is_decided_by_rank_and_recognised_before_it_runs
//! ```

use holonic_engine::elementary_chart::{
    read_elementary_chart, ElementaryChartError, ElementaryReading, ExponentialIntegrand,
    Recognition, RecognitionOutcome,
};
use holonic_engine::rational_polynomial::RationalPolynomial;
use relational_geometry::exact::rat;

fn polynomial(coefficients: &[i64]) -> RationalPolynomial {
    RationalPolynomial::new(coefficients.iter().map(|value| rat(*value, 1)).collect())
}

struct Declared {
    written: &'static str,
    integrand: ExponentialIntegrand,
}

fn declared_atlas() -> Vec<Declared> {
    let coefficient = |written, numerator: &[i64], exponent: &[i64]| Declared {
        written,
        integrand: ExponentialIntegrand::polynomial_coefficient(
            polynomial(numerator),
            polynomial(exponent),
        ),
    };
    let rational = |written, numerator: &[i64], denominator: &[i64], exponent: &[i64]| Declared {
        written,
        integrand: ExponentialIntegrand::rational_coefficient(
            polynomial(numerator),
            polynomial(denominator),
            polynomial(exponent),
        ),
    };
    vec![
        coefficient("e^x", &[1], &[0, 1]),
        coefficient("x e^x", &[0, 1], &[0, 1]),
        coefficient("x^2 e^x", &[0, 0, 1], &[0, 1]),
        coefficient("e^(x^2)", &[1], &[0, 0, 1]),
        coefficient("e^(-x^2)", &[1], &[0, 0, -1]),
        coefficient("2x e^(x^2)", &[0, 2], &[0, 0, 1]),
        coefficient("x e^(x^2)", &[0, 1], &[0, 0, 1]),
        coefficient("(2x^2 + 1) e^(x^2)", &[1, 0, 2], &[0, 0, 1]),
        coefficient("(1 + x) e^(x^2)", &[1, 1], &[0, 0, 1]),
        coefficient("(1 + x + x^2) e^(x^2)", &[1, 1, 1], &[0, 0, 1]),
        coefficient("e^(x^3)", &[1], &[0, 0, 0, 1]),
        coefficient("3x^2 e^(x^3)", &[0, 0, 3], &[0, 0, 0, 1]),
        rational("e^x / x", &[1], &[0, 1], &[0, 1]),
        rational("e^(x^2) / x", &[1], &[0, 1], &[0, 0, 1]),
        rational("(x^2 - x) e^x / x", &[0, -1, 1], &[0, 1], &[0, 1]),
        rational("e^x / x^2", &[1], &[0, 0, 1], &[0, 1]),
    ]
}

fn main() {
    println!("{}", "=".repeat(96));
    println!("THE INTEGRAL IS DECIDED BY RANK, AND RECOGNISED BEFORE IT RUNS");
    println!("{}", "=".repeat(96));
    println!();
    println!("  a' + a g' = R      is the whole condition.");
    println!("  deg a = deg R - deg g + 1   is FORCED, so the candidate population is finite.");
    println!();

    let atlas = declared_atlas();

    println!("{}", "-".repeat(96));
    println!("THE SIGNATURE, READ OFF THE OBJECT BEFORE ANY SYSTEM IS BUILT");
    println!("{}", "-".repeat(96));
    println!(
        "{:>26} {:>7} {:>7} {:>10} {:>26}",
        "integrand", "deg R", "deg g", "deg a", "recognition"
    );
    let mut signatures = Vec::new();
    for declared in &atlas {
        match declared.integrand.signature() {
            Ok(signature) => {
                let recognition = signature.recognise();
                println!(
                    "{:>26} {:>7} {:>7} {:>10} {:>26}",
                    declared.written,
                    signature
                        .coefficient_degree
                        .map(|degree| degree.to_string())
                        .unwrap_or_else(|| "-".to_owned()),
                    signature.exponent_degree,
                    signature
                        .predicted_realizer_degree
                        .map(|degree| degree.to_string())
                        .unwrap_or_else(|| "-".to_owned()),
                    format!("{recognition:?}")
                );
                signatures.push(Some(recognition));
            }
            Err(error) => {
                println!("{:>26} {:>52}", declared.written, format!("{error}"));
                signatures.push(None);
            }
        }
    }

    println!();
    println!("{}", "-".repeat(96));
    println!("WHAT THE EXACT RATIONAL SYSTEM RETURNED");
    println!("{}", "-".repeat(96));
    println!(
        "{:>26} {:>5} {:>5} {:>7} {:>44}",
        "integrand", "eqns", "rank", "unknown", "reading"
    );

    let mut decisive = 0_u32;
    let mut opened_and_found = 0_u32;
    let mut opened_and_refused = 0_u32;
    let mut contradicted = 0_u32;
    let mut outside_aperture = 0_u32;
    let mut differentiates_back = 0_u32;
    let mut admitted = 0_u32;
    let mut witnesses = Vec::new();

    for declared in &atlas {
        match read_elementary_chart(&declared.integrand) {
            Ok(reading) => {
                let described = match &reading.reading {
                    ElementaryReading::Admits { realizer, .. } => {
                        admitted += 1;
                        if reading.returns_under_differentiation {
                            differentiates_back += 1;
                        }
                        format!("ELEMENTARY   a = {}", realizer.written("x"))
                    }
                    ElementaryReading::PoleObstructed { remainder } => {
                        format!("REFUSED  simple pole, remainder {}", remainder.written("x"))
                    }
                    ElementaryReading::SystemInconsistent { obstruction } => {
                        witnesses.push((declared.written, obstruction.clone()));
                        format!(
                            "REFUSED  rank deficient at monomial x^{}",
                            obstruction.lowest_monomial
                        )
                    }
                };
                match reading.recognition_outcome {
                    RecognitionOutcome::Decisive => decisive += 1,
                    RecognitionOutcome::OpenedAndFound { .. } => opened_and_found += 1,
                    RecognitionOutcome::OpenedAndRefused { .. } => opened_and_refused += 1,
                    RecognitionOutcome::Contradicted => contradicted += 1,
                }
                println!(
                    "{:>26} {:>5} {:>5} {:>7} {:>44}",
                    declared.written,
                    reading.monomial_equations,
                    reading.rank,
                    reading.unknowns,
                    described
                );
            }
            Err(ElementaryChartError::DenominatorNotSquarefree { degree }) => {
                outside_aperture += 1;
                println!(
                    "{:>26} {:>63}",
                    declared.written,
                    format!("OUTSIDE APERTURE  denominator of degree {degree} is not squarefree")
                );
            }
            Err(error) => {
                println!("{:>26} {:>63}", declared.written, format!("{error}"));
            }
        }
    }

    println!();
    println!("{}", "-".repeat(96));
    println!("THE EXHIBITED WITNESSES -- non-elementarity written out, not asserted");
    println!("{}", "-".repeat(96));
    for (written, obstruction) in &witnesses {
        let combination = obstruction
            .combination
            .iter()
            .map(|(monomial, weight)| format!("({weight})*eq[x^{monomial}]"))
            .collect::<Vec<_>>()
            .join(" + ");
        println!("  {written}");
        println!("      {combination}  annihilates every unknown");
        println!(
            "      and returns {} on the right-hand side, which is not zero",
            obstruction.response
        );
    }

    println!();
    println!("{}", "-".repeat(96));
    println!("THE CONTROL -- the same coefficient R = 1, and only the transport differs");
    println!("{}", "-".repeat(96));
    for (written, exponent) in [("e^x", vec![0, 1]), ("e^(x^2)", vec![0, 0, 1])] {
        let integrand =
            ExponentialIntegrand::polynomial_coefficient(polynomial(&[1]), polynomial(&exponent));
        let reading = read_elementary_chart(&integrand).expect("inside the aperture");
        println!(
            "  R = 1,  g' = {:<10}  ->  {}",
            integrand.exponent.derivative().written("x"),
            if reading.reading.is_elementary() {
                "ELEMENTARY"
            } else {
                "REFUSED"
            }
        );
        let _ = written;
    }
    println!();
    println!("  The numerator is identical. Only g' separates them, and g' IS the transport.");

    println!();
    println!("{}", "=".repeat(96));
    println!("WHAT RETURNED");
    println!("{}", "=".repeat(96));
    println!("  declared integrands                      {}", atlas.len());
    println!("  outside the declared aperture            {outside_aperture}");
    println!("  elementary, realizer returned            {admitted}");
    println!("  of those, differentiated back exactly    {differentiates_back}");
    println!("  refusals with an exhibited witness       {}", witnesses.len());
    println!();
    println!("  recognition settled it alone             {decisive}");
    println!("  recognition opened it, system found      {opened_and_found}");
    println!("  recognition opened it, system refused    {opened_and_refused}");
    println!("  recognition contradicted                 {contradicted}");

    println!();
    println!("{}", "-".repeat(96));
    println!("WHAT THIS RUN DOES NOT ESTABLISH");
    println!("{}", "-".repeat(96));
    println!("  This is not integration and not Risch. The aperture is R = P/Q with Q squarefree");
    println!("  and g a non-constant polynomial. No logarithmic or algebraic extension is touched,");
    println!("  and a repeated denominator factor is refused by name rather than answered.");

    let every_admission_returns = differentiates_back == admitted && admitted > 0;
    let recognition_is_sound = contradicted == 0;
    let recognition_is_partial = decisive > 0 && opened_and_refused > 0 && opened_and_found > 0;

    println!();
    println!("{}", "=".repeat(96));
    if every_admission_returns && recognition_is_sound && recognition_is_partial {
        println!(
            "HELD -- every realizer differentiated back, the recognition was never contradicted,"
        );
        println!(
            "        and it is decisive on refusal while genuinely open on admission, so the"
        );
        println!("        signature and the solver are two frames rather than one.");
    } else {
        println!("REFUTED -- differentiates_back={differentiates_back} of {admitted}, contradicted={contradicted}, decisive={decisive}, opened_found={opened_and_found}, opened_refused={opened_and_refused}");
        println!("{}", "=".repeat(96));
        std::process::exit(1);
    }
    println!("{}", "=".repeat(96));
}

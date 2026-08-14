//! The Tschirnhaus organ, driven over a declared quintic family.
//!
//! `canon/TABLET_THE_CHART.md:280` names the owed construction: take a degree-five input, transport
//! it to Bring form by an exact rational chart change, return the transported form **and the
//! transport**, and refuse — with the obstruction named — when the target chart cannot represent the
//! answer.
//!
//! Five declared controls run here and the executable exits non-zero if any fails:
//!
//! 1. the radical chart **refuses** a non-solvable quintic naming the obstruction, and **returns**
//!    for a solvable one — a chart that refuses everything has not been built;
//! 2. every returned transport is verified **by substitution**, exactly, and again by an
//!    independent Sylvester resultant, and the substitution check is shown to be capable of
//!    failing;
//! 3. one declared input whose chart change is rational and one whose is not, the second returning
//!    the auxiliary polynomial with its Sturm certificate;
//! 4. the obstruction population is a **population**, every member carrying what refused it, all
//!    printed;
//! 5. the chart's verdict agrees with `QuinticTransitiveGroup::solvable_by_radicals()` on every
//!    declared input, with at least one input where the fiber is still open.
//!
//! Nothing here consults a clock, and no float, tolerance, threshold or score occurs anywhere on
//! the path.

use std::collections::BTreeSet;
use std::error::Error;

use holonic_engine::arithmetic_monodromy::{
    IntegralQuinticProblem, QuinticIrreducibility, QuinticProblemId,
};
use holonic_engine::quintic_chart::{
    ChartObstructionSpecies, ChartOutcome, QuinticChart, QuinticChartAtlas, RadicalChartVerdict,
    RadicalReturn, read_quintic_charts,
};
use holonic_engine::rational_polynomial::RationalPolynomial;
use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;

/// **What this driver declares as its horn local-section limit.** `prime_ecology` stopped picking a
/// default on 2026-08-09 (`canon/THE_CONTAMINANT_PROTOCOL.md` §2.5 — *a default is a level the
/// organ picked because the caller was never asked*). It bounds how many affine
/// integer-polynomial torsors one horn-resolution event may retain; past it the event refuses by
/// name rather than sampling.
const HORN_LOCAL_SECTION_LIMIT: u64 = 1_000_000;

const PRIME_LIMIT: u64 = 97;

/// One declared input, with the role it plays in the controls.
struct Declared {
    name: &'static str,
    written: &'static str,
    coefficients: &'static [i64],
    role: &'static str,
}

const FAMILY: &[Declared] = &[
    Declared {
        name: "quintic-of-the-wall",
        written: "x^5 - x - 1",
        coefficients: &[-1, -1, 0, 0, 0, 1],
        role: "Galois group S_5: the radical chart must refuse. Already in Bring form.",
    },
    Declared {
        name: "rational-linear-factor",
        written: "(x - 1)(x^4 - 2) = x^5 - x^4 - 2x + 2",
        coefficients: &[2, -2, 0, 0, -1, 1],
        role: "reducible below the wall: the radical chart must return.",
    },
    Declared {
        name: "binomial-behind-a-shift",
        written: "(x + 1)^5 + 2 = x^5 + 5x^4 + 10x^3 + 10x^2 + 5x + 3",
        coefficients: &[3, 5, 10, 10, 5, 1],
        role: "the chart change is what lets the radical chart read it at all.",
    },
    Declared {
        name: "pure-binomial",
        written: "x^5 - 2",
        coefficients: &[-2, 0, 0, 0, 0, 1],
        role: "Galois group F_20, solvable, and its own depressed form.",
    },
    Declared {
        name: "principal-change-is-rational",
        written: "x^5 + 5x^3 + 5x + 1",
        coefficients: &[1, 5, 0, 5, 0, 1],
        role: "the auxiliary quadratic has a rational root: the principal chart returns.",
    },
    Declared {
        name: "principal-change-is-not-rational",
        written: "x^5 + x^3 + 1",
        coefficients: &[1, 0, 0, 1, 0, 1],
        role: "the auxiliary quadratic has no rational root: the principal chart refuses.",
    },
    Declared {
        name: "bring-by-a-cubic-transport",
        written: "x^5 - 2x^3 + x - 1",
        coefficients: &[-1, 1, 0, -2, 0, 1],
        role: "the roots are the SQUARES of the roots of y^5 - y - 1, so the cubic g = x^3 - x \
               carries it back to Bring form over Q. The radical chart still refuses.",
    },
    Declared {
        name: "cyclic-quintic",
        written: "x^5 + x^4 - 4x^3 - 3x^2 + 3x + 1  (minimal polynomial of 2cos(2pi/11))",
        coefficients: &[1, 3, -3, -4, 1, 1],
        role: "square discriminant, cycle types only 1^5 and 5: the fiber stays OPEN.",
    },
    Declared {
        name: "non-monic-input",
        written: "2x^5 + 3x - 6",
        coefficients: &[-6, 3, 0, 0, 0, 2],
        role: "leading coefficient 2: exercises the splitting-field-preserving root scale.",
    },
];

fn main() -> Result<(), Box<dyn Error>> {
    let mut atlases = Vec::new();
    for (index, declared) in FAMILY.iter().enumerate() {
        let problem = IntegralQuinticProblem::new(
            QuinticProblemId(index as u64 + 1),
            declared.name,
            declared
                .coefficients
                .iter()
                .map(|value| BigInt::from(*value))
                .collect(),
        )?;
        atlases.push((
            declared,
            read_quintic_charts(&problem, PRIME_LIMIT, HORN_LOCAL_SECTION_LIMIT)?,
        ));
    }

    println!("THE CHART REFUSES OR RETURNS");
    println!("the Tschirnhaus organ over a declared quintic family");
    println!("prime limit for the Frobenius receiver: {PRIME_LIMIT}");
    println!();

    for (declared, atlas) in &atlases {
        report(declared, atlas);
    }

    println!("================================================================================");
    println!("DECLARED CONTROLS");
    println!("================================================================================");
    println!();

    let mut failures = Vec::new();
    control_radical_both_directions(&atlases, &mut failures);
    control_transports_are_verified(&atlases, &mut failures)?;
    control_rational_and_irrational_chart_change(&atlases, &mut failures);
    control_the_obstruction_population(&atlases, &mut failures);
    control_agreement_with_the_group_fiber(&atlases, &mut failures);
    report_the_boundary(&atlases, &mut failures);

    println!("================================================================================");
    if failures.is_empty() {
        println!("ALL FIVE DECLARED CONTROLS RETURNED, AND THE BOUNDARY REPORT PASSED");
        Ok(())
    } else {
        println!("CONTROLS THAT FAILED: {}", failures.len());
        for failure in &failures {
            println!("  {failure}");
        }
        Err(format!("{} declared control(s) failed", failures.len()).into())
    }
}

fn report(declared: &Declared, atlas: &QuinticChartAtlas) {
    println!("--------------------------------------------------------------------------------");
    println!("{}", declared.name);
    println!("  input        {}", declared.written);
    println!("  role         {}", declared.role);
    println!(
        "  normalised   {}   (root scale {}: y = {} * x)",
        atlas.monic_source.written("x"),
        atlas.root_scale,
        atlas.root_scale
    );
    println!("  degree       {}", atlas.degree);
    println!(
        "  power sums   s_0..s_{} = [{}]",
        atlas.degree,
        atlas.power_sums[..=atlas.degree]
            .iter()
            .map(written_rational)
            .collect::<Vec<_>>()
            .join(", ")
    );
    println!();

    println!("  RADICAL CHART");
    println!(
        "    discriminant            {}{}",
        atlas.radical.discriminant,
        if atlas.radical.discriminant_is_square {
            "   (a square in Q)"
        } else {
            "   (not a square in Q)"
        }
    );
    println!(
        "    irreducibility          {}",
        match &atlas.radical.irreducibility {
            QuinticIrreducibility::Open => "OPEN".to_owned(),
            QuinticIrreducibility::CertifiedByPrime { prime, .. } =>
                format!("certified at prime {prime}"),
        }
    );
    println!(
        "    observed cycle types    {}",
        atlas
            .radical
            .observed_cycle_types
            .iter()
            .map(|(cycle, primes)| format!("{cycle:?}x{}", primes.len()))
            .collect::<Vec<_>>()
            .join(" ")
    );
    println!(
        "    admitted groups         {}",
        written_groups(&atlas.radical.admitted_groups)
    );
    println!(
        "    solvable / non-solvable {} / {}",
        written_groups(&atlas.radical.solvable_admitted),
        written_groups(&atlas.radical.nonsolvable_admitted)
    );
    println!(
        "    rational roots          {}",
        if atlas.radical.rational_roots.is_empty() {
            "none".to_owned()
        } else {
            atlas
                .radical
                .rational_roots
                .iter()
                .map(written_rational)
                .collect::<Vec<_>>()
                .join(", ")
        }
    );
    println!(
        "    residual degree         {}",
        atlas.radical.residual_degree_after_deflation
    );
    println!(
        "    VERDICT                 {}",
        atlas.radical.verdict.label()
    );
    match &atlas.radical.verdict {
        RadicalChartVerdict::Returns(RadicalReturn::BelowTheWall {
            rational_roots,
            residual_degree,
        }) => {
            println!(
                "      below the wall: {} rational root(s) deflate to degree {residual_degree}; \
                 Cardano and Ferrari write the rest",
                rational_roots.len()
            );
        }
        RadicalChartVerdict::Returns(RadicalReturn::DepressedBinomial { written, .. }) => {
            println!("      the depressed form is a binomial; the roots, written:");
            for root in written {
                println!("        {root}");
            }
        }
        RadicalChartVerdict::Refuses(obstruction) => {
            println!("      {}", obstruction.written());
        }
        RadicalChartVerdict::Open {
            solvable,
            nonsolvable,
        } => {
            println!(
                "      the receiver family cannot separate {} from {}: a scalar answer here would \
                 be a lie",
                written_groups(solvable),
                written_groups(nonsolvable)
            );
        }
    }
    println!();

    for (chart, outcome) in atlas.outcomes() {
        println!("  {} CHART", chart.name().to_uppercase());
        match outcome {
            ChartOutcome::Returned(transport) => {
                println!("    RETURNS");
                println!(
                    "    transport    g(x) = {}",
                    transport.transport.written("x")
                );
                println!(
                    "    transported  F(y) = {}",
                    transport.transported.written("y")
                );
                println!(
                    "    killed       {}",
                    transport
                        .killed
                        .iter()
                        .map(|(degree, value)| format!("y^{degree} = {}", written_rational(value)))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                for step in &transport.auxiliary {
                    println!(
                        "    auxiliary    {} solves {} = 0, took {}",
                        step.parameter,
                        step.auxiliary.written(&step.parameter),
                        written_rational(&step.taken)
                    );
                    if let Some(discriminant) = &step.quadratic_discriminant {
                        println!(
                            "                 quadratic discriminant {}",
                            written_rational(discriminant)
                        );
                    }
                }
                println!(
                    "    certificate  substitution residue {} | independent resultant {} | \
                     discriminant {} -> {}",
                    if transport.certificate.substitution_vanishes {
                        "ZERO"
                    } else {
                        "NONZERO"
                    },
                    if transport.certificate.resultant_agrees {
                        "AGREES"
                    } else {
                        "DISAGREES"
                    },
                    written_rational(&transport.certificate.source_discriminant),
                    written_rational(&transport.certificate.transported_discriminant)
                );
                println!(
                    "    work         Newton {} power-sum evaluations | Bareiss {}x{} matrix, {} \
                     exact polynomial divisions, {} multiplications",
                    transport.certificate.newton_work.exact_evaluations,
                    transport.certificate.resultant_work.matrix_extent,
                    transport.certificate.resultant_work.matrix_extent,
                    transport.certificate.resultant_work.exact_divisions,
                    transport
                        .certificate
                        .resultant_work
                        .polynomial_multiplications
                );
            }
            ChartOutcome::Refused(obstruction) => {
                println!("    REFUSES");
                println!("    {}", obstruction.written());
                if let ChartObstructionSpecies::AuxiliaryRootNotRational { census, .. }
                | ChartObstructionSpecies::PartnerNotRational { census, .. } =
                    &obstruction.species
                {
                    println!(
                        "    census       {} distinct real root(s), {} rational, complete",
                        census.distinct_real_roots,
                        census.rational_roots.len()
                    );
                    for (index, root) in census.roots.iter().enumerate() {
                        println!(
                            "      root {index}: isolated in ({}, {}) with Sturm variations {} -> \
                             {}, {}",
                            written_rational(&root.isolating.isolating_interval.lower),
                            written_rational(&root.isolating.isolating_interval.upper),
                            root.isolating.certificate.variations_at_lower,
                            root.isolating.certificate.variations_at_upper,
                            match &root.rational_value {
                                Some(value) => format!("rational = {}", written_rational(value)),
                                None => "NOT rational".to_owned(),
                            }
                        );
                    }
                    println!(
                        "      the census is over the monic companion {}, whose integer roots are \
                         the leading coefficient {} times the rational roots",
                        written_integers(&census.monic_companion.coefficients),
                        census.leading_coefficient
                    );
                    println!(
                        "      work: {} Sturm counts, {} bisection steps, {} exact evaluations",
                        census.work.sturm_counts,
                        census.work.bisection_steps,
                        census.work.exact_evaluations
                    );
                }
            }
        }
        println!();
    }

    println!(
        "  RETAINED OBSTRUCTION POPULATION ({})",
        atlas.obstructions.len()
    );
    for (index, obstruction) in atlas.obstructions.iter().enumerate() {
        println!("    [{index}] {}", obstruction.written());
    }
    println!();
}

fn control_radical_both_directions(
    atlases: &[(&Declared, QuinticChartAtlas)],
    failures: &mut Vec<String>,
) {
    println!("CONTROL 1 — the radical chart refuses AND returns, both on declared inputs");
    let refusing = atlases
        .iter()
        .filter(|(_, atlas)| matches!(atlas.radical.verdict, RadicalChartVerdict::Refuses(_)))
        .collect::<Vec<_>>();
    let returning = atlases
        .iter()
        .filter(|(_, atlas)| matches!(atlas.radical.verdict, RadicalChartVerdict::Returns(_)))
        .collect::<Vec<_>>();
    for (declared, atlas) in &refusing {
        let named = match &atlas.radical.verdict {
            RadicalChartVerdict::Refuses(obstruction) => match &obstruction.species {
                ChartObstructionSpecies::NonSolvableMonodromy { named, .. } => named.clone(),
                _ => String::new(),
            },
            _ => String::new(),
        };
        println!("  REFUSES  {:34} {named}", declared.name);
        if !named.contains("A_5 is simple") {
            failures.push(format!(
                "control 1: {} refused without naming the obstruction",
                declared.name
            ));
        }
    }
    for (declared, atlas) in &returning {
        let how = match &atlas.radical.verdict {
            RadicalChartVerdict::Returns(RadicalReturn::BelowTheWall {
                residual_degree, ..
            }) => format!("below the wall, residual degree {residual_degree}"),
            RadicalChartVerdict::Returns(RadicalReturn::DepressedBinomial {
                degree,
                constant,
                ..
            }) => {
                let mut coefficients = vec![Rat::zero(); *degree + 1];
                coefficients[0] = constant.clone();
                coefficients[*degree] = Rat::one();
                format!(
                    "depressed binomial {}",
                    RationalPolynomial::new(coefficients).written("y")
                )
            }
            _ => String::new(),
        };
        println!("  RETURNS  {:34} {how}", declared.name);
    }
    if refusing.is_empty() {
        failures.push("control 1: no declared input made the radical chart refuse".to_owned());
    }
    if returning.is_empty() {
        failures.push(
            "control 1: the radical chart returned for nothing, so it has not been built"
                .to_owned(),
        );
    }
    println!(
        "  verdict: {} refusal(s), {} return(s), {} open — {}",
        refusing.len(),
        returning.len(),
        atlases
            .iter()
            .filter(|(_, atlas)| matches!(atlas.radical.verdict, RadicalChartVerdict::Open { .. }))
            .count(),
        if refusing.is_empty() || returning.is_empty() {
            "FAILED"
        } else {
            "PASSED"
        }
    );
    println!();
}

fn control_transports_are_verified(
    atlases: &[(&Declared, QuinticChartAtlas)],
    failures: &mut Vec<String>,
) -> Result<(), Box<dyn Error>> {
    println!("CONTROL 2 — every returned transport verified by substitution, exactly");
    let mut checked = 0_usize;
    for (declared, atlas) in atlases {
        for (chart, outcome) in atlas.outcomes() {
            let Some(transport) = outcome.transport() else {
                continue;
            };
            checked += 1;
            // Recompute the substitution here rather than trusting the carried flag: F(g(x))
            // reduced modulo f(x) must be identically zero over Q.
            let composed = transport.transported.composed_with(&transport.transport);
            let (_, residue) = composed.divided_by(&transport.source)?;
            let independent = transport.certificate.resultant_form == transport.transported;
            println!(
                "  {:34} {:10} residue {:4} | resultant {} | Newton {} evals vs Bareiss {} \
                 divisions",
                declared.name,
                chart.name(),
                if residue.is_zero() { "ZERO" } else { "NONZERO" },
                if independent { "AGREES" } else { "DISAGREES" },
                transport.certificate.newton_work.exact_evaluations,
                transport.certificate.resultant_work.exact_divisions
            );
            if !residue.is_zero() {
                failures.push(format!(
                    "control 2: {} / {} does not satisfy F(g(x)) = 0 mod f(x)",
                    declared.name,
                    chart.name()
                ));
            }
            if !independent {
                failures.push(format!(
                    "control 2: {} / {} disagrees with its own Sylvester resultant",
                    declared.name,
                    chart.name()
                ));
            }
        }
    }
    // A check that cannot fail is not a check. Perturb one returned transport and require the
    // residue to become nonzero.
    let mut falsifier_fired = false;
    if let Some(transport) = atlases
        .iter()
        .find_map(|(_, atlas)| atlas.depressed.transport())
    {
        let wrong = transport
            .transport
            .plus(&RationalPolynomial::constant(Rat::one()));
        let composed = transport.transported.composed_with(&wrong);
        let (_, residue) = composed.divided_by(&transport.source)?;
        falsifier_fired = !residue.is_zero();
        println!(
            "  falsifier: perturbing one transport by +1 gives residue {} — the check can fail",
            residue.written("x")
        );
    }
    if !falsifier_fired {
        failures.push("control 2: the substitution check could not be made to fail".to_owned());
    }
    println!(
        "  verdict: {checked} transport(s) verified — {}",
        if failures
            .iter()
            .any(|failure| failure.starts_with("control 2"))
        {
            "FAILED"
        } else {
            "PASSED"
        }
    );
    println!();
    Ok(())
}

fn control_rational_and_irrational_chart_change(
    atlases: &[(&Declared, QuinticChartAtlas)],
    failures: &mut Vec<String>,
) {
    println!("CONTROL 3 — one chart change that IS rational, one that is not");
    let mut rational = Vec::new();
    let mut irrational = Vec::new();
    for (declared, atlas) in atlases {
        for (chart, outcome) in atlas.outcomes() {
            match outcome {
                ChartOutcome::Returned(transport) if !transport.auxiliary.is_empty() => {
                    for step in &transport.auxiliary {
                        rational.push(format!(
                            "{} / {}: {} = {} solves {} = 0",
                            declared.name,
                            chart.name(),
                            step.parameter,
                            written_rational(&step.taken),
                            step.auxiliary.written(&step.parameter)
                        ));
                    }
                }
                ChartOutcome::Refused(obstruction) => {
                    if let ChartObstructionSpecies::AuxiliaryRootNotRational {
                        parameter,
                        auxiliary,
                        census,
                        quadratic_discriminant,
                    } = &obstruction.species
                    {
                        irrational.push(format!(
                            "{} / {}: {parameter} needs a root of {}; {} real root(s), 0 rational{}",
                            declared.name,
                            chart.name(),
                            auxiliary.written(parameter),
                            census.distinct_real_roots,
                            quadratic_discriminant
                                .as_ref()
                                .map(|value| format!(
                                    "; the chart wanted sqrt({})",
                                    written_rational(value)
                                ))
                                .unwrap_or_default()
                        ));
                    }
                }
                ChartOutcome::Returned(_) => {}
            }
        }
    }
    println!("  RATIONAL chart changes taken:");
    for line in &rational {
        println!("    {line}");
    }
    println!("  IRRATIONAL chart changes refused, with the auxiliary and its census:");
    for line in &irrational {
        println!("    {line}");
    }
    if rational.is_empty() {
        failures.push("control 3: no declared input needed a rational auxiliary root".to_owned());
    }
    if irrational.is_empty() {
        failures.push(
            "control 3: every declared input transported rationally, so the fixture family is too \
             narrow"
                .to_owned(),
        );
    }
    println!(
        "  verdict: {} rational, {} irrational — {}",
        rational.len(),
        irrational.len(),
        if rational.is_empty() || irrational.is_empty() {
            "FAILED"
        } else {
            "PASSED"
        }
    );
    println!();
}

fn control_the_obstruction_population(
    atlases: &[(&Declared, QuinticChartAtlas)],
    failures: &mut Vec<String>,
) {
    println!("CONTROL 4 — the obstruction population, whole, every member carrying its evidence");
    let mut total = 0_usize;
    let mut species = BTreeSet::new();
    for (declared, atlas) in atlases {
        if atlas.obstructions.is_empty() {
            continue;
        }
        println!("  {}", declared.name);
        for obstruction in &atlas.obstructions {
            total += 1;
            species.insert(species_name(&obstruction.species));
            println!("    {}", obstruction.written());
            let carries = match &obstruction.species {
                ChartObstructionSpecies::NonSolvableMonodromy { admitted, .. } => {
                    !admitted.is_empty()
                }
                ChartObstructionSpecies::AuxiliaryRootNotRational { auxiliary, .. } => {
                    !auxiliary.is_zero()
                }
                ChartObstructionSpecies::PartnerNotRational {
                    partner_auxiliary, ..
                } => !partner_auxiliary.is_zero(),
                ChartObstructionSpecies::AuxiliaryHasNoRoot { auxiliary, .. } => {
                    !auxiliary.is_zero()
                }
                ChartObstructionSpecies::TransportCollapsesRoots { transport, .. } => {
                    !transport.is_zero()
                }
                ChartObstructionSpecies::EliminationDegenerate { .. }
                | ChartObstructionSpecies::OutsideTransformAperture { .. } => true,
                ChartObstructionSpecies::ChartUndefinedAtDegree {
                    least_source_degree,
                    ..
                } => *least_source_degree > 0,
                ChartObstructionSpecies::EliminantExceedsBezoutBound { cost, .. } => {
                    !cost.condition_degrees.is_empty()
                }
            };
            if !carries {
                failures.push(format!(
                    "control 4: an obstruction from {} carried no evidence",
                    declared.name
                ));
            }
        }
    }
    if total == 0 {
        failures
            .push("control 4: nothing refused, so there is no population to inspect".to_owned());
    }
    println!(
        "  verdict: {total} retained obstruction(s) across {} species [{}] — {}",
        species.len(),
        species.iter().copied().collect::<Vec<_>>().join(", "),
        if total == 0 { "FAILED" } else { "PASSED" }
    );
    println!();
}

fn control_agreement_with_the_group_fiber(
    atlases: &[(&Declared, QuinticChartAtlas)],
    failures: &mut Vec<String>,
) {
    println!("CONTROL 5 — the chart's verdict agrees with solvable_by_radicals() on every input");
    let mut open_exhibited = false;
    for (declared, atlas) in atlases {
        let agrees = atlas.radical.agrees_with_group_fiber();
        let applies = atlas.radical.transitive_receiver_applies();
        println!(
            "  {:34} {:8} fiber {:34} applies {:5} agrees {}",
            declared.name,
            atlas.radical.verdict.label(),
            written_groups(&atlas.radical.admitted_groups),
            applies,
            agrees
        );
        if !agrees {
            failures.push(format!(
                "control 5: {} disagrees with the group fiber",
                declared.name
            ));
        }
        if let RadicalChartVerdict::Open {
            solvable,
            nonsolvable,
        } = &atlas.radical.verdict
            && !solvable.is_empty()
            && !nonsolvable.is_empty()
        {
            open_exhibited = true;
            println!(
                "      OPEN exhibited: {} is solvable, {} is not, and the cycle-type receiver \
                     cannot separate them. The chart returns the population; a scalar answer would \
                     have to pick one and would be wrong either way.",
                written_groups(solvable),
                written_groups(nonsolvable)
            );
        }
    }
    if !open_exhibited {
        failures.push(
            "control 5: no declared input left the fiber open, so the population case is untested"
                .to_owned(),
        );
    }
    println!(
        "  verdict: {}",
        if failures
            .iter()
            .any(|failure| failure.starts_with("control 5"))
        {
            "FAILED"
        } else {
            "PASSED"
        }
    );
    println!();
}

/// What the organ can and cannot transport, measured over the declared family rather than asserted.
///
/// The Bring chart's aperture is *transforms of degree at most three up to projective scale*. A
/// transport of degree at least two returning here is the evidence that the aperture is not vacuous
/// — an organ that only ever returned the identity would have refused everything that mattered and
/// still looked green.
fn report_the_boundary(atlases: &[(&Declared, QuinticChartAtlas)], failures: &mut Vec<String>) {
    println!("THE BOUNDARY — what transported, at what transform degree");
    let mut nontrivial_bring = 0_usize;
    let mut nontrivial_principal = 0_usize;
    for (declared, atlas) in atlases {
        let mut row = Vec::new();
        for (chart, outcome) in atlas.outcomes() {
            let cell = match outcome {
                ChartOutcome::Returned(transport) => {
                    let degree = transport.transport.degree().unwrap_or(0);
                    if degree >= 2 {
                        match chart {
                            QuinticChart::Bring => nontrivial_bring += 1,
                            QuinticChart::Principal => nontrivial_principal += 1,
                            _ => {}
                        }
                    }
                    format!("{} deg {degree}", chart.name())
                }
                ChartOutcome::Refused(_) => format!("{} REFUSED", chart.name()),
            };
            row.push(cell);
        }
        println!("  {:34} {}", declared.name, row.join(" | "));
    }
    println!(
        "  non-identity transports returned: {nontrivial_principal} principal, {nontrivial_bring} \
         Bring"
    );
    if nontrivial_bring == 0 {
        failures.push(
            "boundary: the Bring chart never returned a transform of degree above one, so its \
             aperture is vacuous on this family"
                .to_owned(),
        );
    }
    if nontrivial_principal == 0 {
        failures.push(
            "boundary: the principal chart never returned a transform of degree above one"
                .to_owned(),
        );
    }
    println!(
        "  verdict: {}",
        if nontrivial_bring == 0 || nontrivial_principal == 0 {
            "FAILED"
        } else {
            "PASSED"
        }
    );
    println!();
}

fn species_name(species: &ChartObstructionSpecies) -> &'static str {
    match species {
        ChartObstructionSpecies::NonSolvableMonodromy { .. } => "NonSolvableMonodromy",
        ChartObstructionSpecies::AuxiliaryRootNotRational { .. } => "AuxiliaryRootNotRational",
        ChartObstructionSpecies::PartnerNotRational { .. } => "PartnerNotRational",
        ChartObstructionSpecies::EliminationDegenerate { .. } => "EliminationDegenerate",
        ChartObstructionSpecies::AuxiliaryHasNoRoot { .. } => "AuxiliaryHasNoRoot",
        ChartObstructionSpecies::TransportCollapsesRoots { .. } => "TransportCollapsesRoots",
        ChartObstructionSpecies::OutsideTransformAperture { .. } => "OutsideTransformAperture",
        ChartObstructionSpecies::ChartUndefinedAtDegree { .. } => "ChartUndefinedAtDegree",
        ChartObstructionSpecies::EliminantExceedsBezoutBound { .. } => {
            "EliminantExceedsBezoutBound"
        }
    }
}

fn written_rational(value: &Rat) -> String {
    if value.denom().is_one() {
        format!("{}", value.numer())
    } else {
        format!("{}/{}", value.numer(), value.denom())
    }
}

fn written_integers(values: &[BigInt]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(|value| value.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn written_groups<T: std::fmt::Debug>(groups: &BTreeSet<T>) -> String {
    if groups.is_empty() {
        return "{}".to_owned();
    }
    format!(
        "{{{}}}",
        groups
            .iter()
            .map(|group| format!("{group:?}"))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

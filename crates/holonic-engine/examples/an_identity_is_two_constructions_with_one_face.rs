//! **An identity is two constructions with one face.**
//!
//! ```text
//! cargo run --release --example an_identity_is_two_constructions_with_one_face
//! ```
//!
//! ## The receiver question
//!
//! *Given a configuration with a rational parametrization, a finite receiver family and a degree —
//! and no table of identities anywhere on the path — which identities does the kernel of the face
//! map return, which of them survive exact certification on every chart, and what exactly is still
//! owed before "all degrees" may be said?*
//!
//! ## What is walked
//!
//! **T0** one angle with the curvature `k` a variable: the generator `C² + k S² − 1` and its
//! bounded-degree consequences. **T1** two angles and their sum: the addition laws uniformly in
//! `k`, then the circular, Galilean and hyperbolic collapses computed **separately** and compared
//! against the transported generic ideal. **T2** three helical axes with the Killing form `K`, the
//! reciprocal (Klein) form `R`, pitches, spreads and quadrances: the transferred laws of cosines
//! and sines.
//!
//! ## What this run does not claim
//!
//! The kernel of the sampled evaluation is a **candidate space** and its rank is the **sampled**
//! rank; only the certified basis is a return. The Buchberger closure is a basis of the ideal the
//! certified generators generate, so this run returns **bounded-degree** completeness and prints
//! the remaining all-degree ideal obligation rather than discharging it. The filtered Hilbert
//! dimension counts independent algebraic faces; the certificate size and the wall clock are
//! printed as separate columns because they are separate things.
//!
//! The falsifier is run in the open: the Galilean collapse is walked twice, once with the principal
//! winding alone and once with all four, and the extra relations the first declares are exhibited
//! with the exact counterexample point the second returns.

use holonic_engine::identity_atlas::{
    ADDITION_RECEIVERS, AtlasReturn, COLLAPSED_ADDITION_RECEIVERS, CertifiedIdentity, ChartVerdict,
    ChowScope, Configuration, ExactMultivariate, HELICAL_RECEIVERS, IdentityAtlasError,
    MONOMIAL_CEILING, ONE_ANGLE_RECEIVERS, ReceiverFamily, bounded_degree_completeness, buchberger,
    certify, collapsed_addition, compare_collapse, elementary_generators, helical_triple,
    read_column_matroid, screw_gram_point, two_sided_addition, two_sided_angle, walk,
};
use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;

fn names(source: &[&str]) -> Vec<String> {
    source.iter().map(|name| (*name).to_owned()).collect()
}

fn rational(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn rule(title: &str) {
    println!("\n{}", "=".repeat(96));
    println!("{title}");
    println!("{}", "=".repeat(96));
}

fn report(returned: &AtlasReturn, receiver_names: &[String]) {
    println!("  configuration            {}", returned.configuration());
    println!("  declared family          {}", returned.declaration());
    println!(
        "  |Mon|                    {}   samples {}   resamples {}",
        returned.monomials(),
        returned.samples(),
        returned.resamples()
    );
    println!(
        "  sampled rank             {}   (a lower bound until every basis vector is certified)",
        returned.sampled_rank()
    );
    println!(
        "  filtered dimension       {}   cumulative Hilbert function through the declared degree",
        returned.filtered_dimension()
    );
    println!(
        "  algebraic redundancy     {}   = dim ker E, the identities of the declared family",
        returned.redundancy()
    );
    println!(
        "  certified                {}   refused {}",
        returned.identities().len(),
        returned.refusals().len()
    );
    println!(
        "  certificate size         {} terms, {} coefficient bits   [codec cost, measured separately]",
        returned.certificate_terms(),
        returned.certificate_bits()
    );
    println!(
        "  check cost               {} ms   [wall clock, measured separately]",
        returned.elapsed_millis()
    );
    for (index, identity) in returned.identities().iter().enumerate() {
        println!(
            "    [{index:>2}] {}",
            identity.polynomial().written(receiver_names)
        );
    }
    for refusal in returned.refusals() {
        println!(
            "    REFUSED {}",
            refusal.polynomial().written(receiver_names)
        );
        for verdict in refusal.verdicts() {
            if let ChartVerdict::Refused {
                chart,
                remainder_terms,
                counterexample,
                value,
            } = verdict
            {
                println!(
                    "            chart `{chart}` left a remainder of {remainder_terms} terms; \
                     counterexample {counterexample:?} gives {value:?}"
                );
            }
        }
    }
}

fn closure_report(
    identities: &[CertifiedIdentity],
    receiver_names: &[String],
) -> Result<(), IdentityAtlasError> {
    let elementary = elementary_generators(identities)?;
    println!(
        "  elementary generators    {} new, {} consequences ({} reduction steps) — I4's reduction \
         by increasing degree, in a filtered chart",
        elementary.generators().len(),
        elementary.consequences(),
        elementary.reduction_steps()
    );
    for generator in elementary.generators() {
        println!("    NEW  {}", generator.written(receiver_names));
    }
    let closure = elementary.closure().clone();
    let completeness = bounded_degree_completeness(identities, &closure)?;
    println!(
        "  Groebner closure         {} basis members under {} ({} S-pairs: {} discharged by the \
         product criterion, {} by the chain criterion, {} reduced, {} ms)",
        closure.basis().len(),
        closure.order(),
        closure.reductions().len(),
        closure
            .reductions()
            .iter()
            .filter(|reduction| reduction.coprime)
            .count(),
        closure
            .reductions()
            .iter()
            .filter(|reduction| reduction.chain)
            .count(),
        closure
            .reductions()
            .iter()
            .filter(|reduction| !reduction.chain && !reduction.coprime)
            .count(),
        closure.elapsed_millis()
    );
    for member in closure.basis() {
        println!("    G  {}", member.written(receiver_names));
    }
    println!(
        "  bounded-degree complete  {}   ({} reduction steps)",
        completeness.every_certified_vector_reduces_to_zero(),
        completeness.reduction_steps()
    );
    println!(
        "  STILL OWED               {}",
        completeness.remaining_obligation()
    );
    Ok(())
}

fn matroid_report(
    configuration: &Configuration,
    identities: &[CertifiedIdentity],
) -> Result<(), IdentityAtlasError> {
    let charts = configuration.charts().len();
    let points: Vec<(usize, Vec<Rat>)> = configuration
        .candidate_points(configuration.family().monomials().len() * 2 + 64)
        .into_iter()
        .enumerate()
        .filter_map(|(index, point)| {
            let chart = index % charts;
            configuration.charts()[chart]
                .denominator()
                .evaluate(&point)
                .ok()
                .filter(|value| !value.is_zero())
                .map(|_| (chart, point))
        })
        .take(configuration.family().monomials().len() + 8)
        .collect();
    let reading = read_column_matroid(configuration, &points, identities)?;
    println!(
        "  column matroid           ground {}, loops {:?}, parallel classes {}, simple ground {}",
        reading.ground,
        reading.loops,
        reading.parallel_classes.len(),
        reading.simple_ground
    );
    for (support, circuit) in reading
        .identity_supports
        .iter()
        .zip(&reading.support_is_circuit)
    {
        println!("    identity support {support:?} is a minimal sampled dependency: {circuit}");
    }
    match &reading.chow {
        ChowScope::Admitted {
            ground,
            rank,
            reduced_characteristic,
        } => println!(
            "  identity circuit         U({rank}, {ground}); reduced characteristic magnitudes \
             {reduced_characteristic:?} via matroid_chow"
        ),
        ChowScope::Refused { reason } => println!("  identity circuit REFUSED {reason}"),
    }
    match &reading.full_matroid_scope {
        ChowScope::Admitted { ground, rank, .. } => {
            println!("  whole column matroid     admissible: simple ground {ground}, rank {rank}")
        }
        ChowScope::Refused { reason } => println!("  whole matroid REFUSED    {reason}"),
    }
    Ok(())
}

fn main() -> Result<(), IdentityAtlasError> {
    println!(
        "An identity is two constructions with one face. Nothing below is an authored table: every\n\
         line is a basis vector of the kernel of a declared face map, certified by exact\n\
         substitution on every declared chart."
    );

    // ---------------------------------------------------------------------------------------
    rule("T0 — one angle, the curvature a variable: the generator");
    // ---------------------------------------------------------------------------------------
    let t0_names = names(&ONE_ANGLE_RECEIVERS);
    let t0 = two_sided_angle(2, 1)?;
    println!("  coverage                 {}", t0.coverage());
    for chart in t0.charts() {
        println!("  chart `{}` domain: {}", chart.name(), chart.domain());
    }
    let t0_return = walk(&t0)?;
    report(&t0_return, &t0_names);
    matroid_report(&t0, t0_return.identities())?;

    rule("T0 — the bounded-degree consequences of that one generator");
    let wide = two_sided_angle(4, 2)?;
    let wide_return = walk(&wide)?;
    report(&wide_return, &t0_names);
    println!(
        "\n  Every one of these is a monomial multiple of the single generator. The check is a\n\
         reduction, not a count:"
    );
    let generator_closure = buchberger(&[t0_return.identities()[0].polynomial().clone()])?;
    let consequence_check =
        bounded_degree_completeness(wide_return.identities(), &generator_closure)?;
    println!(
        "  every consequence reduces to zero modulo the generator: {}   ({} steps)",
        consequence_check.every_certified_vector_reduces_to_zero(),
        consequence_check.reduction_steps()
    );

    // ---------------------------------------------------------------------------------------
    rule("T1 — two angles and their sum, uniformly in k: the addition laws");
    // ---------------------------------------------------------------------------------------
    let t1_names = names(&ADDITION_RECEIVERS);
    let t1 = two_sided_addition(2, 1)?;
    println!("  coverage                 {}", t1.coverage());
    println!(
        "  windings charted         {} — (e1, e2) in {{+-1}}^2, with e3 = e1 e2 forced by the \
         group law; -1 = e^{{i pi}} is the half-turn",
        t1.charts().len()
    );
    let t1_return = walk(&t1)?;
    report(&t1_return, &t1_names);
    closure_report(t1_return.identities(), &t1_names)?;
    matroid_report(&t1, t1_return.identities())?;

    // ---------------------------------------------------------------------------------------
    rule("T1 — the three collapses, each kernel computed SEPARATELY");
    // ---------------------------------------------------------------------------------------
    let collapsed_names = names(&COLLAPSED_ADDITION_RECEIVERS);
    let assignment: Vec<Option<Rat>> = vec![None, None, None, None, None, None, None];
    let retained = [0usize, 1, 2, 3, 4, 5];
    let all_windings = [(1, 1), (1, -1), (-1, 1), (-1, -1)];
    for (curvature, label) in [(1i64, "circular"), (0, "Galilean"), (-1, "hyperbolic")] {
        println!("\n  --- k = {curvature} ({label}), all four windings ---");
        let collapsed = collapsed_addition(curvature, &all_windings, 2)?;
        let collapsed_return = walk(&collapsed)?;
        report(&collapsed_return, &collapsed_names);
        let mut moved = assignment.clone();
        moved[6] = Some(rational(curvature));
        let comparison = compare_collapse(
            &format!("k -> {curvature}, all four windings"),
            t1_return.identities(),
            &moved,
            &retained,
            &collapsed_return,
        )?;
        println!(
            "  transported generic ideal has {} generators; specialized kernel lies inside it: {}",
            comparison.transported().len(),
            comparison.specialized_lies_in_transported()
        );
        for relation in comparison.extra_relations() {
            println!(
                "    EXTRA SPECIAL-FIBRE RELATION  {}",
                relation.written(&collapsed_names)
            );
        }
    }

    // ---------------------------------------------------------------------------------------
    rule("The falsifier: the Galilean collapse charted on one winding misses a component");
    // ---------------------------------------------------------------------------------------
    println!(
        "  At k = 0 the fibre of the two-sided circle is C^2 = 1, whose components are C = +1 and\n\
         C = -1. The principal winding covers only the first. A chart family that misses a\n\
         component certifies a non-identity — this is V(xy) charted on y = 0 certifying y."
    );
    let principal = collapsed_addition(0, &[(1, 1)], 2)?;
    let principal_return = walk(&principal)?;
    report(&principal_return, &collapsed_names);
    let mut galilean = assignment.clone();
    galilean[6] = Some(Rat::zero());
    let complete = collapsed_addition(0, &all_windings, 2)?;
    let complete_return = walk(&complete)?;
    let partial = compare_collapse(
        "k -> 0, principal winding alone",
        t1_return.identities(),
        &galilean,
        &retained,
        &principal_return,
    )?;
    println!(
        "\n  one winding gives {} certified identities; four windings give {}.",
        principal_return.identities().len(),
        complete_return.identities().len()
    );
    println!(
        "  relations the one-chart declaration creates beyond the transported ideal: {}",
        partial.extra_relations().len()
    );
    for relation in partial.extra_relations().iter().take(6) {
        println!("    {}", relation.written(&collapsed_names));
    }
    if partial.extra_relations().len() > 6 {
        println!("    … and {} more", partial.extra_relations().len() - 6);
    }

    // C1 - 1 itself: certified on one chart, refused with a point on four.
    let width = COLLAPSED_ADDITION_RECEIVERS.len();
    let mut exponents = vec![0u32; width];
    exponents[0] = 1;
    let candidate =
        ExactMultivariate::term(width, exponents, Rat::from_integer(BigInt::from(1)))?.minus(
            &ExactMultivariate::constant(width, Rat::from_integer(BigInt::from(1))),
        )?;
    let vector_of = |configuration: &Configuration, polynomial: &ExactMultivariate| {
        configuration
            .family()
            .monomials()
            .iter()
            .map(|monomial| {
                polynomial
                    .terms()
                    .get(monomial)
                    .cloned()
                    .unwrap_or_else(Rat::zero)
            })
            .collect::<Vec<_>>()
    };
    let grid = principal.candidate_points(64);
    println!(
        "\n  C1 - 1 on the principal winding alone: {}",
        if certify(&principal, &vector_of(&principal, &candidate), &grid)?.is_ok() {
            "CERTIFIED — and it is not an identity of the fibre"
        } else {
            "refused"
        }
    );
    match certify(&complete, &vector_of(&complete, &candidate), &grid)? {
        Ok(_) => println!("  C1 - 1 on all four windings: certified (this would be a bug)"),
        Err(refused) => {
            for verdict in refused.verdicts() {
                if let ChartVerdict::Refused {
                    chart,
                    counterexample: Some(point),
                    value: Some(value),
                    ..
                } = verdict
                {
                    println!(
                        "  C1 - 1 on all four windings: REFUSED by `{chart}` at (t1, t2) = \
                         ({}, {}) where it takes the value {value}",
                        point[0], point[1]
                    );
                    break;
                }
            }
        }
    }

    // ---------------------------------------------------------------------------------------
    rule("T2 — three helical axes: the transferred laws of cosines and sines");
    // ---------------------------------------------------------------------------------------
    let t2_names = names(&HELICAL_RECEIVERS);
    let t2 = helical_triple(2, 1)?;
    println!("  coverage                 {}", t2.coverage());
    println!(
        "  receivers                {:?}\n                           Qua1 = G11 (quadrance), \
         Pit1 = R11 = 2 h1 Q1 (pitch), SpQ1j = G11 Gjj - G1j^2 (quadrance x spread),\n\
                            Cross = G11 G23 - G12 G13 (the law of cosines' numerator), Gram = det G, \
         each split into its 1-part and its iota-part",
        HELICAL_RECEIVERS
    );
    let t2_return = walk(&t2)?;
    report(&t2_return, &t2_names);
    closure_report(t2_return.identities(), &t2_names)?;

    println!(
        "\n  The same relations on REAL rational screws — three axis directions with rational\n\
         moments, not Gram data invented for the chart:"
    );
    let screw = |u: [i64; 3], v: [i64; 3]| {
        (
            [rational(u[0]), rational(u[1]), rational(u[2])],
            [rational(v[0]), rational(v[1]), rational(v[2])],
        )
    };
    let screws = [
        screw([3, 4, 0], [1, -2, 5]),
        screw([0, 5, 12], [-3, 1, 2]),
        screw([8, -1, 4], [2, 7, -1]),
    ];
    for curvature in [1i64, 0, -1] {
        let point = screw_gram_point(&screws, rational(curvature));
        let receivers = t2.charts()[0].receivers_at(&point)?;
        let mut held = true;
        for identity in t2_return.identities() {
            let mut total = Rat::zero();
            for (monomial, coefficient) in identity.polynomial().terms() {
                let mut term = coefficient.clone();
                for (slot, exponent) in monomial.iter().enumerate() {
                    for _ in 0..*exponent {
                        term *= &receivers[slot];
                    }
                }
                total += term;
            }
            held &= total.is_zero();
        }
        println!(
            "    k = {curvature:>2}: quadrance Q1 = {}, pitch receiver R11 = {}, det-part = {} \
             … every certified identity holds: {held}",
            receivers[0], receivers[1], receivers[8]
        );
    }

    // ---------------------------------------------------------------------------------------
    rule("Where the cost becomes the wall, and who owns the next instance");
    // ---------------------------------------------------------------------------------------
    println!(
        "  Each row is one walk of T1 at a wider head degree: the same configuration, the same\n\
         charts, only the declared monomial family grows. Wall clock is a measured cost and is\n\
         reported beside the algebra, never as it.\n"
    );
    println!("  head degree | |Mon| | samples | redundancy | walk ms");
    for head in 2u32..=3 {
        let ladder = two_sided_addition(head, 1)?;
        let monomials = ladder.family().monomials().len();
        let returned = walk(&ladder)?;
        println!(
            "  {head:>11} | {monomials:>5} | {:>7} | {:>10} | {:>7}",
            returned.samples(),
            returned.redundancy(),
            returned.elapsed_millis()
        );
    }
    match ReceiverFamily::graded_with_tail(&ADDITION_RECEIVERS, 6, 5, 1) {
        Ok(family) => println!(
            "  head degree 5 declares {} monomials, inside the ceiling of {MONOMIAL_CEILING}",
            family.monomials().len()
        ),
        Err(refusal) => println!("  head degree 5 is REFUSED BY TYPE: {refusal}"),
    }
    println!(
        "\n  The wall is the reduced row echelon form of an N x |Mon| exact rational matrix, which\n\
         is cubic in |Mon| with rational coefficient growth on top. It is reached, for this\n\
         receiver family, between head degree 3 and head degree 4 — well inside a single thread.\n\
         The next consumer of a parallel exact linear solve is therefore the T1 family at head\n\
         degree 4 and above, and the T2 family with all six pairwise spreads rather than the two\n\
         at one vertex."
    );

    println!(
        "\n  What the Hilbert function measured above is the number of independent algebraic faces\n\
         of the declared receiver family. It is not encoded bits, not runtime, and not the\n\
         preservation of any continuing conduct; the certificate term counts and the wall clocks\n\
         were printed as separate columns for exactly that reason."
    );
    Ok(())
}

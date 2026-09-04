//! The Tschirnhaus organ, driven up and down the degree ladder.
//!
//! Until 2026-08-09 this organ carried `const QUINTIC_DEGREE: usize = 5` and refused anything else
//! at its first gate. `docs/canon/THE_CONTAMINANT_PROTOCOL.md` §2.6 names that species — **a restriction
//! the organ imposes presented as a fact about the subject** — and says why lifting it is not
//! hygiene:
//!
//! > *"The restriction deletes the mechanism the organ exists to demonstrate.
//! > `solvable_by_radicals` refusing at degree 5 is meaningful only against the degrees where it
//! > does not refuse. An organ that only ever sees degree five cannot state its own theorem."*
//!
//! So this driver is the excision's orbit. The pinned organ **could not accept a non-quintic at
//! all**, which is why the movement is not a changed number but a population that did not exist:
//! twelve declared inputs at degrees two through seven, each read through the whole chart family.
//!
//! Six declared controls run here and the executable exits non-zero if any fails. Each one is
//! stated with the configuration of the declared material that would make it fail, because a check
//! whose material cannot vary the property under test is the same defect as a check that cannot
//! fail — it just wears a passing result (`CLAUDE.md` §8).
//!
//! 1. **the wall is at four and the ladder crosses it.** Every declared input of degree at most
//!    four RETURNS in the radical chart, and at least one of degree at least five REFUSES. Fails if
//!    the organ returns everywhere (the refusal is vacuous) or refuses everywhere (the return is).
//! 2. **the three transport certificates hold at every rung.** `F(g(x)) = 0 mod f(x)` recomputed
//!    here rather than read off the carried flag, the independent Sylvester/Bareiss resultant
//!    agreeing coefficient for coefficient, and the promised coefficients exactly zero. Fails if
//!    any residue at any degree is nonzero.
//! 3. **the chart family has its own floor and names it.** A chart killing `k` coefficients needs
//!    `n >= k + 1`; below that its killed set would reach the constant term. The control requires
//!    each chart to refuse with `ChartUndefinedAtDegree` below its floor **and** to be entered
//!    above it — a two-sided orbit, so a chart that refused everywhere fails it.
//! 4. **the Bezout cost law, computed across `k`.** `2 * 3 * ... * k = k!`, with `k = 3` giving
//!    `6 = 2 * 3`, which is the sentence the organ's own header already contained at one rung. The
//!    control requires the returned figure to equal an independently computed factorial, and every
//!    returned Bring eliminant to sit under the bound.
//! 5. **the two solvability routes agree where both apply.** At degree five the catalogue of the
//!    transitive subgroups of `S_5` and Galois's prime-degree criterion are independent
//!    implementations of one predicate; they must agree on every quintic, and the control exhibits
//!    the **distinguishing word** — the cycle type and witness prime at which the criterion
//!    refuses.
//! 6. **primality of the degree is what decides whether a verdict exists.** Degree seven returns
//!    `NOT-SOLVABLE` with a named witness; degree six returns `NO-CRITERION-AT-THIS-DEGREE` naming
//!    its own factor. Same machine, same material shape, different return, caused by the degree.
//!
//! Nothing here consults a clock, and no float, tolerance, threshold or score occurs anywhere on
//! the path.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;

use holonic_engine::arithmetic_monodromy::{
    IntegralQuinticProblem, QuinticIrreducibility, QuinticProblemId, SolvabilityConstraint,
    affine_group_cycle_types, least_nontrivial_factor,
};
use holonic_engine::quintic_chart::{
    ChartObstructionSpecies, ChartOutcome, QuinticChart, QuinticChartAtlas, RadicalChartVerdict,
    RadicalReturn, read_quintic_charts, tschirnhaus_cost,
};
use num_bigint::{BigInt, BigUint};
use num_traits::One;
use relational_geometry::Rat;

/// **What this driver declares as its horn local-section limit.** `prime_ecology` stopped picking a
/// default on 2026-08-09 (`docs/canon/THE_CONTAMINANT_PROTOCOL.md` §2.5 — *a default is a level the
/// organ picked because the caller was never asked*).
const HORN_LOCAL_SECTION_LIMIT: u64 = 1_000_000;

/// The Frobenius receiver's declared prime limit. A receiver family's aperture is the caller's to
/// declare; what it cannot see is reported as part of the return rather than hidden by it.
const PRIME_LIMIT: u64 = 97;

/// How far the Bezout table is walked. A table's extent is a presentation choice, not a level in an
/// organ: `tschirnhaus_cost` accepts any `k`.
const BEZOUT_TABLE_EXTENT: usize = 8;

struct Declared {
    name: &'static str,
    written: &'static str,
    /// Coefficient-first, lowest degree first. The degree is the length minus one and nothing here
    /// asserts it.
    coefficients: &'static [i64],
    role: &'static str,
}

const LADDER: &[Declared] = &[
    Declared {
        name: "quadratic-root-two",
        written: "x^2 - 2",
        coefficients: &[-2, 0, 1],
        role: "the lowest rung that has a discriminant at all. Principal and Bring are undefined \
               here and must say so.",
    },
    Declared {
        name: "cubic-root-two",
        written: "x^3 - 2",
        coefficients: &[-2, 0, 0, 1],
        role: "already depressed. Bring is undefined at degree three: killing x^2, x^1 and x^0 \
               would kill the constant term.",
    },
    Declared {
        name: "cubic-cyclic",
        written: "x^3 - 3x - 1",
        coefficients: &[-1, -3, 0, 1],
        role: "discriminant 81, a square: the Galois group is C_3 and every cycle type is even.",
    },
    Declared {
        name: "quartic-root-two",
        written: "x^4 - 2",
        coefficients: &[-2, 0, 0, 0, 1],
        role: "ALREADY IN BRING FORM at degree four — y^4 + q is what killing x^3, x^2 and x^1 \
               leaves. The linear transform solves it.",
    },
    Declared {
        name: "quartic-of-the-symmetric-group",
        written: "x^4 + x + 1",
        coefficients: &[1, 1, 0, 0, 1],
        role: "irreducible with Galois group S_4. S_4 IS solvable, so the radical chart RETURNS — \
               this is the contrast that makes the quintic's refusal mean something.",
    },
    Declared {
        name: "quartic-binomial-behind-a-shift",
        written: "(x + 1)^4 + 2 = x^4 + 4x^3 + 6x^2 + 4x + 3",
        coefficients: &[3, 4, 6, 4, 1],
        role: "not a binomial; its depressed transport is. The chart change is what lets the \
               radical chart read it.",
    },
    Declared {
        name: "quintic-of-the-wall",
        written: "x^5 - x - 1",
        coefficients: &[-1, -1, 0, 0, 0, 1],
        role: "Galois group S_5. The first rung at which the radical chart refuses. Already in \
               Bring form.",
    },
    Declared {
        name: "quintic-bring-by-a-cubic-transport",
        written: "x^5 - 2x^3 + x - 1",
        coefficients: &[-1, 1, 0, -2, 0, 1],
        role: "the roots are the SQUARES of the roots of y^5 - y - 1, so g = x^3 - x carries it \
               back to Bring form over Q while the radical chart still refuses.",
    },
    Declared {
        name: "sextic-binomial",
        written: "x^6 - 2",
        coefficients: &[-2, 0, 0, 0, 0, 0, 1],
        role: "composite degree, but a binomial: the radical chart writes the roots without any \
               solvability criterion at all.",
    },
    Declared {
        name: "sextic-composite-degree",
        written: "(x^2 - 2)(x^4 - 2) = x^6 - 2x^4 - 2x^2 + 4",
        coefficients: &[4, 0, -2, 0, -2, 0, 1],
        role: "degree six is composite, so Galois's prime-degree theorem states nothing. The organ \
               must return NO-CRITERION-AT-THIS-DEGREE naming the factor, not a guess.",
    },
    Declared {
        name: "septic-binomial",
        written: "x^7 - 2",
        coefficients: &[-2, 0, 0, 0, 0, 0, 0, 1],
        role: "prime degree seven, Galois group inside AGL(1,7) of order 42: every observed cycle \
               type must be affine-admissible.",
    },
    Declared {
        name: "septic-of-the-fano-plane",
        written: "x^7 - 7x + 3",
        coefficients: &[3, -7, 0, 0, 0, 0, 0, 1],
        role: "prime degree seven, Galois group PSL(2,7) of order 168. Its involutions fix three \
               points, which is a cycle type no affine map over F_7 has: the criterion must \
               REFUTE solvability and name the witness prime.",
    },
];

fn main() -> Result<(), Box<dyn Error>> {
    let mut atlases = Vec::new();
    for (index, declared) in LADDER.iter().enumerate() {
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

    println!("THE DEGREE IS A RUNG");
    println!("the Tschirnhaus organ over degrees two through seven");
    println!("prime limit for the Frobenius receiver: {PRIME_LIMIT}");
    println!(
        "declared inputs: {} across degrees {:?}",
        atlases.len(),
        atlases
            .iter()
            .map(|(_, atlas)| atlas.degree)
            .collect::<BTreeSet<_>>()
    );
    println!();

    for (declared, atlas) in &atlases {
        report(declared, atlas);
    }

    println!("================================================================================");
    println!("DECLARED CONTROLS");
    println!("================================================================================");
    println!();

    let mut failures = Vec::new();
    control_the_wall_is_at_four(&atlases, &mut failures);
    control_certificates_hold_at_every_rung(&atlases, &mut failures)?;
    control_the_chart_family_has_a_floor(&atlases, &mut failures);
    control_the_bezout_cost_law(&atlases, &mut failures);
    control_the_two_routes_agree(&atlases, &mut failures);
    control_primality_of_the_degree_decides(&atlases, &mut failures);

    println!("================================================================================");
    if failures.is_empty() {
        println!("ALL SIX DECLARED CONTROLS RETURNED");
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
    println!("degree {}   {}", atlas.degree, declared.name);
    println!("  input        {}", declared.written);
    println!("  role         {}", declared.role);
    println!(
        "  normalised   {}   (root scale {})",
        atlas.monic_source.written("x"),
        atlas.root_scale
    );
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
            "   (a square in Q: G <= A_n)"
        } else {
            "   (not a square in Q)"
        }
    );
    println!(
        "    irreducibility          {}",
        match &atlas.radical.irreducibility {
            QuinticIrreducibility::Open => "OPEN".to_owned(),
            QuinticIrreducibility::CertifiedByPrime { prime, .. } => format!(
                "certified at prime {prime} by a full {}-cycle",
                atlas.degree
            ),
        }
    );
    println!(
        "    observed cycle types    {}",
        written_cycle_types(&atlas.radical.observed_cycle_types)
    );
    println!(
        "    affine-admissible       {}",
        if least_nontrivial_factor(atlas.degree).is_some() {
            "n/a — composite degree".to_owned()
        } else {
            affine_group_cycle_types(atlas.degree)
                .iter()
                .map(|cycle| format!("{cycle:?}"))
                .collect::<Vec<_>>()
                .join(" ")
        }
    );
    println!(
        "    solvability             {}",
        atlas.radical.solvability.label()
    );
    println!("      {}", atlas.radical.solvability.written());
    println!(
        "    degree-5 catalogue      {}",
        if atlas.radical.catalogue_applies() {
            format!(
                "applies; admitted {} (solvable {} / non-solvable {})",
                written_groups(&atlas.radical.admitted_groups),
                written_groups(&atlas.radical.solvable_admitted),
                written_groups(&atlas.radical.nonsolvable_admitted)
            )
        } else {
            "does not apply at this degree".to_owned()
        }
    );
    println!(
        "    two routes agree        {}",
        match atlas.radical.criterion_agrees_with_catalogue {
            Some(true) => "YES — both applied and returned the same verdict",
            Some(false) => "NO — one of the two implementations is defective",
            None => "n/a — only one route applies here",
        }
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
        "    residual degree         {} (the wall is at 4: S_n is solvable exactly for n <= 4)",
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
        }) => println!(
            "      below the wall: {} rational root(s) deflate to degree {residual_degree}; \
             Cardano and Ferrari write the rest",
            rational_roots.len()
        ),
        RadicalChartVerdict::Returns(RadicalReturn::DepressedBinomial { written, .. }) => {
            println!("      the depressed form is a binomial; the roots, written:");
            for root in written {
                println!("        {root}");
            }
        }
        RadicalChartVerdict::Refuses(obstruction) => println!("      {}", obstruction.written()),
        RadicalChartVerdict::Open { .. } => println!(
            "      the declared receiver family cannot decide this. The population is the return."
        ),
    }
    println!();

    for (chart, outcome) in atlas.outcomes() {
        let killed = chart.killed_degrees(atlas.degree);
        println!(
            "  {} CHART   kills {}   transform degree {}   Bezout {}",
            chart.name().to_uppercase(),
            if killed.is_empty() {
                format!("— (undefined below degree {})", chart.least_source_degree())
            } else {
                format!("{killed:?}")
            },
            chart.killed_count(),
            chart.cost().bezout_number
        );
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
                    if transport.killed.is_empty() {
                        "nothing".to_owned()
                    } else {
                        transport
                            .killed
                            .iter()
                            .map(|(degree, value)| {
                                format!("y^{degree} = {}", written_rational(value))
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    }
                );
                for step in &transport.auxiliary {
                    println!(
                        "    auxiliary    {} solves {} = 0, took {}",
                        step.parameter,
                        step.auxiliary.written(&step.parameter),
                        written_rational(&step.taken)
                    );
                }
                println!(
                    "    certificate  substitution {} | independent resultant {} | discriminant \
                     {} -> {}",
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
                println!("    cost         {}", transport.cost.written());
            }
            ChartOutcome::Refused(obstruction) => {
                println!("    REFUSES");
                println!("    {}", obstruction.written());
            }
        }
        println!();
    }
}

// ---------------------------------------------------------------------------------------------

fn control_the_wall_is_at_four(
    atlases: &[(&Declared, QuinticChartAtlas)],
    failures: &mut Vec<String>,
) {
    println!("CONTROL 1 — the wall is at four, and the ladder crosses it");
    println!(
        "  This is the orbit of the excision. The pinned organ could not accept a non-quintic at"
    );
    println!(
        "  all, so every row below degree five and above it is a return that did not previously"
    );
    println!(
        "  exist. What would make this fail: the organ returning at every degree, or refusing"
    );
    println!("  at every degree — either would mean the verdict carries no information.");
    println!();
    let mut low_returning = 0_usize;
    let mut high_refusing = 0_usize;
    let mut high_returning = 0_usize;
    for (declared, atlas) in atlases {
        let label = atlas.radical.verdict.label();
        println!(
            "  degree {}  {:38} {:8} residual {}",
            atlas.degree, declared.name, label, atlas.radical.residual_degree_after_deflation
        );
        if atlas.degree <= 4 {
            if matches!(atlas.radical.verdict, RadicalChartVerdict::Returns(_)) {
                low_returning += 1;
            } else {
                failures.push(format!(
                    "control 1: {} has degree {} <= 4 and did not return — S_n is solvable there",
                    declared.name, atlas.degree
                ));
            }
        } else {
            match atlas.radical.verdict {
                RadicalChartVerdict::Refuses(_) => high_refusing += 1,
                RadicalChartVerdict::Returns(_) => high_returning += 1,
                RadicalChartVerdict::Open { .. } => {}
            }
        }
    }
    println!();
    println!(
        "  degrees <= 4 returning: {low_returning}    degrees >= 5 refusing: {high_refusing}    \
         degrees >= 5 returning anyway: {high_returning}"
    );
    println!(
        "  The two right-hand columns are both nonzero, so a degree at or above five neither \
         always refuses"
    );
    println!(
        "  nor always returns: it depends on the polynomial, which is exactly what \"not solvable \
         IN THAT CHART\" means."
    );
    if high_refusing == 0 {
        failures.push(
            "control 1: nothing above degree four refused, so the wall is not exhibited".to_owned(),
        );
    }
    if low_returning == 0 {
        failures.push(
            "control 1: nothing at or below degree four returned, so the contrast is not exhibited"
                .to_owned(),
        );
    }
    println!(
        "  verdict: {}",
        if high_refusing == 0 || low_returning == 0 {
            "FAILED"
        } else {
            "PASSED"
        }
    );
    println!();
}

fn control_certificates_hold_at_every_rung(
    atlases: &[(&Declared, QuinticChartAtlas)],
    failures: &mut Vec<String>,
) -> Result<(), Box<dyn Error>> {
    println!("CONTROL 2 — the three transport certificates hold at every rung");
    let mut per_degree: BTreeMap<usize, usize> = BTreeMap::new();
    for (declared, atlas) in atlases {
        for (chart, outcome) in atlas.outcomes() {
            let Some(transport) = outcome.transport() else {
                continue;
            };
            *per_degree.entry(atlas.degree).or_default() += 1;
            // Recomputed here, not read off the carried flag.
            let composed = transport.transported.composed_with(&transport.transport);
            let (_, residue) = composed.divided_by(&transport.source)?;
            let independent = transport.certificate.resultant_form == transport.transported;
            let killed_clean = transport.killed.values().all(|value| {
                use num_traits::Zero;
                value.is_zero()
            });
            println!(
                "  degree {}  {:38} {:10} residue {:8} resultant {:10} killed {}",
                atlas.degree,
                declared.name,
                chart.name(),
                if residue.is_zero() { "ZERO" } else { "NONZERO" },
                if independent { "AGREES" } else { "DISAGREES" },
                if killed_clean { "EXACT" } else { "ALIVE" }
            );
            if !residue.is_zero() {
                failures.push(format!(
                    "control 2: {} / {} at degree {} does not satisfy F(g(x)) = 0 mod f(x)",
                    declared.name,
                    chart.name(),
                    atlas.degree
                ));
            }
            if !independent {
                failures.push(format!(
                    "control 2: {} / {} at degree {} disagrees with its own Sylvester resultant",
                    declared.name,
                    chart.name(),
                    atlas.degree
                ));
            }
            if !killed_clean {
                failures.push(format!(
                    "control 2: {} / {} at degree {} left a promised coefficient alive",
                    declared.name,
                    chart.name(),
                    atlas.degree
                ));
            }
        }
    }
    // A check that cannot fail is not a check: perturb one transport at each degree and require
    // the residue to become nonzero.
    let mut falsified_at = BTreeSet::new();
    for (_, atlas) in atlases {
        if let Some(transport) = atlas.depressed.transport() {
            let wrong = transport.transport.plus(
                &holonic_engine::rational_polynomial::RationalPolynomial::constant(Rat::one()),
            );
            let composed = transport.transported.composed_with(&wrong);
            let (_, residue) = composed.divided_by(&transport.source)?;
            if !residue.is_zero() {
                falsified_at.insert(atlas.degree);
            }
        }
    }
    println!();
    println!(
        "  verified transports per degree: {:?}",
        per_degree.iter().collect::<Vec<_>>()
    );
    println!(
        "  falsifier fired at degrees {:?}: perturbing a returned transform by +1 makes the \
         substitution residue nonzero, so the check can fail at every rung",
        falsified_at
    );
    let degrees = atlases
        .iter()
        .map(|(_, atlas)| atlas.degree)
        .collect::<BTreeSet<_>>();
    if falsified_at != degrees {
        failures.push(format!(
            "control 2: the substitution check could not be made to fail at degrees {:?}",
            degrees.difference(&falsified_at).collect::<Vec<_>>()
        ));
    }
    println!(
        "  verdict: {}",
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

fn control_the_chart_family_has_a_floor(
    atlases: &[(&Declared, QuinticChartAtlas)],
    failures: &mut Vec<String>,
) {
    println!("CONTROL 3 — each chart has a floor derived from what it kills, and names it");
    println!(
        "  A chart killing k coefficients needs n >= k + 1: the killed set is x^(n-1)..x^(n-k) and"
    );
    println!(
        "  reaching x^0 would force a root to the origin. Two-sided: each chart must REFUSE below"
    );
    println!("  its floor with ChartUndefinedAtDegree and be ENTERED above it.");
    println!();
    let mut refused_below: BTreeMap<&str, BTreeSet<usize>> = BTreeMap::new();
    let mut entered_above: BTreeMap<&str, BTreeSet<usize>> = BTreeMap::new();
    for (_, atlas) in atlases {
        for (chart, outcome) in atlas.outcomes() {
            let floor = chart.least_source_degree();
            let undefined = matches!(
                outcome
                    .obstruction()
                    .map(|obstruction| &obstruction.species),
                Some(ChartObstructionSpecies::ChartUndefinedAtDegree { .. })
            );
            if atlas.degree < floor {
                if undefined {
                    refused_below
                        .entry(chart.name())
                        .or_default()
                        .insert(atlas.degree);
                } else {
                    failures.push(format!(
                        "control 3: {} at degree {} is below its floor {floor} but did not refuse \
                         with ChartUndefinedAtDegree",
                        chart.name(),
                        atlas.degree
                    ));
                }
            } else {
                if undefined {
                    failures.push(format!(
                        "control 3: {} at degree {} is at or above its floor {floor} and still \
                         reported itself undefined",
                        chart.name(),
                        atlas.degree
                    ));
                }
                entered_above
                    .entry(chart.name())
                    .or_default()
                    .insert(atlas.degree);
            }
        }
    }
    for chart in QuinticChart::TRANSPORTING {
        println!(
            "  {:10} kills {}   floor {}   refused below at degrees {:?}   entered above at {:?}",
            chart.name(),
            chart.killed_count(),
            chart.least_source_degree(),
            refused_below.get(chart.name()).cloned().unwrap_or_default(),
            entered_above.get(chart.name()).cloned().unwrap_or_default()
        );
    }
    // The orbit must be non-trivial for the charts that have a reachable floor. `depressed` has
    // floor 2, which is the lowest degree this organ admits at all, so nothing can sit below it —
    // that is reported rather than counted as evidence.
    println!();
    println!(
        "  ORBIT: the depressed chart's floor is 2, which is the lowest degree the organ admits, \
         so no"
    );
    println!(
        "  declared material can sit below it. That row is a SNAPSHOT and is not counted as \
         evidence."
    );
    for chart in [QuinticChart::Principal, QuinticChart::Bring] {
        let below = refused_below.get(chart.name()).cloned().unwrap_or_default();
        let above = entered_above.get(chart.name()).cloned().unwrap_or_default();
        if below.is_empty() || above.is_empty() {
            failures.push(format!(
                "control 3: the {} chart's orbit is trivial on this material (below {below:?}, \
                 above {above:?})",
                chart.name()
            ));
        }
    }
    println!(
        "  verdict: {}",
        if failures
            .iter()
            .any(|failure| failure.starts_with("control 3"))
        {
            "FAILED"
        } else {
            "PASSED"
        }
    );
    println!();
}

fn control_the_bezout_cost_law(
    atlases: &[(&Declared, QuinticChartAtlas)],
    failures: &mut Vec<String>,
) {
    println!("CONTROL 4 — the Bezout cost law across k, computed rather than commented");
    println!(
        "  For a Tschirnhaus transform of degree k killing the top k coefficients, p_1 = 0 solves"
    );
    println!(
        "  linearly for c_0 and leaves k-1 homogeneous conditions of degrees 2..k on P^(k-1)."
    );
    println!("  The source degree does not appear: the cost is a property of the transform.");
    println!();
    println!(
        "    k   conditions        P^(k-1)   Bezout = k!   max radical   chart at this k   \
         independent k!"
    );
    let mut independent = BigUint::one();
    for k in 1..=BEZOUT_TABLE_EXTENT {
        let cost = tschirnhaus_cost(k);
        independent *= BigUint::from(k);
        let chart = QuinticChart::TRANSPORTING
            .iter()
            .find(|chart| chart.killed_count() == k)
            .map(|chart| chart.name())
            .unwrap_or("—");
        println!(
            "    {k}   {:16}  P^{:<6}  {:<12}  {:<12}  {:<16}  {independent}",
            if cost.condition_degrees.is_empty() {
                "(none)".to_owned()
            } else {
                cost.condition_degrees
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(" * ")
            },
            cost.parameter_space_dimension,
            cost.bezout_number,
            cost.maximum_radical_degree,
            chart
        );
        if cost.bezout_number != independent {
            failures.push(format!(
                "control 4: the returned Bezout number at k = {k} is {} but k! is {independent}",
                cost.bezout_number
            ));
        }
    }
    println!();
    println!(
        "  k = 3 gives 6 = 2 * 3, which is the organ's own header sentence: the classical Bring"
    );
    println!("  reduction costs a square root AND a cube root, and that factorisation is the why.");
    println!();
    // The bound consumed: every returned Bring transport's eliminant sat under it, and the organ
    // refuses by name if one ever does not.
    let mut bring_returns = 0_usize;
    let mut bound_refusals = 0_usize;
    for (_, atlas) in atlases {
        if atlas.bring.transport().is_some() {
            bring_returns += 1;
        }
        for obstruction in &atlas.obstructions {
            if matches!(
                obstruction.species,
                ChartObstructionSpecies::EliminantExceedsBezoutBound { .. }
            ) {
                bound_refusals += 1;
            }
        }
    }
    println!(
        "  Bring transports returned across the ladder: {bring_returns}; eliminants refused for \
         exceeding the bound: {bound_refusals}"
    );
    println!(
        "  The bound is a live guard in the organ, not an assertion here: an eliminant above {} \
         returns",
        tschirnhaus_cost(QuinticChart::Bring.killed_count()).bezout_number
    );
    println!("  EliminantExceedsBezoutBound carrying the cost that refused it.");
    println!(
        "  verdict: {}",
        if failures
            .iter()
            .any(|failure| failure.starts_with("control 4"))
        {
            "FAILED"
        } else {
            "PASSED"
        }
    );
    println!();
}

fn control_the_two_routes_agree(
    atlases: &[(&Declared, QuinticChartAtlas)],
    failures: &mut Vec<String>,
) {
    println!("CONTROL 5 — the two solvability routes agree exactly where both apply");
    println!(
        "  Route A: the catalogue of the five transitive subgroups of S_5, generated and filtered"
    );
    println!("  by observed cycle types and discriminant parity. Degree five only.");
    println!(
        "  Route B: Galois's theorem on solvable equations of PRIME degree — G <= AGL(1,p), whose"
    );
    println!("  element cycle types are derived from the divisors of p-1. Every prime degree.");
    println!();
    let mut compared = 0_usize;
    let mut agreed = 0_usize;
    for (declared, atlas) in atlases {
        match atlas.radical.criterion_agrees_with_catalogue {
            Some(true) => {
                compared += 1;
                agreed += 1;
                println!(
                    "  degree {}  {:38} BOTH APPLY, AGREE   catalogue {} / criterion {}",
                    atlas.degree,
                    declared.name,
                    written_groups(&atlas.radical.admitted_groups),
                    atlas.radical.solvability.label()
                );
            }
            Some(false) => {
                compared += 1;
                println!(
                    "  degree {}  {:38} BOTH APPLY, DISAGREE",
                    atlas.degree, declared.name
                );
                failures.push(format!(
                    "control 5: {} disagrees between the catalogue and the prime-degree criterion",
                    declared.name
                ));
            }
            None => println!(
                "  degree {}  {:38} only one route applies    criterion {}",
                atlas.degree,
                declared.name,
                atlas.radical.solvability.label()
            ),
        }
    }
    println!();
    println!(
        "  THE DISTINGUISHING WORD — what the criterion refused on, and the prime that saw it:"
    );
    let mut witnessed = 0_usize;
    for (declared, atlas) in atlases {
        if let SolvabilityConstraint::NotSolvable {
            degree,
            witness,
            admissible_cycle_types,
        } = &atlas.radical.solvability
        {
            witnessed += 1;
            println!(
                "    {:38} cycle type {:?} at prime {} — AGL(1,{degree}) admits only {}",
                declared.name,
                witness.cycle_type,
                witness.prime,
                admissible_cycle_types
                    .iter()
                    .map(|cycle| format!("{cycle:?}"))
                    .collect::<Vec<_>>()
                    .join(" ")
            );
        }
    }
    if compared == 0 {
        failures.push(
            "control 5: no declared input had both routes apply, so nothing was cross-checked"
                .to_owned(),
        );
    }
    if witnessed == 0 {
        failures.push(
            "control 5: the criterion refuted nothing, so its refusal branch is untested"
                .to_owned(),
        );
    }
    println!();
    println!(
        "  compared on {compared} input(s), agreed on {agreed}; {witnessed} refusal(s) carry a \
         witness prime"
    );
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

fn control_primality_of_the_degree_decides(
    atlases: &[(&Declared, QuinticChartAtlas)],
    failures: &mut Vec<String>,
) {
    println!("CONTROL 6 — primality of the DEGREE is what decides whether a verdict exists");
    println!(
        "  The same machine on the same shape of material returns a verdict at prime degree and"
    );
    println!(
        "  explicitly refuses to state one at composite degree. That refusal names its own factor."
    );
    println!();
    let mut prime_verdicts = 0_usize;
    let mut composite_refusals = 0_usize;
    for (declared, atlas) in atlases {
        let factor = least_nontrivial_factor(atlas.degree);
        println!(
            "  degree {} {:10} {:38} {}",
            atlas.degree,
            match factor {
                Some(least) => format!("({least} | n)"),
                None => "(prime)".to_owned(),
            },
            declared.name,
            atlas.radical.solvability.label()
        );
        match &atlas.radical.solvability {
            SolvabilityConstraint::NoCriterionAtThisDegree {
                degree,
                least_factor,
            } => {
                composite_refusals += 1;
                if factor != Some(*least_factor) || least_nontrivial_factor(*degree).is_none() {
                    failures.push(format!(
                        "control 6: {} declined a verdict at degree {degree} but the factor it \
                         named does not divide it",
                        declared.name
                    ));
                }
            }
            SolvabilityConstraint::NotSolvable { .. }
            | SolvabilityConstraint::ConsistentWithSolvable { .. } => {
                prime_verdicts += 1;
                if factor.is_some() {
                    failures.push(format!(
                        "control 6: {} returned a prime-degree verdict at composite degree {}",
                        declared.name, atlas.degree
                    ));
                }
            }
            SolvabilityConstraint::IrreducibilityNotCertified { .. } => {}
        }
    }
    println!();
    println!(
        "  prime-degree verdicts: {prime_verdicts}    composite-degree refusals to state one: \
         {composite_refusals}"
    );
    if prime_verdicts == 0 || composite_refusals == 0 {
        failures.push(
            "control 6: the orbit is trivial — the declared material does not carry both a prime \
             and a composite degree that reach the criterion"
                .to_owned(),
        );
    }
    println!(
        "  verdict: {}",
        if failures
            .iter()
            .any(|failure| failure.starts_with("control 6"))
        {
            "FAILED"
        } else {
            "PASSED"
        }
    );
    println!();
}

// ---------------------------------------------------------------------------------------------

fn written_rational(value: &Rat) -> String {
    if value.denom().is_one() {
        format!("{}", value.numer())
    } else {
        format!("{}/{}", value.numer(), value.denom())
    }
}

fn written_cycle_types(types: &BTreeMap<Vec<u32>, BTreeSet<u64>>) -> String {
    if types.is_empty() {
        return "none".to_owned();
    }
    types
        .iter()
        .map(|(cycle, primes)| format!("{cycle:?}x{}", primes.len()))
        .collect::<Vec<_>>()
        .join(" ")
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

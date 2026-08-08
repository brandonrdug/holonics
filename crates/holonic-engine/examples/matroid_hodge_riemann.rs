//! The Chow ring of a matroid, its Hodge–Riemann form, and the split that form returns.
//!
//! Adiprasito, Huh and Katz, *Hodge theory for combinatorial geometries*, Annals of Mathematics
//! **188** (2018). The Chow ring of an arbitrary matroid satisfies Poincaré duality, hard Lefschetz,
//! and the Hodge–Riemann relations — with no ambient variety, over no field. This driver builds the
//! ring exactly over `BigRational`, computes the form, hands the form to
//! `holonic_engine::inertia::inertia`, and prints the split it returns.
//!
//! Every declared control is checked and a failure exits nonzero. The falsifier — a class certified
//! to sit **outside** the ample cone — is required to break Hodge–Riemann somewhere; a suite in
//! which nothing can break is a suite that carries no evidence.

use std::process::ExitCode;

use holonic_engine::inertia::{Inertia, SymmetricForm, inertia};
use holonic_engine::matroid_chow::{
    ChowRing, GROUND_APERTURE, LefschetzReport, Matroid, RANK_APERTURE, SubmodularVerdict,
    chain_monomial_census,
};
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;

fn main() -> ExitCode {
    let mut failures: Vec<String> = Vec::new();

    println!("the Chow ring of a matroid, and the positive form on it");
    println!("Adiprasito, Huh & Katz, Annals of Mathematics 188 (2018)");
    println!();
    println!(
        "aperture, declared and enforced: ground set at most {GROUND_APERTURE}, rank at most \
         {RANK_APERTURE}."
    );
    println!(
        "  the rank table is dense over 2^|E| subsets and the matroid audit is 4^|E| comparisons;"
    );
    println!("  the grade-k row reduction is cubic in the chain-monomial count of that grade.");
    println!();

    report_degenerate_refusals(&mut failures);

    for (matroid, note) in fixtures() {
        report_matroid(matroid, note, &mut failures);
    }

    report_vamos_wall(&mut failures);

    println!();
    println!("================================================================================");
    if failures.is_empty() {
        println!("every declared control returned as stated.");
        ExitCode::SUCCESS
    } else {
        println!("{} declared control(s) failed:", failures.len());
        for failure in &failures {
            println!("  - {failure}");
        }
        ExitCode::FAILURE
    }
}

// -------------------------------------------------------------------------------------------

fn fixtures() -> Vec<(Matroid, &'static str)> {
    vec![
        (
            Matroid::uniform(2, 3).expect("U(2,3)"),
            "three points on a line; the smallest ring with a top grade at all",
        ),
        (
            Matroid::uniform(3, 3).expect("U(3,3)"),
            "the Boolean matroid B3: three general lines in P^2. Its wonderful model is Bl_3 P^2, \
             the degree-six del Pezzo surface, Picard rank 4",
        ),
        (
            Matroid::uniform(3, 4).expect("U(3,4)"),
            "four general lines in P^2; wonderful model Bl_6 P^2",
        ),
        (
            Matroid::graphic("M(K4)", 4, &[(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)])
                .expect("M(K4)"),
            "the graphic matroid of K_4: six lines in P^2 with four triple points and three double \
             points; wonderful model Bl_7 P^2, Picard rank 8",
        ),
        (
            Matroid::rank_three_from_lines(
                "Fano F7",
                7,
                &[
                    &[0, 1, 2],
                    &[0, 3, 4],
                    &[0, 5, 6],
                    &[1, 3, 5],
                    &[1, 4, 6],
                    &[2, 3, 6],
                    &[2, 4, 5],
                ],
            )
            .expect("F7"),
            "the Fano plane: representable ONLY in characteristic two, so there is no complex \
             surface to compare against",
        ),
        (
            Matroid::rank_three_from_lines(
                "non-Pappus",
                9,
                &[
                    &[0, 1, 2],
                    &[3, 4, 5],
                    &[0, 4, 8],
                    &[0, 5, 7],
                    &[1, 3, 8],
                    &[1, 5, 6],
                    &[2, 3, 7],
                    &[2, 4, 6],
                ],
            )
            .expect("non-Pappus"),
            "representable over NO field: Pappus's theorem holds in every Desarguesian plane, and \
             this configuration denies it. This is the case that makes the point",
        ),
        (
            Matroid::uniform(4, 4).expect("U(4,4)"),
            "the Boolean matroid B4: the permutohedral fan, whose Betti numbers are the Eulerian \
             numbers 1, 11, 11, 1. Rank four, so the Lefschetz power in the degree-one form is a \
             genuine ω and not the identity",
        ),
    ]
}

fn report_matroid(matroid: Matroid, note: &str, failures: &mut Vec<String>) {
    println!();
    println!("================================================================================");
    println!(
        "{}   |E| = {}, rank {}, top grade r = {}",
        matroid.name(),
        matroid.ground(),
        matroid.rank(),
        matroid.rank() - 1
    );
    println!("  {note}.");

    let name = matroid.name().to_owned();
    let ground = matroid.ground();
    let moebius_magnitudes = match matroid.reduced_characteristic_magnitudes() {
        Ok(values) => values,
        Err(error) => {
            failures.push(format!("{name}: {error}"));
            return;
        }
    };
    let characteristic = matroid.characteristic_polynomial();

    let ring = match ChowRing::new(matroid) {
        Ok(ring) => ring,
        Err(error) => {
            failures.push(format!("{name}: the ring refused to build — {error}"));
            return;
        }
    };
    let top = ring.top();

    // ---- the flats ----
    println!();
    println!("  the proper nonempty flats — one ring generator, one Bergman ray, each:");
    for rank in 1..=top {
        let level: Vec<String> = ring
            .flats()
            .iter()
            .filter(|flat| ring.matroid().rank_of(**flat) == rank)
            .map(|flat| render_subset(*flat, ground))
            .collect();
        println!("    rank {rank} ({:2}): {}", level.len(), level.join(" "));
    }
    println!("    total: {}", ring.flats().len());

    // ---- the grades ----
    println!();
    println!("  the graded ring, monomial basis per grade:");
    for degree in 0..=top {
        let integral = ring.monomial_basis_is_integral(degree);
        if !integral {
            failures.push(format!(
                "{name}: grade {degree} reduces over Q but not over Z, so its monomials are not a \
                 Z-basis"
            ));
        }
        println!(
            "    A^{degree}  dim {:3}   {} chain monomials, {} relation rows   Z-basis: {}",
            ring.dimension(degree),
            ring.chain_monomial_count(degree),
            ring.relation_row_count(degree),
            if integral { "certified" } else { "NOT CERTIFIED" }
        );
        let basis: Vec<String> = ring
            .monomial_basis(degree)
            .iter()
            .map(|monomial| render_monomial(monomial, ring.flats(), ground))
            .collect();
        println!("      {}", wrap(&basis.join("  "), 72, 6));
    }

    let dimensions = ring.dimensions();
    let dual: Vec<usize> = dimensions.iter().rev().copied().collect();
    if dimensions == dual {
        println!("    Poincaré duality: {dimensions:?}  [holds]");
    } else {
        failures.push(format!("{name}: Poincaré duality fails, {dimensions:?}"));
    }
    let above = ring.grade_above_the_top();
    if above.dimension == 0 && above.monomials > 0 && above.relation_rows > 0 {
        println!(
            "    A^{}: {} chain monomials and {} relation rows go in, dimension 0 comes out  [the \
             ring stops at its top grade]",
            above.degree, above.monomials, above.relation_rows
        );
    } else {
        failures.push(format!(
            "{name}: grade {} returned {above:?}, so the ring does not stop at its top grade",
            above.degree
        ));
    }
    println!(
        "    complete flags normalising the degree map: {} (all agreed, or the build would have \
         refused)",
        ring.complete_flag_count()
    );

    // ---- the ample class ----
    let ground_signed = ground as i64;
    let ample_law = move |flat: u32| {
        let size = flat.count_ones() as i64;
        size * (ground_signed - size)
    };
    let verdict = ring.submodularity_verdict(ample_law);
    println!();
    println!("  the ample class ω = Σ_F c_F x_F with c(S) = |S|·(|E| − |S|):");
    println!("    coefficients: {}", render_coefficients(&ring, ample_law));
    println!("    cone verdict: {}", render_verdict(&verdict));
    if !verdict.is_ample() {
        failures.push(format!(
            "{name}: the declared ample family did not certify as strictly submodular"
        ));
    }
    let ample = match ring.class_from_coefficients(&ring.ample_coefficients()) {
        Ok(class) => class,
        Err(error) => {
            failures.push(format!("{name}: {error}"));
            return;
        }
    };

    let reports = match ring.lefschetz_reports(&ample) {
        Ok(reports) => reports,
        Err(error) => {
            failures.push(format!("{name}: {error}"));
            return;
        }
    };
    for report in &reports {
        print_report(&name, &report_title(report), report, failures, true);
    }

    // ---- the external frame for a top grade of two ----
    if top == 2 {
        match (ring.generator_pairing(), ring.blowup_lattice_pairing()) {
            (Ok(computed), Ok(predicted)) => {
                println!();
                println!("  the external frame — the blown-up projective plane:");
                println!(
                    "    x_{{i}} ↦ H − Σ_{{G ∋ i}} E_G on rank-one flats, x_G ↦ E_G on rank-two \
                     flats, H² = 1, E_G² = −1."
                );
                let rank_two = ring
                    .flats()
                    .iter()
                    .filter(|flat| ring.matroid().rank_of(**flat) == 2)
                    .count();
                let generators = ring.flats().len();
                println!(
                    "    that lattice is Pic(Bl_{rank_two} P²) of rank {}, whose intersection form \
                     has split (1, 0, {}) — the Hodge index.",
                    rank_two + 1,
                    rank_two
                );
                println!(
                    "    the Gram matrix below is on all {generators} GENERATORS, a spanning set \
                     rather than a basis, so it carries a"
                );
                println!(
                    "    {}-dimensional radical: the kernel of the spanning map. Its split is {}.",
                    generators - rank_two - 1,
                    render_inertia(&inertia(&predicted))
                );
                if computed == predicted {
                    println!(
                        "    deg(x_F · x_G) computed IN THE RING agrees with it on all {}×{} \
                         generator pairs  [frames agree]",
                        ring.flats().len(),
                        ring.flats().len()
                    );
                } else {
                    failures.push(format!(
                        "{name}: the ring's generator pairing disagrees with the blow-up lattice"
                    ));
                }
            }
            (Err(error), _) | (_, Err(error)) => {
                failures.push(format!("{name}: {error}"));
            }
        }
    }

    // ---- log-concavity, two frames ----
    println!();
    println!("  the characteristic polynomial, two frames:");
    println!(
        "    χ_M(t) from the Möbius function of the lattice of flats: {}",
        render_polynomial(&characteristic)
    );
    let ring_magnitudes = match ring.ring_characteristic_magnitudes() {
        Ok(values) => values,
        Err(error) => {
            failures.push(format!("{name}: {error}"));
            return;
        }
    };
    let ring_rendered: Vec<String> = ring_magnitudes.iter().map(render_rational).collect();
    let moebius_rendered: Vec<String> = moebius_magnitudes
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    println!(
        "    |μ^k| = deg(α^{{r−k}} β^k), computed IN THE RING: {}",
        ring_rendered.join("  ")
    );
    println!(
        "    |μ^k| from the reduced characteristic polynomial:  {}",
        moebius_rendered.join("  ")
    );
    if ring_rendered == moebius_rendered {
        println!("    [frames agree]");
    } else {
        failures.push(format!(
            "{name}: the ring's μ disagrees with the Möbius function's"
        ));
    }
    let mut log_concave = true;
    let mut lines = Vec::new();
    for window in moebius_magnitudes.windows(3) {
        let left = &window[1] * &window[1];
        let right = &window[0] * &window[2];
        log_concave &= left >= right;
        lines.push(format!(
            "{}² = {left} {} {}·{} = {right}",
            window[1],
            if left >= right { "≥" } else { "<" },
            window[0],
            window[2]
        ));
    }
    if lines.is_empty() {
        println!("    log-concavity: the sequence is too short to carry a window");
    } else {
        println!(
            "    log-concavity (Heron–Rota–Welsh, a consequence of Hodge–Riemann in degree one):"
        );
        for line in lines {
            println!("      {line}");
        }
    }
    if !log_concave {
        failures.push(format!("{name}: the reduced characteristic is not log-concave"));
    }

    // ---- the falsifiers ----
    println!();
    println!("  falsifiers — classes certified OUTSIDE the ample cone:");

    let supermodular_law = |flat: u32| {
        let size = flat.count_ones() as i64;
        size * size
    };
    let supermodular_verdict = ring.submodularity_verdict(supermodular_law);
    println!();
    println!(
        "    (a) c(S) = |S|², strictly supermodular — {}",
        render_verdict(&supermodular_verdict)
    );
    if !matches!(supermodular_verdict, SubmodularVerdict::Violated { .. }) {
        failures.push(format!(
            "{name}: the supermodular family was not certified outside the cone, so it is not a \
             falsifier"
        ));
    }
    let coefficients = ring.coefficients_from_set_function(supermodular_law);
    match ring.class_from_coefficients(&coefficients) {
        Ok(class) => match ring.lefschetz_reports(&class) {
            Ok(reports) => {
                let mut broke = false;
                for report in &reports {
                    let held = report.hodge_riemann_holds && report.lefschetz_is_isomorphism;
                    broke |= !held;
                    println!(
                        "        k = {}: hard Lefschetz rank {} of {} ({}), primitive dim {}, \
                         split {} under hand {:+}  →  {}",
                        report.degree,
                        report.lefschetz_rank,
                        report.ambient_dimension,
                        if report.lefschetz_is_isomorphism {
                            "iso"
                        } else {
                            "NOT an iso"
                        },
                        report.primitive_dimension,
                        render_inertia(&report.primitive_split),
                        report.hand,
                        if held { "held" } else { "BROKE" }
                    );
                }
                if broke {
                    println!("        the falsifier broke the theorem. The check can fail.");
                } else if top >= 2 {
                    failures.push(format!(
                        "{name}: a class certified outside the ample cone did NOT break \
                         Hodge–Riemann — either the fixture or the construction is wrong"
                    ));
                } else {
                    // r = 1. This is a real finding and it bounds what the certificate certifies.
                    let self_intersection = ring
                        .top_self_intersection(&class)
                        .map(|value| render_rational(&value))
                        .unwrap_or_else(|error| error.to_string());
                    println!(
                        "        it did NOT break, and the reason is a number: deg(ω^r) = \
                         {self_intersection} > 0."
                    );
                    println!(
                        "        A^1 here is one-dimensional, so every nonzero class is ample or \
                         anti-ample. The certificate is on the"
                    );
                    println!(
                        "        COEFFICIENT FAMILY, and c ↦ Σ c_F x_F has the linear relations in \
                         its kernel, so a family outside"
                    );
                    println!(
                        "        the cone can still land on a class inside it. Outside-the-cone is \
                         demanded to break only for r ≥ 2."
                    );
                }
            }
            Err(error) => failures.push(format!("{name}: {error}")),
        },
        Err(error) => failures.push(format!("{name}: {error}")),
    }

    let modular_law = |flat: u32| flat.count_ones() as i64;
    let modular_verdict = ring.submodularity_verdict(modular_law);
    println!();
    println!(
        "    (b) c(S) = |S|, modular — {}",
        render_verdict(&modular_verdict)
    );
    let coefficients = ring.coefficients_from_set_function(modular_law);
    match ring.class_from_coefficients(&coefficients) {
        Ok(class) => match ring.lefschetz_reports(&class) {
            Ok(reports) => {
                let mut broke = false;
                for report in &reports {
                    let held = report.hodge_riemann_holds && report.lefschetz_is_isomorphism;
                    broke |= !held;
                    println!(
                        "        k = {}: primitive dim {}, split {} under hand {:+}  →  {}",
                        report.degree,
                        report.primitive_dimension,
                        render_inertia(&report.primitive_split),
                        report.hand,
                        if held { "held" } else { "BROKE" }
                    );
                }
                if broke {
                    println!(
                        "        with r = {top} the form at k = 1 is ±deg(ω·a·b): ω sits INSIDE \
                         the form, and a boundary class breaks it."
                    );
                    if top < 3 {
                        failures.push(format!(
                            "{name}: a boundary class broke Hodge–Riemann at top grade {top}, \
                             where ω enters only through P^k — that would be new"
                        ));
                    }
                } else {
                    println!(
                        "        with r = {top} the form at k = 1 is ±deg(a·b): ω enters only \
                         through P^k = ω^⊥, and the split of the"
                    );
                    println!(
                        "        ambient form is (1, 0, ρ−1) whatever ω is. A boundary class of \
                         positive self-intersection survives that."
                    );
                    if top >= 3 {
                        failures.push(format!(
                            "{name}: a boundary class survived at top grade {top}, where ω is \
                             inside the form — that would be new"
                        ));
                    }
                }
                println!(
                    "        Recorded, not hidden: a falsifier suite that only ever reported \
                     breakage would be concealing this half."
                );
            }
            Err(error) => failures.push(format!("{name}: {error}")),
        },
        Err(error) => failures.push(format!("{name}: {error}")),
    }

    println!();
    println!("    (c) −ω, the ample class with the hand reversed:");
    let negated: Vec<Rat> = ring
        .ample_coefficients()
        .into_iter()
        .map(|coefficient| -coefficient)
        .collect();
    match ring.class_from_coefficients(&negated) {
        Ok(class) => match ring.lefschetz_reports(&class) {
            Ok(reports) => {
                let mut broke = false;
                for report in &reports {
                    let held = report.hodge_riemann_holds && report.lefschetz_is_isomorphism;
                    broke |= !held;
                    println!(
                        "        k = {}: primitive dim {}, split {} under hand {:+}  →  {}",
                        report.degree,
                        report.primitive_dimension,
                        render_inertia(&report.primitive_split),
                        report.hand,
                        if held { "held" } else { "BROKE" }
                    );
                }
                if top % 2 == 1 && !broke {
                    failures.push(format!(
                        "{name}: −ω left an odd top grade intact, which it cannot"
                    ));
                }
                if top % 2 == 1 {
                    println!(
                        "        r = {top} is odd, so ω^r changes sign with ω and the top grade \
                         breaks."
                    );
                } else {
                    println!(
                        "        r = {top} is even, so ω^{{r−2k}} is unchanged by the negation at \
                         every k here and the theorem survives it. Negation is not a falsifier for \
                         an even top grade."
                    );
                }
            }
            Err(error) => failures.push(format!("{name}: {error}")),
        },
        Err(error) => failures.push(format!("{name}: {error}")),
    }
}

fn report_title(report: &LefschetzReport) -> String {
    format!("degree k = {}", report.degree)
}

fn print_report(
    name: &str,
    title: &str,
    report: &LefschetzReport,
    failures: &mut Vec<String>,
    demand: bool,
) {
    println!();
    println!("  {title}   hand (−1)^k = {:+}", report.hand);
    println!(
        "    hard Lefschetz  ω^{} : A^{} (dim {}) → A^{} (dim {})   rank {} of {} → {}",
        report.top - 2 * report.degree,
        report.degree,
        report.ambient_dimension,
        report.top - report.degree,
        report.target_dimension,
        report.lefschetz_rank,
        report.ambient_dimension,
        if report.lefschetz_is_isomorphism {
            "isomorphism"
        } else {
            "NOT an isomorphism"
        }
    );
    if let Some(factors) = &report.lefschetz_invariant_factors {
        let rendered: Vec<String> = factors.iter().map(std::string::ToString::to_string).collect();
        println!(
            "      Smith invariant factors over Z: [{}]",
            wrap(&rendered.join(" "), 68, 8)
        );
    }
    if demand && !report.lefschetz_is_isomorphism {
        failures.push(format!(
            "{name}: hard Lefschetz fails at degree {} under the ample class",
            report.degree
        ));
    }

    println!(
        "    the form deg(ω^{{r−2k}}·a·b) on all of A^{} ({}×{}):",
        report.degree, report.ambient_dimension, report.ambient_dimension
    );
    print_form(&report.ambient_form, 6);
    println!(
        "      split {}   |   the Lefschetz decomposition A^k = ⊕_j ω^{{k−j}} P^j predicts {}  [{}]",
        render_inertia(&report.ambient_split),
        render_inertia(&report.predicted_ambient_split),
        if report.ambient_split_matches_decomposition() {
            "frames agree"
        } else {
            "FRAMES DISAGREE"
        }
    );
    if demand && !report.ambient_split_matches_decomposition() {
        failures.push(format!(
            "{name}: at degree {} the elimination returned {:?} where the decomposition predicts \
             {:?}",
            report.degree, report.ambient_split, report.predicted_ambient_split
        ));
    }

    println!(
        "    the primitive part P^k = ker(ω^{{r−2k+1}}) has dimension {}",
        report.primitive_dimension
    );
    println!(
        "    the Hodge–Riemann form (−1)^k·deg(ω^{{r−2k}}·a·b) restricted to P^k ({}×{}):",
        report.primitive_dimension, report.primitive_dimension
    );
    print_form(&report.primitive_form, 6);
    println!(
        "      split {}  →  Hodge–Riemann {}",
        render_inertia(&report.primitive_split),
        if report.hodge_riemann_holds {
            "holds: the null cone is empty and every passage returns the declared hand"
        } else {
            "FAILS"
        }
    );
    if demand && !report.hodge_riemann_holds {
        failures.push(format!(
            "{name}: Hodge–Riemann fails at degree {} under a certified ample class",
            report.degree
        ));
    }
}

fn report_degenerate_refusals(failures: &mut Vec<String>) {
    println!("degenerate material, refused by type rather than silently computed:");
    let ranks: Vec<u32> = (0..4usize).map(|subset| u32::from(subset & 1 != 0)).collect();
    match Matroid::from_rank_table("a loop", 2, ranks) {
        Err(error) => println!("  a loop:              refused — {error}"),
        Ok(_) => failures.push("a matroid with a loop was accepted".to_owned()),
    }
    let ranks: Vec<u32> = (0..4usize).map(|subset| u32::from(subset != 0)).collect();
    match Matroid::from_rank_table("parallel", 2, ranks) {
        Err(error) => println!("  a parallel pair:     refused — {error}"),
        Ok(_) => failures.push("a matroid with parallel elements was accepted".to_owned()),
    }
    match Matroid::from_rank_table("rank zero", 3, vec![0; 8]) {
        Err(error) => println!("  rank zero:           refused — {error}"),
        Ok(_) => failures.push("a rank-zero matroid was accepted".to_owned()),
    }
    match Matroid::uniform(1, 1).map(ChowRing::new) {
        Ok(Err(error)) => println!("  rank one:            refused — {error}"),
        _ => failures.push("a rank-one matroid produced a Chow ring".to_owned()),
    }
    match Matroid::uniform(5, 6).map(ChowRing::new) {
        Ok(Err(error)) => println!("  rank above aperture: refused — {error}"),
        _ => failures.push("a rank above the aperture produced a Chow ring".to_owned()),
    }
}

fn report_vamos_wall(failures: &mut Vec<String>) {
    println!();
    println!("================================================================================");
    println!("the aperture wall, stated with counts rather than adjectives");
    let vamos = match Matroid::vamos() {
        Ok(vamos) => vamos,
        Err(error) => {
            failures.push(format!("Vámos: {error}"));
            return;
        }
    };
    println!(
        "  Vámos V8: |E| = {}, rank {}, {} proper flats — representable over no division ring,",
        vamos.ground(),
        vamos.rank(),
        vamos.proper_flats().len()
    );
    println!("  which is a strictly stronger non-representability than the non-Pappus matroid's.");
    for degree in 1..=3 {
        match chain_monomial_census(&vamos, degree) {
            Ok((monomials, rows)) => println!(
                "    grade {degree}: {monomials:5} chain monomials against {rows:5} relation rows"
            ),
            Err(error) => failures.push(format!("Vámos census: {error}")),
        }
    }
    println!(
        "  the grade-three elimination is cubic in 997 columns over BigRational and was NOT run."
    );
    println!(
        "  DROPPED, and this is what was dropped: the only fixture here representable over no"
    );
    println!(
        "  division ring. The non-Pappus matroid stands in for it at rank three — representable"
    );
    println!("  over no field, though representable over some noncommutative division rings.");
}

// -------------------------------------------------------------------------------------------
// rendering

fn render_subset(subset: u32, ground: usize) -> String {
    let members: Vec<String> = (0..ground)
        .filter(|element| subset & (1 << element) != 0)
        .map(|element| element.to_string())
        .collect();
    format!("{{{}}}", members.join(""))
}

fn render_monomial(
    monomial: &holonic_engine::matroid_chow::FlagMonomial,
    flats: &[u32],
    ground: usize,
) -> String {
    if monomial.factors().is_empty() {
        return "1".to_owned();
    }
    monomial
        .factors()
        .iter()
        .map(|(flat, exponent)| {
            let base = render_subset(flats[*flat], ground);
            if *exponent == 1 {
                format!("x{base}")
            } else {
                format!("x{base}^{exponent}")
            }
        })
        .collect::<Vec<String>>()
        .join("·")
}

fn render_coefficients(ring: &ChowRing, law: impl Fn(u32) -> i64) -> String {
    let ground = ring.matroid().ground();
    let terms: Vec<String> = ring
        .flats()
        .iter()
        .map(|flat| format!("{}·x{}", law(*flat), render_subset(*flat, ground)))
        .collect();
    wrap(&terms.join(" + "), 68, 6)
}

fn render_verdict(verdict: &SubmodularVerdict) -> String {
    match verdict {
        SubmodularVerdict::StrictlySubmodular => {
            "strictly submodular on every incomparable pair → INSIDE the ample cone".to_owned()
        }
        SubmodularVerdict::ModularSomewhere { left, right } => format!(
            "submodular with equality at ({left:#b}, {right:#b}) → ON THE BOUNDARY of the cone, \
             not inside it"
        ),
        SubmodularVerdict::Violated {
            left,
            right,
            deficit,
        } => format!(
            "submodularity violated at ({left:#b}, {right:#b}) by {deficit} → OUTSIDE the ample \
             cone"
        ),
    }
}

fn render_inertia(split: &Inertia) -> String {
    format!(
        "(positive {}, zero {}, negative {})",
        split.positive, split.zero, split.negative
    )
}

fn render_rational(value: &Rat) -> String {
    if value.is_integer() {
        value.to_integer().to_string()
    } else {
        format!("{}/{}", value.numer(), value.denom())
    }
}

fn render_polynomial(coefficients: &[num_bigint::BigInt]) -> String {
    let degree = coefficients.len() - 1;
    let mut terms = Vec::new();
    for (index, coefficient) in coefficients.iter().enumerate() {
        if coefficient.is_zero() {
            continue;
        }
        let power = degree - index;
        let magnitude = coefficient.abs();
        let body = match power {
            0 => magnitude.to_string(),
            1 => {
                if magnitude.is_one() {
                    "t".to_owned()
                } else {
                    format!("{magnitude}t")
                }
            }
            _ => {
                if magnitude.is_one() {
                    format!("t^{power}")
                } else {
                    format!("{magnitude}t^{power}")
                }
            }
        };
        if terms.is_empty() {
            terms.push(if coefficient.is_negative() {
                format!("−{body}")
            } else {
                body
            });
        } else {
            terms.push(format!(
                "{} {body}",
                if coefficient.is_negative() { "−" } else { "+" }
            ));
        }
    }
    terms.join(" ")
}

fn print_form(form: &SymmetricForm, indent: usize) {
    let pad = " ".repeat(indent);
    let mut widest = 1usize;
    let mut cells = Vec::with_capacity(form.extent());
    for row in 0..form.extent() {
        let mut line = Vec::with_capacity(form.extent());
        for column in 0..form.extent() {
            let rendered = render_rational(form.at(row, column));
            widest = widest.max(rendered.len());
            line.push(rendered);
        }
        cells.push(line);
    }
    for line in cells {
        let body: Vec<String> = line
            .into_iter()
            .map(|cell| format!("{cell:>widest$}"))
            .collect();
        println!("{pad}[ {} ]", body.join(" "));
    }
}

fn wrap(text: &str, width: usize, indent: usize) -> String {
    let pad = " ".repeat(indent);
    let mut lines = Vec::new();
    let mut current = String::new();
    for word in text.split(' ') {
        if !current.is_empty() && current.chars().count() + 1 + word.chars().count() > width {
            lines.push(std::mem::take(&mut current));
        }
        if !current.is_empty() {
            current.push(' ');
        }
        current.push_str(word);
    }
    if !current.is_empty() {
        lines.push(current);
    }
    lines.join(&format!("\n{pad}"))
}

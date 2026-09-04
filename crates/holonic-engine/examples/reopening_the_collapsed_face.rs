//! Reopening the collapsed face.
//!
//! ## What this is
//!
//! `docs/canon/THE_MATHEMATICS_TABLET.md` §1 states the deletion: a float is not a bad approximation *of*
//! a ratio — it is the ratio's series expansion in base two, truncated, with the remainder
//! discarded. So the law is not *"do not expand"*; it is **you may take the expansion, you may not
//! discard the tail.**
//!
//! A collapsed numeric datum is therefore a **partial face of a larger series expansion**, and the
//! machine's job is to found the basis in which that face can continue. That operation has an exact
//! name: **integer relation detection**. Given a face and candidate basis elements `x_1 … x_n`, find
//! integers `a_i`, not all zero, with `Σ a_i x_i = 0`. LLL does it exactly over the integers, and it
//! is how the BBP formula for π was *discovered* rather than derived.
//!
//! ## The four controls, and the second one is the grade
//!
//! 1. **Known identities are recovered**, as exact integers, from faces built by disjoint series.
//! 2. **THE NEGATIVE CONTROL.** A basis that is *provably* relation-free must return **nothing**. A
//!    relation finder that always finds a relation has found nothing at all, and this is the entire
//!    difference between an instrument and a curve-fitting procedure.
//! 3. **Precision dependence is exhibited, not assumed.** The same face and the same basis must fail
//!    at a coarse grain and succeed at a fine one — twice over: once by starving the *lattice* and
//!    once by starving the *tail*.
//! 4. **A collapsed face is refused past its own truncation**, by name.
//!
//! ## The tautology check, which this driver has to pass before anything else counts
//!
//! `CLAUDE.md` §8: a receipt that could not have come out otherwise carries no evidence. The obvious
//! way to fake this deed is to build the π face out of the very arctangents the search is meant to
//! relate. So the two positive controls are built as **duals** and neither face knows the other's
//! identity:
//!
//! ```text
//!   control A   basis {atan(1/2), atan(1/3), pi}      pi built from MACHIN  (16*a5 - 4*a239)
//!   control B   basis {atan(1/5), atan(1/239), pi}    pi built from EULER   (4*a2  + 4*a3)
//! ```
//!
//! Recovering Euler's identity from a Machin-built π means the lattice discovered
//! `4·atan(1/2) + 4·atan(1/3) = 16·atan(1/5) − 4·atan(1/239)`, which is in neither face.
//!
//! ## The exactness route
//!
//! Exact throughout. `BigInt` lattice entries, `Rat` Gram–Schmidt, `Rat` Lovász test. There is no
//! float, no tolerance, no epsilon and no threshold anywhere in `reopening.rs`.
//!
//! The instrument has **three** gates and none of them is a tolerance. Gate 1 is exact refutation by
//! the faces' own enclosures. Gate 2 is frame invariance — `CLAUDE.md` §0's fourth lesson, *an
//! invariant is only visible across two frames*, with the grain and the enclosure endpoint as the
//! frames. Gate 3 is the searched population, `(2A+1)^n · width(residual) < 1`, whose bar is one
//! expected coincidence and therefore chose nothing.
//!
//! **Which gate carries which control is measured below, and the measurement was not what was
//! designed.** Gate 1 alone carries every retained-tail negative control; gate 2's endpoint sub-gauge
//! was built as the repair for collapsed faces and its orbit on the *returned vector* is trivial
//! everywhere measured, so it is reported and not counted; gate 3 is what actually returns nothing on
//! a collapsed face. `CLAUDE.md` §8 requires a gauge to exhibit its own orbit before its agreement is
//! read as evidence, and that requirement is what convicted gate 2 here.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use holonic_engine::exact_value::{CertifiedSeries, ExactInterval, SeriesTailCertificate};
use holonic_engine::reopening::{
    CertifiedBits, DeclaredGrain, EnclosureFrame, ExactFace, FaceProvenance, LatticeWork,
    Reopening, ReopeningError, ReopeningVerdict, arctan_unit_fraction, dyadic_scale,
    finest_admissible_grain, probe_at_frame, probe_at_grain, reopen, reopen_with_frames,
};
use relational_geometry::exact::{Rat, integer};
use relational_geometry::exact_analysis::log_rational_interval;

const ARCTAN_TERMS: u32 = 128;
const LOG_TERMS: u32 = 120;
const LOG_BITS: u32 = 210;

fn arctan_face(denominator: u32, terms: u32) -> ExactFace {
    let series: CertifiedSeries =
        arctan_unit_fraction(denominator, terms).expect("a unit-fraction arctangent");
    // The enclosure IS the retained tail: the partial sum translated by the exact rational
    // remainder interval the certificate returns.
    debug_assert_eq!(
        series.enclosure().lower,
        &series.partial_sum
            + &series
                .tail_certificate
                .remainder_interval()
                .expect("a validated certificate")
                .lower
    );
    ExactFace::from_certified_series(format!("atan(1/{denominator})"), series)
}

fn log_face(value: i64) -> ExactFace {
    let interval =
        log_rational_interval(&integer(value), LOG_TERMS, LOG_BITS).expect("a positive logarithm");
    ExactFace::from_rat_interval(format!("log {value}"), "log_rational_interval", &interval)
        .expect("an ordered enclosure")
}

fn scale_of(value: &Rat) -> String {
    match dyadic_scale(value) {
        None => "0".to_string(),
        Some(exponent) => format!("~2^{exponent}"),
    }
}

fn describe_enclosure(enclosure: &ExactInterval) -> String {
    let width = &enclosure.upper - &enclosure.lower;
    let straddles = enclosure.lower <= Rat::zero() && enclosure.upper >= Rat::zero();
    format!(
        "width {}, {}",
        scale_of(&width),
        if straddles {
            "contains zero"
        } else {
            "EXCLUDES zero -- refuted"
        }
    )
}

fn vector_text(vector: &[BigInt]) -> String {
    let entries: Vec<String> = vector.iter().map(|entry| entry.to_string()).collect();
    format!("({})", entries.join(", "))
}

fn abbreviate(vector: &[BigInt]) -> String {
    let entries: Vec<String> = vector
        .iter()
        .map(|entry| {
            let text = entry.to_string();
            if text.len() > 22 {
                let sign = if entry.is_negative() { "-" } else { "" };
                format!("{sign}~2^{}", entry.magnitude().bits().saturating_sub(1))
            } else {
                text
            }
        })
        .collect();
    format!("({})", entries.join(", "))
}

/// The provenance, returned as the artifact it is rather than as a label.
///
/// `docs/canon/THE_MATHEMATICS_TABLET.md` §2 measured `CertifiedSeries` at thirteen references in one
/// file and `SeriesTailCertificate` at six in one, with **zero in any `examples/`, `tests/` or
/// `bin/` path** -- the half of the enclosure carrier that this movement's question needs, written
/// and never exercised. This driver exercises it, so the certificate is printed and not just used.
fn describe_provenance(face: &ExactFace) -> String {
    match &face.provenance {
        FaceProvenance::Rational => "exact rational".to_string(),
        FaceProvenance::CertifiedSeries(series) => {
            let species: &str = match &series.tail_certificate {
                SeriesTailCertificate::AlternatingMonotone { first_omitted_term } => {
                    return format!(
                        "CertifiedSeries/AlternatingMonotone, {} terms folded, first omitted term {}",
                        series.terms_folded,
                        scale_of(first_omitted_term)
                    );
                }
                SeriesTailCertificate::AbsoluteGeometric { .. } => "AbsoluteGeometric",
                SeriesTailCertificate::ExactTail { .. } => "ExactTail",
            };
            format!(
                "CertifiedSeries/{species}, {} terms folded",
                series.terms_folded
            )
        }
        FaceProvenance::AnalyticEnclosure { carrier } => format!("exact_analysis::{carrier}"),
        FaceProvenance::IntegerCombination { parts } => {
            let terms: Vec<String> = parts
                .iter()
                .map(|(coefficient, name)| format!("{coefficient}*{name}"))
                .collect();
            format!("integer combination {}", terms.join(" + "))
        }
        FaceProvenance::Collapsed { truncated_at_bits } => {
            format!("COLLAPSED at {truncated_at_bits} bits -- the tail is gone")
        }
        FaceProvenance::MeasuredFloat {
            species,
            bits,
            reading,
            ulp_bits,
            source,
        } => format!(
            "{} 0x{bits:x} read as {}, ulp 2^-{ulp_bits}, from {source}",
            species.name(),
            reading.name()
        ),
    }
}

fn report_faces(label: &str, faces: &[ExactFace]) {
    println!("  {label}");
    for face in faces {
        println!(
            "    {:<34} width {:<10} certified to {:<8} {}",
            face.name,
            scale_of(&face.width()),
            face.certified_bits().to_string(),
            describe_provenance(face)
        );
    }
    println!(
        "    finest grain this basis admits: {}",
        finest_admissible_grain(faces)
    );
}

fn report_work(work: &LatticeWork) {
    println!(
        "    work: {} loop steps, {} swaps, {} size reductions, {} Gram recomputations, \
         largest reduced entry {} bits, budget {}",
        work.loop_steps,
        work.swaps,
        work.size_reductions,
        work.gram_recomputations,
        work.largest_entry_bits,
        work.budget
    );
}

fn report(reopening: &Reopening) {
    for probe in &reopening.probes {
        println!(
            "    probe {:<8} frame {:<9} shortest vector {:<40} residual {}",
            probe.grain.to_string(),
            probe.frame.to_string(),
            abbreviate(&probe.coefficients),
            describe_enclosure(&probe.residual)
        );
    }
    match &reopening.verdict {
        ReopeningVerdict::Candidate(candidate) => {
            println!("    RETURNED  {candidate}");
            println!(
                "      coefficients  {}",
                vector_text(&candidate.coefficients)
            );
            println!("      height        {}", candidate.height);
            println!(
                "      residual      {}",
                describe_enclosure(&candidate.residual)
            );
            println!(
                "      chance popn   {}  (expected coincidences in the searched population; \
                 admission needs < 1)",
                scale_of(&candidate.chance_population)
            );
            println!(
                "      grains        {}",
                candidate
                    .grains
                    .iter()
                    .map(|grain| grain.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            println!("      this is a CANDIDATE, not a theorem");
        }
        ReopeningVerdict::InvariantButRefuted {
            coefficients,
            residual,
        } => {
            println!(
                "    RETURNED NOTHING  every grain agreed on {} and the faces PROVE it is not a \
                 relation ({})",
                abbreviate(coefficients),
                describe_enclosure(residual)
            );
        }
        ReopeningVerdict::FrameDependent { vectors } => {
            println!(
                "    RETURNED NOTHING  the frames disagreed; the shortest vector is a coordinate \
                 of the frame, not an invariant of the faces"
            );
            let mut distinct: Vec<&Vec<BigInt>> = Vec::new();
            for vector in vectors {
                if !distinct.contains(&vector) {
                    distinct.push(vector);
                }
            }
            for vector in distinct {
                println!("      {}", abbreviate(vector));
            }
        }
        ReopeningVerdict::BelowTheFacesResolution {
            coefficients,
            chance_population,
            ..
        } => {
            println!(
                "    RETURNED NOTHING  every frame agreed on {} and the faces cannot refute it, \
                 but they cannot resolve it either:",
                abbreviate(coefficients)
            );
            println!(
                "      the searched population of vectors this short is expected to contain {} \
                 that straddle zero by chance",
                scale_of(chance_population)
            );
        }
    }
    report_work(&reopening.total_work());
}

fn main() {
    println!("== reopening the collapsed face ==\n");
    println!("A float is the ratio's series expansion in base two, truncated, with the remainder");
    println!("discarded. A collapsed datum is therefore a partial face of a larger expansion, and");
    println!("the operation that continues it is exact integer relation detection.\n");

    let a2 = arctan_face(2, ARCTAN_TERMS);
    let a3 = arctan_face(3, ARCTAN_TERMS);
    let a5 = arctan_face(5, ARCTAN_TERMS);
    let a239 = arctan_face(239, ARCTAN_TERMS);

    let machin_pi = ExactFace::integer_combination(
        "pi (built from Machin)",
        &[(BigInt::from(16), &a5), (BigInt::from(-4), &a239)],
    )
    .expect("an ordered combination");
    let euler_pi = ExactFace::integer_combination(
        "pi (built from Euler)",
        &[(BigInt::from(4), &a2), (BigInt::from(4), &a3)],
    )
    .expect("an ordered combination");

    let grains = [DeclaredGrain::bits(96), DeclaredGrain::bits(144)];

    println!("-- control 1a: Euler's identity, recovered from a MACHIN-built pi --");
    let euler_basis = vec![a2.clone(), a3.clone(), machin_pi];
    report_faces("faces", &euler_basis);
    let euler = reopen(&euler_basis, &grains).expect("a probeable basis");
    report(&euler);
    println!("    hand check: atan(1/2) + atan(1/3) = pi/4, since (1/2+1/3)/(1-1/6) = 1\n");

    println!("-- control 1b: Machin's identity, recovered from an EULER-built pi --");
    let machin_basis = vec![a5.clone(), a239.clone(), euler_pi];
    report_faces("faces", &machin_basis);
    let machin = reopen(&machin_basis, &grains).expect("a probeable basis");
    report(&machin);
    println!("    hand check: pi/4 = 4*atan(1/5) - atan(1/239), so 16*a5 - 4*a239 - pi = 0\n");

    println!("-- control 2: THE NEGATIVE CONTROL, and it is the grade --");
    println!("   `a*log2 + b*log3 + c*log5 = 0`  iff  `2^a 3^b 5^c = 1`  iff  `a=b=c=0`,");
    println!("   by unique factorisation. There is no relation to find, and the instrument must");
    println!("   say so at every grain pair rather than at one lucky one.\n");

    let three_logs = vec![log_face(2), log_face(3), log_face(5)];
    let four_logs = vec![log_face(2), log_face(3), log_face(5), log_face(7)];
    report_faces("faces (three logarithms)", &three_logs);
    let negative = reopen(&three_logs, &grains).expect("a probeable basis");
    report(&negative);
    println!();
    report_faces("faces (four logarithms)", &four_logs);
    let negative_four = reopen(&four_logs, &grains).expect("a probeable basis");
    report(&negative_four);

    println!("\n    sweep: the negative control across eight independent grain pairs");
    let sweep: [(u32, u32); 8] = [
        (24, 32),
        (32, 48),
        (40, 56),
        (48, 72),
        (56, 88),
        (64, 96),
        (80, 120),
        (96, 144),
    ];
    let mut spurious = 0usize;
    for (coarse, fine) in sweep {
        let pair = [DeclaredGrain::bits(coarse), DeclaredGrain::bits(fine)];
        let three = reopen(&three_logs, &pair).expect("a probeable basis");
        let four = reopen(&four_logs, &pair).expect("a probeable basis");
        let three_returned = three.verdict.candidate().is_some();
        let four_returned = four.verdict.candidate().is_some();
        spurious += usize::from(three_returned) + usize::from(four_returned);
        println!(
            "      grains 2^{coarse:<3} / 2^{fine:<3}   three logs: {:<9} four logs: {}",
            if three_returned {
                "RELATION"
            } else {
                "nothing"
            },
            if four_returned { "RELATION" } else { "nothing" }
        );
    }
    println!("    spurious relations over 16 relation-free searches: {spurious}\n");

    println!("-- control 3: precision dependence, exhibited twice --\n");
    println!("   3a. Starve the LATTICE. Machin's relation has height 16 over three faces, so it");
    println!("       is reachable only where the grain modulus comfortably exceeds 16^3 = 4096.");
    println!("       The faces are the SAME fine faces used in control 1b.");
    let starved_lattice: [(u32, u32); 5] = [(4, 6), (6, 8), (8, 10), (10, 14), (12, 16)];
    for (coarse, fine) in starved_lattice {
        let pair = [DeclaredGrain::bits(coarse), DeclaredGrain::bits(fine)];
        let attempt = reopen(&machin_basis, &pair).expect("a probeable basis");
        println!(
            "       grains 2^{coarse:<3} / 2^{fine:<3}  ->  {}",
            match &attempt.verdict {
                ReopeningVerdict::Candidate(candidate) =>
                    format!("RELATION {}", vector_text(&candidate.coefficients)),
                _ => "nothing".to_string(),
            }
        );
    }
    let fine_pair = [DeclaredGrain::bits(96), DeclaredGrain::bits(144)];
    let recovered = reopen(&machin_basis, &fine_pair).expect("a probeable basis");
    println!(
        "       grains 2^96  / 2^144 ->  {}",
        match &recovered.verdict {
            ReopeningVerdict::Candidate(candidate) =>
                format!("RELATION {}", vector_text(&candidate.coefficients)),
            _ => "nothing".to_string(),
        }
    );

    println!("\n   3b. Starve the TAIL. Same basis, same identity, but the arctangent series is");
    println!(
        "       folded to four terms instead of {ARCTAN_TERMS}. The discarded tail is what sets the"
    );
    println!("       grain ceiling, so a starved tail cannot reach the grain the relation needs.");
    let coarse_a2 = arctan_face(2, 4);
    let coarse_a3 = arctan_face(3, 4);
    let coarse_a5 = arctan_face(5, 4);
    let coarse_a239 = arctan_face(239, 4);
    let coarse_pi = ExactFace::integer_combination(
        "pi (built from Euler, 4 terms)",
        &[(BigInt::from(4), &coarse_a2), (BigInt::from(4), &coarse_a3)],
    )
    .expect("an ordered combination");
    let coarse_basis = vec![coarse_a5, coarse_a239, coarse_pi];
    report_faces("faces (four folded terms)", &coarse_basis);
    let ceiling = finest_admissible_grain(&coarse_basis);
    match ceiling {
        CertifiedBits::Bits(bits) => {
            println!(
                "       the tail permits at most 2^{bits}; asking for more is refused by name:"
            );
            let refusal = probe_at_grain(&coarse_basis, DeclaredGrain::bits(bits + 1))
                .expect_err("past the aperture");
            println!("         {refusal}");
            let pair = [
                DeclaredGrain::bits(bits.saturating_sub(2)),
                DeclaredGrain::bits(bits),
            ];
            let attempt = reopen(&coarse_basis, &pair).expect("a probeable basis");
            println!(
                "       at the finest grains the starved tail allows (2^{} / 2^{bits}):",
                bits.saturating_sub(2)
            );
            report(&attempt);
        }
        other => println!("       unexpected aperture {other}"),
    }
    println!("\n       the same basis with the tail retained ({ARCTAN_TERMS} terms):");
    report_faces("faces", &machin_basis);
    report(&recovered);

    println!("\n-- control 4: a collapsed face is refused past its own truncation --");
    let collapsed = ExactFace::collapsed("atan(1/5) collapsed to 53 bits", &a5, 53);
    println!(
        "    {:<34} certified to {}   (this is what a float hands the machine)",
        collapsed.name,
        collapsed.certified_bits()
    );
    let collapsed_basis = vec![collapsed, a239.clone(), machin_basis[2].clone()];
    match probe_at_grain(&collapsed_basis, DeclaredGrain::bits(96)) {
        Err(ReopeningError::FaceCoarserThanGrain { .. }) => {
            let refusal = probe_at_grain(&collapsed_basis, DeclaredGrain::bits(96))
                .expect_err("past the aperture");
            println!("    at grain 2^96:  {refusal}");
        }
        other => println!("    unexpected: {other:?}"),
    }
    let within = [DeclaredGrain::bits(40), DeclaredGrain::bits(53)];
    let inside = reopen(&collapsed_basis, &within).expect("within the collapse's own aperture");
    println!("    within its own aperture (2^40 / 2^53), the collapsed face still carries Machin:");
    report(&inside);

    println!("\n-- the reachability crossover, measured rather than assumed --");
    println!("   A relation of height A over n faces sits in a lattice whose spurious shortest");
    println!(
        "   vector has height about 2^(g/n), so the relation is the shortest vector only once"
    );
    println!("   2^g exceeds A^n. For Machin that is 16^3 = 2^12. Sweeping the grain finds where");
    println!("   the crossover actually is:");
    let mut crossover: Option<u32> = None;
    for bits in 8u32..=40 {
        let pair = [DeclaredGrain::bits(bits), DeclaredGrain::bits(bits + 4)];
        let attempt = reopen(&machin_basis, &pair).expect("a probeable basis");
        let returned = attempt
            .verdict
            .candidate()
            .map(|candidate| candidate.coefficients.clone());
        let text = match &returned {
            Some(coefficients) => vector_text(coefficients),
            None => "nothing".to_string(),
        };
        if returned.is_some() && crossover.is_none() {
            crossover = Some(bits);
        }
        if bits <= 20 || returned.is_some() {
            println!("      grains 2^{bits:<3} / 2^{:<3}  ->  {text}", bits + 4);
        }
        if crossover.is_some() && bits > crossover.expect("just set") + 2 {
            break;
        }
    }
    match crossover {
        Some(bits) => println!(
            "    first grain that returns Machin: 2^{bits}.  A^n = 16^3 = 2^12, so the measured\n    \
             crossover sits {} bits above the height bound -- that gap is LLL's own approximation\n    \
             slack, and it is a measurement, not a constant anyone chose.",
            bits as i64 - 12
        ),
        None => println!("    no grain in 8..40 returned Machin"),
    }

    println!("\n-- which gate returned nothing, measured --");
    println!("   The instrument has three gates and only measurement says which carries the");
    println!("   negative control:");
    println!("     1. exact refutation      the faces' own enclosures PROVE the sum is nonzero");
    println!("     2. frame invariance      every grain and every enclosure endpoint must agree");
    println!("     3. searched population   (2A+1)^n * width(residual) must be below one");
    println!("   Faces certified to width 2^-W, probed at grain 2^g:");
    println!("     basis        W      g      height of shortest vector   refuted by the faces?");
    let log_certified = match finest_admissible_grain(&three_logs) {
        CertifiedBits::Bits(bits) => bits,
        other => panic!("the logarithm faces have a finite aperture, got {other}"),
    };
    let mut refuted_count = 0usize;
    let mut survived_count = 0usize;
    for grain_bits in [48u32, 96, 144, 180, log_certified - 1, log_certified] {
        let probe = probe_at_grain(&three_logs, DeclaredGrain::bits(grain_bits))
            .expect("within the aperture");
        if probe.refuted {
            refuted_count += 1;
        } else {
            survived_count += 1;
        }
        println!(
            "     three logs   {log_certified:<6} {grain_bits:<6} ~2^{:<24} {}",
            probe.height.magnitude().bits().saturating_sub(1),
            if probe.refuted { "yes" } else { "NO" }
        );
    }
    println!(
        "   exact refutation fired on {refuted_count} of {} probes above; \
         {survived_count} survived it.",
        refuted_count + survived_count
    );
    println!(
        "   The algebra says why. A spurious vector has |sum a_i x_i| ~ 2^(g/n - g) while the"
    );
    println!(
        "   enclosure half-width is ~2^(g/n - W), so the two cross at W = g -- and the aperture"
    );
    println!("   rule already forces W >= g. So on faces whose tail was RETAINED past the grain,");
    println!(
        "   gate 1 alone carries the negative control. That is not a defence of gates 2 and 3;"
    );
    println!("   it is the measurement refusing them here. A gate has to be shown load-bearing");
    println!("   somewhere or it is a check that cannot fail (`CLAUDE.md` §8).");
    println!(
        "\n   So: collapse the same faces to EXACTLY the grain, which is what a float does, and"
    );
    println!("   watch the gates fall over one at a time. This is the movement's thesis at its");
    println!("   sharpest -- the discarded tail is precisely what gate 1 was spending.");
    println!("     collapsed to   probed at   height        gate 1 refutes?   gate 3 population");
    let mut blind_probes = 0usize;
    let mut frames_disagreed = 0usize;
    for collapse_bits in [96u32, 120, 144] {
        let collapsed_logs: Vec<ExactFace> = three_logs
            .iter()
            .map(|face| {
                ExactFace::collapsed(
                    format!("{} collapsed to {collapse_bits} bits", face.name),
                    face,
                    collapse_bits,
                )
            })
            .collect();
        for grain_bits in [collapse_bits - 1, collapse_bits] {
            let probe = probe_at_grain(&collapsed_logs, DeclaredGrain::bits(grain_bits))
                .expect("within the collapse's own aperture");
            if !probe.refuted {
                blind_probes += 1;
            }
            // Gate 2, exhibited: do the enclosure endpoints move the lattice, and do they move the
            // returned vector? Those are different questions and only the second is the gauge.
            let lower = probe_at_frame(
                &collapsed_logs,
                DeclaredGrain::bits(grain_bits),
                EnclosureFrame::Lower,
            )
            .expect("within the aperture");
            let upper = probe_at_frame(
                &collapsed_logs,
                DeclaredGrain::bits(grain_bits),
                EnclosureFrame::Upper,
            )
            .expect("within the aperture");
            let lattice_moved = lower.shortest_row.last() != upper.shortest_row.last();
            let return_moved = lower.coefficients != upper.coefficients;
            if return_moved {
                frames_disagreed += 1;
            }
            println!(
                "     2^-{collapse_bits:<11} 2^{grain_bits:<9}  ~2^{:<10} {:<17} {}",
                probe.height.magnitude().bits().saturating_sub(1),
                if probe.refuted { "yes" } else { "NO -- blind" },
                scale_of(&probe.chance_population)
            );
            println!(
                "                                          gate 2: lattice moved {}, return moved {}",
                if lattice_moved { "yes" } else { "no" },
                if return_moved {
                    "yes"
                } else {
                    "NO -- orbit trivial"
                }
            );
        }
        let pair = [
            DeclaredGrain::bits(collapse_bits - 1),
            DeclaredGrain::bits(collapse_bits),
        ];
        let attempt = reopen(&collapsed_logs, &pair).expect("within the aperture");
        println!(
            "       verdict at 2^{} / 2^{collapse_bits}: {}",
            collapse_bits - 1,
            match &attempt.verdict {
                ReopeningVerdict::Candidate(candidate) =>
                    format!("SPURIOUS RELATION {}", abbreviate(&candidate.coefficients)),
                ReopeningVerdict::InvariantButRefuted { .. } =>
                    "nothing, by gate 1 (exact refutation)".to_string(),
                ReopeningVerdict::FrameDependent { .. } =>
                    "nothing, by gate 2 (frame invariance)".to_string(),
                ReopeningVerdict::BelowTheFacesResolution { .. } =>
                    "nothing, by gate 3 (searched population)".to_string(),
            }
        );
        // What midpoint-only framing -- the naive instrument, and the first form of this one --
        // would have returned on the same faces.
        let naive = reopen_with_frames(&collapsed_logs, &pair, &[EnclosureFrame::Midpoint])
            .expect("within the aperture");
        if let ReopeningVerdict::Candidate(candidate) = &naive.verdict {
            println!(
                "         and with gate 3 removed it returns {} -- a FALSE relation",
                abbreviate(&candidate.coefficients)
            );
        }
    }
    println!("   probes where gate 1 went blind: {blind_probes}.");
    println!("   probes where gate 2's ENDPOINT sub-gauge moved the return: {frames_disagreed}.");
    println!(
        "   Gate 2's GRAIN sub-gauge did fire once above (2^119 vs 2^120 returned different
   vectors). Its ENDPOINT sub-gauge never did: it moves the lattice and does not move
   the answer, because a spurious vector's last"
    );
    println!("   coordinate is already of its own height's order, so a one-unit endpoint shift is");
    println!("   an O(1) relative perturbation. It was tried as the repair and it failed; it is");
    println!("   reported rather than deleted, and it is not counted as a gate here.");
    println!(
        "   Gate 3 is what returns nothing on collapsed faces, and it is not a threshold: the"
    );
    println!("   bar is one expected coincidence in the population the search actually swept.");

    println!("\n-- summary --");
    let mut summary_work = LatticeWork::default();
    for reopening in [
        &euler,
        &machin,
        &negative,
        &negative_four,
        &recovered,
        &inside,
    ] {
        let work = reopening.total_work();
        summary_work.loop_steps += work.loop_steps;
        summary_work.swaps += work.swaps;
        summary_work.size_reductions += work.size_reductions;
        summary_work.gram_recomputations += work.gram_recomputations;
        summary_work.largest_entry_bits =
            std::cmp::max(summary_work.largest_entry_bits, work.largest_entry_bits);
    }
    println!(
        "   Euler recovered      {}",
        euler
            .verdict
            .candidate()
            .map(|candidate| vector_text(&candidate.coefficients))
            .unwrap_or_else(|| "NOTHING".to_string())
    );
    println!(
        "   Machin recovered     {}",
        machin
            .verdict
            .candidate()
            .map(|candidate| vector_text(&candidate.coefficients))
            .unwrap_or_else(|| "NOTHING".to_string())
    );
    println!("   negative control     {spurious} spurious relations over 16 searches");
    println!(
        "   total reduction work {} loop steps, {} swaps, {} Gram recomputations",
        summary_work.loop_steps, summary_work.swaps, summary_work.gram_recomputations
    );
    println!("   every figure above is a count of steps. No clock selected anything.");

    assert!(
        spurious == 0,
        "the negative control is the grade and it did not hold"
    );
    assert!(
        euler.verdict.candidate().is_some() && machin.verdict.candidate().is_some(),
        "both positive controls must return"
    );
    // The relations are the ones a hand check gives.
    assert_eq!(
        euler.verdict.candidate().expect("Euler").coefficients,
        vec![BigInt::from(4), BigInt::from(4), BigInt::from(-1)]
    );
    assert_eq!(
        machin.verdict.candidate().expect("Machin").coefficients,
        vec![BigInt::from(16), BigInt::from(-4), BigInt::from(-1)]
    );
    // And the residuals are enclosures, never points: no finite tail proves a real sum is zero.
    let residual = &machin.verdict.candidate().expect("Machin").residual;
    assert!(!residual.is_point());
    assert!(residual.lower <= Rat::zero() && residual.upper >= Rat::zero());
    let _ = (BigInt::one(), BigInt::zero(), Rat::one().is_one());
}

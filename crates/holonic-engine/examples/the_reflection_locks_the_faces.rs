//! The reflection locks the faces, and the rational circle has exactly four points on it.
//!
//! `crates/holonic-engine/src/causal_reflection.rs` is the discrete Kramers-Kronig face lock — the
//! dispersive/absorptive decomposition that **is** integration by reflection. It has one library
//! caller and **no direct driver**. This file conducts through it.
//!
//! The module closes
//! `research/records/2026-08-05_THE_RECEIVER_QUOTIENTS_THE_SPECTRUM_CAUSALITY_LOCKS_ITS_FACES.md`
//! §8's falsifier — *"compute both faces independently over a declared aperture and test the Hilbert
//! transform relation exactly"* — and states its own law:
//!
//! ```text
//!   h_e[n] = (h[n] + h[-n]) / 2     the DISPERSIVE face   (even; carries Re chi)
//!   h_o[n] = (h[n] - h[-n]) / 2     the ABSORPTIVE face   (odd;  carries Im chi)
//!
//!   with sigma[n] = sgn(n):
//!     h_o = sigma . h_e  everywhere        <=>  h[n] = 0 for every n < 0
//!     h_e = sigma . h_o  everywhere n != 0 <=>  h[n] = 0 for every n < 0
//!
//!   Falsifier. If a response with a nonzero pre-stimulus value ever locks, or a response whose
//!   pre-stimulus values are all zero ever fails to lock, this law is false.
//! ```
//!
//! ## Declared apertures
//!
//! - **Carrier.** Exact `Rat` throughout, and Gaussian rationals for every spectral evaluation.
//!   There is no float, no tolerance, no epsilon, no threshold and no fit anywhere below. No
//!   principal value is taken and none is needed: the continuum kernel's pole sits at `omega' =
//!   omega`, whose lattice image is `n = 0`, the unique fixed point of `n -> -n`, where
//!   `sigma[0] = 0`. What a symmetric omission would discard is retained as a subtraction constant.
//! - **Response lattice.** `n` in `[-M, M]` with the stimulus at `n = 0`. `M` in `{1, 2, 3}` below.
//! - **Three exhaustive sweeps**, declared with their sizes so a collapsed class cannot pass
//!   silently: `M = 1` over `{-2, 0, 3}` (27), `M = 2` over `{-1, 0, 1, 2}` (1,024), and
//!   `M = 3` over `{-1, 0, 1}` (2,187). The middle one is the module's own; the outer two are not.
//! - **The spectral aperture is `N = 4` and it is a THEOREM, not an implementation limit.** By
//!   Niven's theorem the only rational values of `cos theta` at rational multiples of `pi` are
//!   `0, +-1/2, +-1`, and of `sin theta` only `0, +-1`; both spectral faces of every rational
//!   response are rational exactly when `N` is in `{1, 2, 4}`. Section 7 does not assert this — it
//!   **measures** the rational unit circle by exact powering over a declared family of 136 slopes,
//!   and finds that exactly four of its points are roots of unity.
//! - **The four-point organ's aperture is support inside one period, `n` in `[-1, 2]`.** Past it,
//!   folding aliases, the organ **appears to return**, and it is answering a different question.
//!   Section 9 exhibits exactly that.
//!
//! ```text
//! cargo run --release --example the_reflection_locks_the_faces
//! ```
//!
//! Exits non-zero if any declared control fails.

use std::collections::BTreeSet;

use holonic_engine::causal_reflection::{
    CausalReflectionError, CausalResponse, CausalityLock, ExactResponseFace, FaceParity,
    RationalCirclePoint, causality_lock,
};
use num_traits::{One, Zero};
use relational_geometry::{Rat, format_rat, integer, rat};

/// The declared lattice grain. It appears in every carrier and must move nothing in the law;
/// section 10 measures both halves of that.
fn grain() -> Rat {
    rat(1, 3)
}

fn response(half_extent: u32, values: &[(i64, i64)]) -> CausalResponse {
    CausalResponse::new(
        half_extent,
        grain(),
        values
            .iter()
            .map(|(numerator, denominator)| rat(*numerator, *denominator))
            .collect(),
    )
    .expect("a lawful response declaration")
}

// --- the fixture family; each declares in its own name what it can exercise ------------------

/// `M = 3`, causal, two-sided retarded tail, nonzero instantaneous value.
fn causal_tail() -> CausalResponse {
    response(
        3,
        &[(0, 1), (0, 1), (0, 1), (5, 2), (-3, 1), (7, 4), (1, 1)],
    )
}

/// `M = 3`, causal and instantaneous-free: `h[0] = 0`, so the subtraction constant is zero and the
/// absorptive reading is **not** blind on this material.
fn causal_without_instantaneous() -> CausalResponse {
    response(
        3,
        &[(0, 1), (0, 1), (0, 1), (0, 1), (4, 1), (-1, 3), (2, 1)],
    )
}

/// `M = 3`, **not** causal: one nonzero value at `n = -2`.
fn advanced_leak() -> CausalResponse {
    response(
        3,
        &[(0, 1), (9, 5), (0, 1), (5, 2), (-3, 1), (7, 4), (1, 1)],
    )
}

/// `M = 3`, not causal, and **even**: its absorptive face is identically zero. The symmetric trap.
fn even_response() -> CausalResponse {
    response(
        3,
        &[(2, 1), (-1, 1), (3, 1), (5, 1), (3, 1), (-1, 1), (2, 1)],
    )
}

/// `M = 3`, not causal, and **odd**: its dispersive face is identically zero.
fn odd_response() -> CausalResponse {
    response(
        3,
        &[(-2, 1), (1, 1), (-3, 1), (0, 1), (3, 1), (-1, 1), (2, 1)],
    )
}

/// `M = 2`, causal, supported only at the stimulus. **Cannot exercise the pairing** — the signature
/// annihilates its only coordinate, so both readings lock whatever the response was.
fn instantaneous_only() -> CausalResponse {
    response(2, &[(0, 1), (0, 1), (11, 2), (0, 1), (0, 1)])
}

fn every_fixture() -> Vec<(&'static str, CausalResponse, bool, bool)> {
    vec![
        ("causal_tail", causal_tail(), true, true),
        (
            "causal_without_instantaneous",
            causal_without_instantaneous(),
            true,
            true,
        ),
        ("advanced_leak", advanced_leak(), false, true),
        ("even_response", even_response(), false, true),
        ("odd_response", odd_response(), false, true),
        ("instantaneous_only", instantaneous_only(), true, false),
    ]
}

// --- rendering --------------------------------------------------------------------------------

fn lattice_header(half_extent: u32) -> String {
    let extent = half_extent as i64;
    (-extent..=extent)
        .map(|index| format!("{index:>9}"))
        .collect::<Vec<_>>()
        .join(" ")
}

fn render_values(values: &[Rat]) -> String {
    values
        .iter()
        .map(|value| format!("{:>9}", format_rat(value)))
        .collect::<Vec<_>>()
        .join(" ")
}

fn render_four(values: &[Rat; 4]) -> String {
    values
        .iter()
        .map(|value| format!("{:>10}", format_rat(value)))
        .collect::<Vec<_>>()
        .join(" ")
}

fn render_point(point: &RationalCirclePoint) -> String {
    format!(
        "({}, {})",
        format_rat(point.real()),
        format_rat(point.imaginary())
    )
}

fn print_response(label: &str, fixture: &CausalResponse) {
    println!("  {label}");
    println!("    n           {}", lattice_header(fixture.half_extent()));
    println!("    h[n]        {}", render_values(fixture.values()));
    println!(
        "    h_e[n]      {}",
        render_values(fixture.dispersive_face().values())
    );
    println!(
        "    h_o[n]      {}",
        render_values(fixture.absorptive_face().values())
    );
}

fn print_reflection_table(label: &str, lock: &CausalityLock, forward: bool) {
    let reflection = if forward {
        &lock.dispersive_to_absorptive
    } else {
        &lock.absorptive_to_dispersive
    };
    println!(
        "  {label}   source parity {:?}   locks {}",
        reflection.source_parity,
        reflection.locks()
    );
    println!(
        "    {:>5} {:>12} {:>12} {:>12}  {}",
        "n", "derived", "measured", "residual", ""
    );
    for residual in &reflection.residuals {
        let blind = residual.index == 0;
        println!(
            "    {:>5} {:>12} {:>12} {:>12}  {}",
            residual.index,
            format_rat(&residual.derived),
            format_rat(&residual.measured),
            format_rat(&residual.residual),
            if blind {
                "<- the reflection's fixed point; sigma[0] = 0, so this reading is blind here"
            } else if !residual.residual.is_zero() {
                "<- STANDING"
            } else {
                ""
            }
        );
    }
}

/// The exhaustive sweep: every response on `[-M, M]` with values from `alphabet`.
struct Sweep {
    label: String,
    total: usize,
    causal: usize,
    acausal: usize,
    exercised: usize,
    law_failures: Vec<Vec<Rat>>,
    standing_seen: usize,
    locked_causal: usize,
    locked_acausal: usize,
}

fn sweep(half_extent: u32, alphabet: &[Rat]) -> Sweep {
    let width = 2 * half_extent as usize + 1;
    let total = alphabet.len().pow(width as u32);
    let mut result = Sweep {
        label: format!(
            "M = {half_extent}, alphabet {{{}}}, {total} declarations",
            alphabet
                .iter()
                .map(format_rat)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        total,
        causal: 0,
        acausal: 0,
        exercised: 0,
        law_failures: Vec::new(),
        standing_seen: 0,
        locked_causal: 0,
        locked_acausal: 0,
    };
    for code in 0..total {
        let mut remaining = code;
        let values: Vec<Rat> = (0..width)
            .map(|_| {
                let digit = remaining % alphabet.len();
                remaining /= alphabet.len();
                alphabet[digit].clone()
            })
            .collect();
        let fixture = CausalResponse::new(half_extent, grain(), values.clone())
            .expect("a lawful declaration");
        let lock = causality_lock(&fixture).expect("a lawful lock");
        if !lock.law_holds() {
            result.law_failures.push(values);
        }
        if fixture.is_causal() {
            result.causal += 1;
            if lock.locks() {
                result.locked_causal += 1;
            }
        } else {
            result.acausal += 1;
            if lock.locks() {
                result.locked_acausal += 1;
            }
            result.standing_seen += lock.dispersive_to_absorptive.standing_indices.len();
        }
        if fixture.exercises_the_pairing() {
            result.exercised += 1;
        }
    }
    result
}

fn main() {
    println!("THE REFLECTION LOCKS THE FACES");
    println!("==============================");
    println!("truth_status=established-bounded");
    println!("evidence=computational-witness");
    println!("law=the two faces lock exactly when the response vanishes before the stimulus");
    println!(
        "organ=crates/holonic-engine/src/causal_reflection.rs   (one library caller, no driver)"
    );

    let mut holds: Vec<(&str, bool, String)> = Vec::new();

    // ===========================================================================================
    println!("\n\n1. THE FIXTURE FAMILY, AND WHAT EACH CAN EXERCISE");
    println!("-------------------------------------------------");
    println!(
        "  {:<30} {:>8} {:>11} {:>16} {:>14}",
        "fixture", "causal", "exercises", "advanced support", "h[0]"
    );
    let mut declarations_agree = true;
    for (name, fixture, declared_causal, declared_exercises) in every_fixture() {
        declarations_agree &= fixture.is_causal() == declared_causal
            && fixture.exercises_the_pairing() == declared_exercises;
        println!(
            "  {:<30} {:>8} {:>11} {:>16} {:>14}",
            name,
            fixture.is_causal(),
            fixture.exercises_the_pairing(),
            format!("{:?}", fixture.advanced_support()),
            format_rat(&fixture.instantaneous_value())
        );
    }
    let causal_count = every_fixture()
        .iter()
        .filter(|(_, fixture, _, _)| fixture.is_causal())
        .count();
    println!(
        "\n  {causal_count} causal, {} acausal — both classes populated, so the biconditional is",
        every_fixture().len() - causal_count
    );
    println!("  tested on both sides rather than confirmed on one.");
    println!(
        "  `instantaneous_only` is retained precisely BECAUSE it cannot exercise the pairing:"
    );
    println!("  a fixture whose only coordinate the signature annihilates would lock whatever the");
    println!(
        "  response was, and a family without such a member could not name that failure mode."
    );
    holds.push((
        "every fixture's declared causality and exercisability match what the organ returns",
        declarations_agree && causal_count >= 3 && every_fixture().len() - causal_count >= 3,
        format!(
            "{causal_count} causal against {} acausal",
            every_fixture().len() - causal_count
        ),
    ));

    // ===========================================================================================
    println!("\n\n2. THE ARTIFACT — THE TWO FACES, AND THE RESPONSE THEY REBUILD");
    println!("--------------------------------------------------------------");
    let mut recomposes = true;
    let mut faces_nonvacuous = true;
    for (name, fixture, _, _) in every_fixture() {
        print_response(name, &fixture);
        let rebuilt =
            CausalResponse::from_faces(&fixture.dispersive_face(), &fixture.absorptive_face())
                .expect("two lawful faces");
        recomposes &= rebuilt == fixture;
        println!(
            "    h_e + h_o == h exactly: {}    even face zero: {}    odd face zero: {}",
            rebuilt == fixture,
            fixture.dispersive_face().is_zero(),
            fixture.absorptive_face().is_zero()
        );
        if name == "causal_tail" || name == "advanced_leak" {
            faces_nonvacuous &=
                !fixture.dispersive_face().is_zero() && !fixture.absorptive_face().is_zero();
        }
    }
    println!(
        "\n  `even_response` and `odd_response` are the degenerate traps: one has a vanishing"
    );
    println!("  absorptive face and the other a vanishing dispersive face, and BOTH must still be");
    println!("  refused. A nonzero response with a mirror symmetry cannot be causal.");
    holds.push((
        "the two faces recompose every fixture exactly, and neither face is vacuous where it matters",
        recomposes && faces_nonvacuous,
        format!("{} fixtures recomposed bit-exactly", every_fixture().len()),
    ));

    // ===========================================================================================
    println!("\n\n3. THE LAW, DECIDED BY EXHAUSTION AT THREE APERTURES");
    println!("----------------------------------------------------");
    println!("  The biconditional `locks() == is_causal()` is decided over every response on the");
    println!(
        "  declared lattice with values from the declared alphabet. A sweep whose causal class"
    );
    println!(
        "  or acausal class had collapsed would be a check that could not fail, so both counts"
    );
    println!("  are printed and both are required non-zero.");
    let sweeps = [
        sweep(1, &[integer(-2), Rat::zero(), integer(3)]),
        sweep(2, &[integer(-1), Rat::zero(), integer(1), integer(2)]),
        sweep(3, &[integer(-1), Rat::zero(), integer(1)]),
    ];
    println!(
        "\n  {:<50} {:>7} {:>8} {:>9} {:>10} {:>9} {:>9}",
        "sweep", "total", "causal", "acausal", "exercised", "failures", "standing"
    );
    let mut every_sweep_holds = true;
    for reading in &sweeps {
        every_sweep_holds &= reading.law_failures.is_empty()
            && reading.causal > 0
            && reading.acausal > 0
            && reading.standing_seen > 0
            && reading.locked_causal == reading.causal
            && reading.locked_acausal == 0;
        println!(
            "  {:<50} {:>7} {:>8} {:>9} {:>10} {:>9} {:>9}",
            reading.label,
            reading.total,
            reading.causal,
            reading.acausal,
            reading.exercised,
            reading.law_failures.len(),
            reading.standing_seen
        );
    }
    println!(
        "\n  Every causal declaration locked, no acausal declaration locked, and the standing"
    );
    println!("  column is the number of standing residual ADDRESSES the acausal half returned —");
    println!("  non-zero, so the acausal half is evidence and not an empty class.");
    println!(
        "  The middle sweep is the module's own test. The other two are new apertures: {} and {}",
        sweeps[0].total, sweeps[2].total
    );
    println!("  declarations at half-extents the module never runs.");
    holds.push((
        "the lock biconditional holds over 3,238 exhaustively enumerated responses at three apertures",
        every_sweep_holds,
        format!(
            "{} + {} + {} declarations, 0 law failures, {} standing residual addresses",
            sweeps[0].total,
            sweeps[1].total,
            sweeps[2].total,
            sweeps.iter().map(|reading| reading.standing_seen).sum::<usize>()
        ),
    ));

    // ===========================================================================================
    println!("\n\n4. THE RESIDUAL IS THE ACAUSAL VALUE AT ITS OWN ADDRESS");
    println!("-------------------------------------------------------");
    println!("  The return is never a norm and never a fit. For a response with an occupied");
    println!(
        "  pre-stimulus region the residual at `n < 0` is exactly `h[n]`, and at `n > 0` it is"
    );
    println!("  exactly `-h[-n]` for the dispersive reading and `+h[-n]` for the absorptive one.");
    let leak = advanced_leak();
    let leak_lock = causality_lock(&leak).expect("a lawful lock");
    println!();
    print_response("advanced_leak", &leak);
    println!();
    print_reflection_table("dispersive -> absorptive", &leak_lock, true);
    println!();
    print_reflection_table("absorptive -> dispersive", &leak_lock, false);
    println!(
        "\n  standing residuals, with their addresses: {:?}",
        leak_lock
            .dispersive_to_absorptive
            .standing_residuals()
            .iter()
            .map(|(index, residual)| format!("n={index}: {}", format_rat(residual)))
            .collect::<Vec<_>>()
    );
    let mut addresses_exact = true;
    for index in leak.indices() {
        if index < 0 {
            addresses_exact &= leak_lock.dispersive_to_absorptive.residual_at(index)
                == leak.value(index)
                && leak_lock.absorptive_to_dispersive.residual_at(index) == leak.value(index);
        } else if index > 0 {
            addresses_exact &= leak_lock.dispersive_to_absorptive.residual_at(index)
                == -leak.value(-index)
                && leak_lock.absorptive_to_dispersive.residual_at(index) == leak.value(-index);
        }
    }
    holds.push((
        "every residual equals the acausal value at that address or its mirror, exactly",
        addresses_exact
            && !leak_lock
                .dispersive_to_absorptive
                .standing_indices
                .is_empty(),
        format!(
            "{} standing addresses on advanced_leak",
            leak_lock.dispersive_to_absorptive.standing_indices.len()
        ),
    ));

    // ===========================================================================================
    println!("\n\n5. THE PAIRING IS ASYMMETRIC, AND WHAT IT ANNIHILATES IS RETAINED");
    println!("-----------------------------------------------------------------");
    println!("  dispersive -> absorptive is exact at EVERY index, the fixed point included.");
    println!("  absorptive -> dispersive is exact everywhere EXCEPT the fixed point, where it is");
    println!(
        "  blind — and the datum it cannot supply is exactly the instantaneous response h[0]."
    );
    println!("  This is not a discretization defect. It is the discrete form of the fact that an");
    println!(
        "  UNSUBTRACTED dispersion relation does not determine Re chi; the physical statement"
    );
    println!("  needs chi_infinity supplied separately, and a SUBTRACTED relation is what carries");
    println!("  it. Here the constant is exhibited exactly, with its address.");
    let tail = causal_tail();
    let tail_lock = causality_lock(&tail).expect("a lawful lock");
    println!(
        "\n  causal_tail        h[0] = {}   subtraction constants {:?}",
        format_rat(&tail.instantaneous_value()),
        tail_lock
            .subtraction_constants
            .iter()
            .map(|constant| format!("n={}: {}", constant.index, format_rat(&constant.value)))
            .collect::<Vec<_>>()
    );
    println!(
        "    dispersive reading's residual at 0: {}    absorptive reading's residual at 0: {}",
        format_rat(&tail_lock.dispersive_to_absorptive.residual_at(0)),
        format_rat(&tail_lock.absorptive_to_dispersive.residual_at(0))
    );
    let clean = causal_without_instantaneous();
    let clean_lock = causality_lock(&clean).expect("a lawful lock");
    println!(
        "  causal_without_... h[0] = {}   subtraction constants {:?}",
        format_rat(&clean.instantaneous_value()),
        clean_lock
            .subtraction_constants
            .iter()
            .map(|constant| format!("n={}: {}", constant.index, format_rat(&constant.value)))
            .collect::<Vec<_>>()
    );
    println!(
        "    dispersive reading's residual at 0: {}    absorptive reading's residual at 0: {}",
        format_rat(&clean_lock.dispersive_to_absorptive.residual_at(0)),
        format_rat(&clean_lock.absorptive_to_dispersive.residual_at(0))
    );
    println!(
        "\n  So the blindness is a property of the MATERIAL, not of the law: on a response with"
    );
    println!("  no instantaneous value nothing is lost, and the pair of readings above is what");
    println!("  makes that a measurement rather than an assertion.");
    holds.push((
        "the reflection is blind at exactly one address, and the annihilated datum is h[0]",
        tail_lock.subtraction_constants.len() == 1
            && tail_lock.subtraction_constants[0].index == 0
            && tail_lock.subtraction_constants[0].value == tail.instantaneous_value()
            && !tail_lock.subtraction_constants[0].value.is_zero()
            && tail_lock.dispersive_to_absorptive.residual_at(0).is_zero()
            && tail_lock.absorptive_to_dispersive.residual_at(0) == tail.instantaneous_value()
            && clean_lock.subtraction_constants[0].value.is_zero()
            && clean_lock.absorptive_to_dispersive.residual_at(0).is_zero(),
        format!(
            "constant {} on causal_tail, {} on the instantaneous-free control",
            format_rat(&tail_lock.subtraction_constants[0].value),
            format_rat(&clean_lock.subtraction_constants[0].value)
        ),
    ));

    // ===========================================================================================
    println!("\n\n6. THE KERNEL IS OCCUPIED — RETURN THE COLLIDING PAIR, NOT A RANK");
    println!("-----------------------------------------------------------------");
    println!("  A metamer is a stronger falsifier than a number. Two DISTINCT responses, both");
    println!("  causal, both locking, with bit-identical absorptive faces:");
    let left = causal_tail();
    let right = left
        .instantaneous_metamer(rat(-19, 7))
        .expect("a distinct instantaneous value");
    print_response("left  (h[0] = 5/2)", &left);
    print_response("right (h[0] = -19/7)", &right);
    let separation = left.dispersive_face().value(0) - right.dispersive_face().value(0);
    println!(
        "\n  identical absorptive faces : {}",
        left.absorptive_face() == right.absorptive_face()
    );
    println!(
        "  distinct dispersive faces  : {}   separated at n = 0 by exactly {}",
        left.dispersive_face() != right.dispersive_face(),
        format_rat(&separation)
    );
    println!(
        "  both members lock          : {} and {}",
        causality_lock(&left).expect("lawful").locks(),
        causality_lock(&right).expect("lawful").locks()
    );
    println!("  a metamer needs two members: replacing h[0] by 5/2, the value already standing,",);
    println!(
        "                               returns {:?}",
        left.instantaneous_metamer(rat(5, 2))
    );
    holds.push((
        "the occupied kernel is returned as an exhibited pair with a nonzero exact separation",
        left != right
            && right.is_causal()
            && left.absorptive_face() == right.absorptive_face()
            && left.dispersive_face() != right.dispersive_face()
            && separation == rat(5, 2) - rat(-19, 7)
            && !separation.is_zero()
            && causality_lock(&left).expect("lawful").locks()
            && causality_lock(&right).expect("lawful").locks(),
        format!("separation {}", format_rat(&separation)),
    ));

    // ===========================================================================================
    println!("\n\n7. THE RATIONAL UNIT CIRCLE HAS EXACTLY FOUR ROOTS OF UNITY ON IT");
    println!("-----------------------------------------------------------------");
    println!("  The module declares itself APERTURE-COMPLETE at `N` in {{1, 2, 4}} by Niven's");
    println!("  theorem. That is a claim about which spectral lattices exist inside the exact");
    println!("  rational carrier at all, and it is measured here rather than asserted.");
    println!();
    println!(
        "  `RationalCirclePoint::from_slope(s)` is the stereographic parametrization from -1;"
    );
    println!("  it reaches every rational point of the unit circle except -1 itself, which");
    println!(
        "  `RationalCirclePoint::new` takes directly. A spectral lattice of resolution N needs"
    );
    println!("  `z` with `z^N = 1`. Every point of a declared family is powered exactly and asked");
    println!("  whether it ever returns.");

    let mut family: Vec<(String, RationalCirclePoint)> = Vec::new();
    let mut seen = BTreeSet::new();
    for numerator in -8i64..=8 {
        for denominator in 1i64..=8 {
            let point = RationalCirclePoint::from_slope(&rat(numerator, denominator));
            let key = render_point(&point);
            if seen.insert(key.clone()) {
                family.push((key, point));
            }
        }
    }
    let minus_one = RationalCirclePoint::new(integer(-1), Rat::zero())
        .expect("(-1, 0) is exactly on the circle");
    let key = render_point(&minus_one);
    if seen.insert(key.clone()) {
        family.push((key, minus_one));
    }

    let horizon = 24u32;
    let mut roots: Vec<(String, u32)> = Vec::new();
    let mut on_the_circle = true;
    for (key, point) in &family {
        on_the_circle &=
            point.real() * point.real() + point.imaginary() * point.imaginary() == Rat::one();
        for order in 1..=horizon {
            let (real, imaginary) = point.power(order as i64);
            if real.is_one() && imaginary.is_zero() {
                roots.push((key.clone(), order));
                break;
            }
        }
    }
    println!(
        "\n  declared family: 136 slopes p/q with |p| <= 8 and 1 <= q <= 8, plus the point -1,"
    );
    println!(
        "  giving {} DISTINCT rational circle points; every one verified exactly on x^2 + y^2 = 1: {on_the_circle}",
        family.len()
    );
    println!(
        "  points with z^N = 1 for some N <= {horizon}:  {}",
        roots
            .iter()
            .map(|(key, order)| format!("{key} order {order}"))
            .collect::<Vec<_>>()
            .join("   ")
    );
    println!(
        "  every other point of the family never returns within the horizon: {} of {}",
        family.len() - roots.len(),
        family.len()
    );
    println!(
        "\n  Four points, of orders 1, 2, 4 and 4. Their orders generate exactly {{1, 2, 4}},"
    );
    println!("  which is the module's declared spectral aperture — reached by exact powering and");
    println!("  not by citing the theorem. And the missing lattices are refused BY NAME, with the");
    println!("  exact miss, rather than being unimplemented:");
    let mut refusals_named = true;
    for (label, x_numerator, x_denominator) in [
        ("N = 3 needs cos(2pi/3) = -1/2", -1i64, 2i64),
        ("N = 6 needs cos(2pi/6) =  1/2", 1, 2),
    ] {
        let mut misses = Vec::new();
        for numerator in -6i64..=6 {
            for denominator in 1i64..=6 {
                let attempt = RationalCirclePoint::new(
                    rat(x_numerator, x_denominator),
                    rat(numerator, denominator),
                );
                match attempt {
                    Err(CausalReflectionError::NotOnTheUnitCircle { deviation }) => {
                        misses.push(*deviation);
                    }
                    _ => refusals_named = false,
                }
            }
        }
        let distinct: BTreeSet<String> = misses.iter().map(format_rat).collect();
        println!(
            "    {label}, so y^2 = 3/4: all {} rational y with |p|,q <= 6 refused, {} distinct exact",
            misses.len(),
            distinct.len()
        );
        println!(
            "      deviations y^2 - 3/4, none of them zero: {}",
            misses.iter().all(|deviation| !deviation.is_zero())
        );
        println!("      and 4p^2 = 3q^2 has no integer solution, because 3 is not a square.");
    }
    holds.push((
        "exactly four points of the rational unit circle are roots of unity, of orders 1, 2, 4, 4",
        on_the_circle
            && roots.len() == 4
            && roots
                .iter()
                .map(|(_, order)| *order)
                .collect::<BTreeSet<_>>()
                == BTreeSet::from([1, 2, 4])
            && family.len() > 4,
        format!(
            "{} of {} distinct rational circle points return within {horizon}",
            roots.len(),
            family.len()
        ),
    ));
    holds.push((
        "the N = 3 and N = 6 lattices are refused by name with the exact miss, not left unbuilt",
        refusals_named,
        "every declared rational y at x = +-1/2 returned NotOnTheUnitCircle".to_owned(),
    ));

    // ===========================================================================================
    println!("\n\n8. THE FACE NAMES ARE A THEOREM — Re chi AND Im chi, EXACTLY");
    println!("------------------------------------------------------------");
    println!("  On the unit circle `z^-1 = conj z`, so at any rational circle point the transfer");
    println!("  function `chi(z) = sum_n h[n] z^-n` has both parts in Q, computed by exact");
    println!(
        "  Gaussian-rational powering with no transcendental anywhere. The claim under test is"
    );
    println!("  that the even face carries Re chi and NOTHING else, and the odd face Im chi and");
    println!("  nothing else.");
    let probe_points: Vec<RationalCirclePoint> = [(0, 1), (1, 2), (-3, 5), (7, 3)]
        .into_iter()
        .map(|(numerator, denominator)| {
            RationalCirclePoint::from_slope(&rat(numerator, denominator))
        })
        .collect();
    let mut faces_carry = true;
    let mut nonzero_dispersive = 0usize;
    let mut nonzero_absorptive = 0usize;
    println!(
        "\n  {:<30} {:<18} {:>16} {:>16}",
        "fixture", "z", "Re chi(z)", "Im chi(z)"
    );
    for (name, fixture, _, _) in every_fixture() {
        let as_even = CausalResponse::new(
            fixture.half_extent(),
            fixture.sample_step().clone(),
            fixture.dispersive_face().values().to_vec(),
        )
        .expect("the even face is a response");
        let as_odd = CausalResponse::new(
            fixture.half_extent(),
            fixture.sample_step().clone(),
            fixture.absorptive_face().values().to_vec(),
        )
        .expect("the odd face is a response");
        for point in &probe_points {
            let whole = fixture.transfer_faces_at(point);
            let even = as_even.transfer_faces_at(point);
            let odd = as_odd.transfer_faces_at(point);
            faces_carry &= even.absorptive.is_zero()
                && odd.dispersive.is_zero()
                && whole.dispersive == even.dispersive
                && whole.absorptive == odd.absorptive;
            if !whole.dispersive.is_zero() {
                nonzero_dispersive += 1;
            }
            if !whole.absorptive.is_zero() {
                nonzero_absorptive += 1;
            }
            if point == &probe_points[1] {
                println!(
                    "  {:<30} {:<18} {:>16} {:>16}",
                    name,
                    render_point(point),
                    format_rat(&whole.dispersive),
                    format_rat(&whole.absorptive)
                );
            }
        }
    }
    println!(
        "\n  over {} fixture-point readings: Re chi nonzero {nonzero_dispersive} times, Im chi {nonzero_absorptive} times",
        every_fixture().len() * probe_points.len()
    );
    holds.push((
        "the even face carries Re chi and nothing else, the odd face Im chi and nothing else",
        faces_carry && nonzero_dispersive > 0 && nonzero_absorptive > 0,
        format!(
            "{} readings, {nonzero_dispersive} nonzero Re, {nonzero_absorptive} nonzero Im",
            every_fixture().len() * probe_points.len()
        ),
    ));

    println!("\n  THE CONTROL THAT MUST NOT DISTINGUISH. Crossing symmetry `chi(conj z) = conj");
    println!("  chi(z)` follows from the response being REAL and holds for acausal responses too,");
    println!("  so it is strictly weaker than causality and must not be mistaken for it:");
    let mut crossing_holds = true;
    let mut crossing_distinguishing = 0usize;
    for (_, fixture, _, _) in every_fixture() {
        for point in &probe_points {
            let forward = fixture.transfer_faces_at(point);
            let conjugated = fixture.transfer_faces_at(&point.conjugate());
            crossing_holds &= forward.dispersive == conjugated.dispersive
                && forward.absorptive == -conjugated.absorptive.clone();
            if forward.absorptive != conjugated.absorptive {
                crossing_distinguishing += 1;
            }
        }
    }
    println!(
        "    crossing symmetry held on every reading including the acausal ones: {crossing_holds}"
    );
    println!(
        "    and the conjugate point genuinely differed {crossing_distinguishing} times, so the"
    );
    println!("    symmetry was tested on something rather than on a real-axis degeneracy");
    holds.push((
        "crossing symmetry holds for acausal responses too, so it cannot be read as causality",
        crossing_holds && crossing_distinguishing > 0,
        format!("{crossing_distinguishing} readings where the conjugate point moved Im chi"),
    ));

    // ===========================================================================================
    println!("\n\n9. THE FOUR-POINT SPECTRAL RELATION, AND WHAT IT COSTS TO LEAVE ITS APERTURE");
    println!("----------------------------------------------------------------------------");
    println!(
        "  At N = 4 the circular Hilbert kernel `(2/N)cot(pi m/N)` is `[0, 1/2, 0, -1/2]` and"
    );
    println!("  the relation collapses to a three-point stencil:");
    println!("      Im chi[k] =  ( Re chi[k+1] - Re chi[k-1] ) / 2");
    println!("      Re chi[k] = -( Im chi[k+1] - Im chi[k-1] ) / 2  +  h_e[0]  +  h_e[2] (-1)^k");
    println!("  The second line is SUBTRACTED, and its two constants are exactly the two fixed");
    println!("  points of `n -> -n` on Z/4.");
    let inside = response(2, &[(0, 1), (0, 1), (5, 2), (-3, 1), (7, 4)]);
    let spectral = inside.four_point_spectral_reflection();
    println!(
        "\n  h = {}   causal {}   inside the declared aperture {}",
        render_values(inside.values()),
        inside.is_causal(),
        inside.within_four_point_aperture()
    );
    println!("    fold[j]              {}", render_four(&spectral.folded));
    println!(
        "    Re chi  (measured)   {}",
        render_four(&spectral.dispersive)
    );
    println!(
        "    Re chi  (derived)    {}",
        render_four(&spectral.derived_dispersive)
    );
    println!(
        "    Im chi  (measured)   {}",
        render_four(&spectral.absorptive)
    );
    println!(
        "    Im chi  (derived)    {}",
        render_four(&spectral.derived_absorptive)
    );
    println!(
        "    residuals            {}   /   {}",
        render_four(&spectral.dispersive_residual),
        render_four(&spectral.absorptive_residual)
    );
    println!(
        "    subtraction constants (h_e[0], h_e[2]) = ({}, {})   folded_advanced = {}   locks {}",
        format_rat(&spectral.subtraction_constants[0]),
        format_rat(&spectral.subtraction_constants[1]),
        format_rat(&spectral.folded_advanced),
        spectral.locks()
    );
    let unsubtracted: [Rat; 4] = std::array::from_fn(|k| {
        (spectral.absorptive[(k + 3) % 4].clone() - &spectral.absorptive[(k + 1) % 4]) / integer(2)
    });
    println!(
        "    the UNSUBTRACTED stencil would return {}",
        render_four(&unsubtracted)
    );
    println!("    which is not Re chi — the constants are load-bearing and both are nonzero here.");
    holds.push((
        "the four-point relation is exact both ways inside its aperture, and needs its two constants",
        spectral.locks()
            && !spectral.is_vacuous()
            && spectral.subtraction_constants.iter().all(|constant| !constant.is_zero())
            && unsubtracted != spectral.dispersive,
        "both residual arrays identically zero; the unsubtracted stencil does not reproduce Re chi"
            .to_owned(),
    ));

    println!("\n  And it fails on a folded-acausal response with residual exactly +-2 fold[3]:");
    let mut leak_residuals_exact = true;
    println!(
        "\n    {:<12} {:>44} {:>44}",
        "fold[3]", "dispersive residual", "absorptive residual"
    );
    for (numerator, denominator) in [(1, 1), (-2, 3), (9, 5)] {
        let value = rat(numerator, denominator);
        let fixture = CausalResponse::new(
            2,
            grain(),
            vec![
                Rat::zero(),
                value.clone(),
                rat(5, 2),
                integer(-3),
                rat(7, 4),
            ],
        )
        .expect("a lawful declaration");
        let reading = fixture.four_point_spectral_reflection();
        let doubled = integer(2) * &value;
        leak_residuals_exact &= reading.folded_advanced == value
            && !reading.locks()
            && reading.absorptive_residual
                == [Rat::zero(), doubled.clone(), Rat::zero(), -doubled.clone()]
            && reading.dispersive_residual
                == [doubled.clone(), Rat::zero(), -doubled.clone(), Rat::zero()]
            && !doubled.is_zero();
        println!(
            "    {:<12} {:>44} {:>44}",
            format_rat(&value),
            render_four(&reading.dispersive_residual),
            render_four(&reading.absorptive_residual)
        );
    }
    holds.push((
        "an occupied folded arc returns residuals of exactly +-2 fold[3] at the frequencies the stencil reaches",
        leak_residuals_exact,
        "three declared leaks, all exact".to_owned(),
    ));

    println!("\n  THE APERTURE IS MEASURED, NOT ASSERTED. Conducted past it the organ APPEARS TO");
    println!(
        "  RETURN: a single nonzero value at `n = -2` folds onto the causal arc's slot 2, and"
    );
    println!("  every spectral residual is zero on material that is not causal.");
    let outside = response(2, &[(6, 1), (0, 1), (5, 2), (-3, 1), (7, 4)]);
    let outside_spectral = outside.four_point_spectral_reflection();
    let outside_lock = causality_lock(&outside).expect("a lawful lock");
    println!(
        "\n    h = {}   causal {}   within_four_point_aperture {}",
        render_values(outside.values()),
        outside.is_causal(),
        outside.within_four_point_aperture()
    );
    println!(
        "    fold[j] = {}   folded_advanced = {}",
        render_four(&outside_spectral.folded),
        format_rat(&outside_spectral.folded_advanced)
    );
    println!(
        "    the SPECTRAL organ locks   : {}   <- it is answering a different question",
        outside_spectral.locks()
    );
    println!(
        "    the RESPONSE-domain law    : {}   advanced support {:?}   residual at -2 = {}",
        outside_lock.locks(),
        outside_lock.advanced_support,
        format_rat(&outside_lock.dispersive_to_absorptive.residual_at(-2))
    );
    println!("    The response-domain reading has no aperture limit and refuses it. This is why");
    println!("    `within_four_point_aperture` is a checkable predicate and not a comment.");
    holds.push((
        "past its aperture the spectral organ returns a passing result on acausal material, and the response-domain law still refuses",
        outside_spectral.locks()
            && !outside.is_causal()
            && !outside.within_four_point_aperture()
            && !outside_spectral.is_vacuous()
            && !outside_lock.locks()
            && outside_lock.advanced_support == vec![-2]
            && outside_lock.dispersive_to_absorptive.residual_at(-2) == integer(6),
        "the aliasing violation is exhibited rather than asserted".to_owned(),
    ));

    println!("\n  The spectral biconditional, decided by exhaustion INSIDE the aperture: every");
    println!("  declaration supported on `n` in `[-1, 2]` over the alphabet {{-1, 0, 3}}.");
    let alphabet = [integer(-1), Rat::zero(), integer(3)];
    let mut empty = 0usize;
    let mut occupied = 0usize;
    let mut spectral_law_holds = true;
    for code in 0..alphabet.len().pow(4) {
        let mut remaining = code;
        let values: Vec<Rat> = (0..4)
            .map(|_| {
                let digit = remaining % alphabet.len();
                remaining /= alphabet.len();
                alphabet[digit].clone()
            })
            .collect();
        let fixture = CausalResponse::new(
            2,
            grain(),
            vec![
                Rat::zero(),
                values[0].clone(),
                values[1].clone(),
                values[2].clone(),
                values[3].clone(),
            ],
        )
        .expect("a lawful declaration");
        let reading = fixture.four_point_spectral_reflection();
        spectral_law_holds &= reading.locks() == reading.folded_advanced.is_zero()
            && reading.locks() == fixture.is_causal();
        if reading.folded_advanced.is_zero() {
            empty += 1;
        } else {
            occupied += 1;
        }
    }
    println!(
        "    {} declarations: {empty} with an empty folded arc, {occupied} with an occupied one,",
        empty + occupied
    );
    println!("    and inside the aperture the folded reading IS the response's own reading.");
    holds.push((
        "the spectral lock equals the emptiness of the folded arc, and inside the aperture equals causality",
        spectral_law_holds && empty == 27 && occupied == 54,
        format!("{empty} empty / {occupied} occupied over 81 declarations"),
    ));

    // ===========================================================================================
    println!("\n\n10. TWO INDEPENDENT ROUTES TO ONE SPECTRUM, AND WHAT EACH COSTS");
    println!("---------------------------------------------------------------");
    println!("  `CLAUDE.md` §8: where an independent implementation exists, state both costs.");
    println!("    fold then transform  O(M) exact rational ADDITIONS and no multiplication at all");
    println!("    direct evaluation    O(M) Gaussian-rational MULTIPLICATIONS, four Rat products");
    println!("                         each — strictly the dearer, by the multiplication");
    println!("  The two must agree bitwise on all four frequencies of every fixture.");
    let gaussian = [
        RationalCirclePoint::new(integer(1), Rat::zero()).expect("on the circle"),
        RationalCirclePoint::new(Rat::zero(), integer(1)).expect("on the circle"),
        RationalCirclePoint::new(integer(-1), Rat::zero()).expect("on the circle"),
        RationalCirclePoint::new(Rat::zero(), integer(-1)).expect("on the circle"),
    ];
    let mut routes_agree = true;
    let mut compared = 0usize;
    for (_, fixture, _, _) in every_fixture() {
        let reading = fixture.four_point_spectral_reflection();
        for (k, point) in gaussian.iter().enumerate() {
            let direct = fixture.transfer_faces_at(point);
            routes_agree &= direct.dispersive == reading.dispersive[k]
                && direct.absorptive == reading.absorptive[k];
            compared += 1;
        }
    }
    println!("\n  {compared} comparisons, agreement {routes_agree}");
    let tail_spectrum = causal_tail().four_point_spectral_reflection();
    println!(
        "  and the comparison is run on material where both routes return something: {}",
        !tail_spectrum.is_vacuous()
    );
    holds.push((
        "the fold and the direct Gaussian evaluation are bit-identical on every fixture and frequency",
        routes_agree && !tail_spectrum.is_vacuous(),
        format!("{compared} comparisons"),
    ));

    println!("\n  THE GRAIN IS A RECEIVER GAUGE. It appears in every carrier — two faces on");
    println!("  different grains cannot be compared at all — and it must move NOTHING in the law.");
    println!("  Both halves are measured, because an invariance whose gauge does not act on the");
    println!("  carrier is not an invariance:");
    let mut grain_moves_nothing = true;
    for (_, fixture, _, _) in every_fixture() {
        let reference = causality_lock(&fixture).expect("a lawful lock");
        for (numerator, denominator) in [(1, 1), (7, 2), (1, 1000), (99, 7)] {
            let regrained = CausalResponse::new(
                fixture.half_extent(),
                rat(numerator, denominator),
                fixture.values().to_vec(),
            )
            .expect("a lawful declaration");
            let lock = causality_lock(&regrained).expect("a lawful lock");
            grain_moves_nothing &= lock.locks() == reference.locks()
                && lock.dispersive_to_absorptive.standing_residuals()
                    == reference.dispersive_to_absorptive.standing_residuals()
                && lock.subtraction_constants == reference.subtraction_constants;
        }
    }
    let regrained = CausalResponse::new(
        causal_tail().half_extent(),
        integer(5),
        causal_tail().values().to_vec(),
    )
    .expect("lawful");
    let across_grains = causal_tail()
        .dispersive_face()
        .reflect_and_compare(&regrained.absorptive_face());
    println!(
        "    the gauge ACTS on the carrier: comparing across grains returns {across_grains:?}"
    );
    println!(
        "    and it moves nothing in the law over 6 fixtures x 4 grains: {grain_moves_nothing}"
    );
    holds.push((
        "the grain acts on the carrier and moves no lock, no residual and no subtraction constant",
        grain_moves_nothing && matches!(across_grains, Err(CausalReflectionError::LatticesDiffer)),
        "24 regrained readings, all bit-identical; cross-grain comparison refused".to_owned(),
    ));

    // ===========================================================================================
    println!("\n\n11. HOLOMORPHY, DECIDED BY INSPECTING COEFFICIENTS");
    println!("--------------------------------------------------");
    println!("  `chi(z) = sum_n h[n] z^-n` is a Laurent polynomial. A nonzero pre-stimulus value");
    println!("  `h[-m]` is the coefficient of `z^+m`, a pole at infinity. So a response is causal");
    println!("  exactly when its transfer function has no advanced part, exactly when it extends");
    println!(
        "  holomorphically over the exterior chart including infinity, where its value is the"
    );
    println!("  instantaneous response. No half-plane, no contour, no limit.");
    println!(
        "\n  {:<30} {:>10} {:>12} {:>18} {:>28}",
        "fixture", "causal", "pole order", "chi(infinity)", "advanced coefficients"
    );
    let mut holomorphy_agrees = true;
    for (name, fixture, _, _) in every_fixture() {
        let witness = fixture.holomorphy_witness();
        holomorphy_agrees &= witness.extends_over_infinity() == fixture.is_causal()
            && (fixture.is_causal()) == (witness.pole_order_at_infinity() == 0);
        println!(
            "  {:<30} {:>10} {:>12} {:>18} {:>28}",
            name,
            fixture.is_causal(),
            witness.pole_order_at_infinity(),
            format_rat(&witness.value_at_infinity),
            format!(
                "{:?}",
                witness
                    .advanced_coefficients
                    .iter()
                    .map(|(power, coefficient)| format!("z^{power}: {}", format_rat(coefficient)))
                    .collect::<Vec<_>>()
            )
        );
    }
    holds.push((
        "holomorphy over infinity and structural causality agree on every fixture, both ways",
        holomorphy_agrees,
        format!("{} fixtures, both classes populated", every_fixture().len()),
    ));

    // ===========================================================================================
    println!("\n\n12. REFUSALS — WHAT THE ORGAN WILL NOT DECLARE");
    println!("----------------------------------------------");
    let mut refusals: Vec<(&str, String, bool)> = Vec::new();

    let extent_zero = CausalResponse::new(0, grain(), vec![integer(1)]);
    refusals.push((
        "a lattice with no pre-stimulus region",
        format!("{:?}", extent_zero.as_ref().err()),
        matches!(
            extent_zero.as_ref().err(),
            Some(CausalReflectionError::LatticeExtentZero)
        ),
    ));

    let zero_step = CausalResponse::new(1, Rat::zero(), vec![integer(1); 3]);
    refusals.push((
        "a lattice grain of zero",
        format!("{:?}", zero_step.as_ref().err()),
        matches!(
            zero_step.as_ref().err(),
            Some(CausalReflectionError::SampleStepNotPositive)
        ),
    ));

    let width = CausalResponse::new(2, grain(), vec![integer(1); 4]);
    refusals.push((
        "four values on a five-point lattice",
        format!("{:?}", width.as_ref().err()),
        matches!(
            width.as_ref().err(),
            Some(CausalReflectionError::LatticeWidthMismatch {
                half_extent: 2,
                declared: 5,
                supplied: 4
            })
        ),
    ));

    // f[-1] = 1, f[0] = 0, f[1] = 2: as an even face the violation at index 1 is 2 - 1 = 1; as an
    // odd face it is 2 - (-1) = 3. The refusal carries the exact violation, not a flag.
    let lopsided = vec![integer(1), Rat::zero(), integer(2)];
    let even_violation =
        ExactResponseFace::new(FaceParity::Dispersive, 1, grain(), lopsided.clone());
    refusals.push((
        "a declared even face that is not even, with the exact violation",
        format!("{:?}", even_violation.as_ref().err()),
        matches!(
            even_violation.as_ref().err(),
            Some(CausalReflectionError::FaceParityViolated { index: 1, violation, .. })
                if **violation == integer(1)
        ),
    ));
    let odd_violation = ExactResponseFace::new(FaceParity::Absorptive, 1, grain(), lopsided);
    refusals.push((
        "the same values declared odd, whose violation is a different exact number",
        format!("{:?}", odd_violation.as_ref().err()),
        matches!(
            odd_violation.as_ref().err(),
            Some(CausalReflectionError::FaceParityViolated { index: 1, violation, .. })
                if **violation == integer(3)
        ),
    ));

    let fixed_point_violation = ExactResponseFace::new(
        FaceParity::Absorptive,
        1,
        grain(),
        vec![integer(-3), integer(5), integer(3)],
    );
    refusals.push((
        "an odd face with a nonzero value at the fixed point, despite a perfect mirror symmetry",
        format!("{:?}", fixed_point_violation.as_ref().err()),
        matches!(
            fixed_point_violation.as_ref().err(),
            Some(CausalReflectionError::FaceParityViolated { index: 0, .. })
        ),
    ));

    let parity_mismatch = causal_tail()
        .dispersive_face()
        .reflect_and_compare(&causal_tail().dispersive_face());
    refusals.push((
        "a derived odd face compared against an even one",
        format!("{:?}", parity_mismatch.as_ref().err()),
        matches!(
            parity_mismatch.as_ref().err(),
            Some(CausalReflectionError::FaceParityMismatch {
                expected: FaceParity::Absorptive,
                supplied: FaceParity::Dispersive
            })
        ),
    ));

    let lattices = causal_tail()
        .dispersive_face()
        .reflect_and_compare(&response(1, &[(0, 1), (3, 1), (-7, 2)]).absorptive_face());
    refusals.push((
        "two faces on different lattices, whose residual would mean nothing",
        format!("{:?}", lattices.as_ref().err()),
        matches!(
            lattices.as_ref().err(),
            Some(CausalReflectionError::LatticesDiffer)
        ),
    ));

    let off_circle = RationalCirclePoint::new(rat(1, 2), rat(1, 2));
    refusals.push((
        "a spectral point that misses the unit circle, carrying the exact miss",
        format!("{:?}", off_circle.as_ref().err()),
        matches!(
            off_circle.as_ref().err(),
            Some(CausalReflectionError::NotOnTheUnitCircle { deviation })
                if **deviation == rat(-1, 2)
        ),
    ));

    let short_retarded =
        CausalResponse::from_retarded_values(2, grain(), &[integer(1), integer(1)]);
    refusals.push((
        "a retarded declaration of the wrong width",
        format!("{:?}", short_retarded.as_ref().err()),
        matches!(
            short_retarded.as_ref().err(),
            Some(CausalReflectionError::LatticeWidthMismatch { .. })
        ),
    ));

    for (what, rendered, _) in &refusals {
        println!("  {:<74} {rendered}", format!("{what}:"));
    }
    holds.push((
        "every refusal fires by name, and the parity refusals carry the exact violation",
        refusals.iter().all(|(_, _, fired)| *fired),
        format!(
            "{} of {} refusals returned the declared variant",
            refusals.iter().filter(|(_, _, fired)| *fired).count(),
            refusals.len()
        ),
    ));

    // ===========================================================================================
    println!("\n\nBOUNDS");
    println!("------");
    println!("  - This is NOT the continuum Kramers-Kronig relation. No integral is evaluated, no");
    println!("    limit is taken, no refinement is scheduled, and no convergence of the lattice");
    println!("    statement to the continuum one is claimed or tested. The lattice statement is a");
    println!("    finite biconditional between a support condition and a pointwise sign identity,");
    println!("    and that is its whole content.");
    println!("  - It says nothing about a susceptibility. `chi` here is a Laurent polynomial with");
    println!("    exact rational coefficients. There is no resonance, no pole off the origin, no");
    println!("    line shape, no Lorentzian, and no analytic continuation.");
    println!("  - The spectral relation at N > 4 is not implemented and is not implementable in");
    println!(
        "    this carrier. Section 7 measures WHY over a declared finite family of 136 slopes"
    );
    println!("    and a horizon of 24; it does not prove Niven's theorem, which is cited. A body");
    println!("    wanting N > 4 must declare the real cyclotomic field Q(zeta_N)+, which neither");
    println!("    this module nor `exact_value.rs`'s Sturm-certified `AlgebraicRoot` supplies —");
    println!("    an enclosure of an algebraic number is not arithmetic in a number field.");
    println!(
        "  - NO RECEIVER IS MEASURED. The record's open conjecture asks whether the continuing"
    );
    println!("    body's own declared response is causal in the required sense. Nothing here");
    println!("    answers that; this module is the apparatus that would, and this driver runs the");
    println!("    apparatus on declared fixtures.");
    println!("  - The exhaustive sweeps are 27 + 1,024 + 2,187 declarations at half-extents 1, 2");
    println!("    and 3 over three small alphabets. The biconditional is decided on exactly that");
    println!("    material and nothing is established for larger lattices or richer value sets.");
    println!("  - The four-point organ tests the FOLDED response. Section 9 exhibits a response");
    println!("    outside the aperture on which it locks while the response is not causal; that");
    println!("    exhibit is one witness, not a characterization of the aliasing set.");

    // ===========================================================================================
    println!("\n\nDECLARED CONTROLS");
    println!("-----------------");
    let mut failed = 0;
    for (claim, verdict, evidence) in &holds {
        if *verdict {
            println!("  [holds] {claim}\n            {evidence}");
        } else {
            failed += 1;
            println!("  [FAILS] {claim}\n            {evidence}");
        }
    }
    println!();
    if failed == 0 {
        println!("HELD -- {} declared controls, 0 failed", holds.len());
    } else {
        println!(
            "FAILED -- {failed} of {} declared controls did not hold",
            holds.len()
        );
        std::process::exit(1);
    }
}

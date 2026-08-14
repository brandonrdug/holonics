//! **The whip, made computable: an adiabatic taper is a chain of zero-remainder rebases.**
//!
//! Organs: `analytic_field::{exact_stratified_stack, exact_scalar_interface_coefficients}`, and
//! `dimensional_wave::ExactWavePhaseTransport` as the phase carrier. Nothing new is built here.
//!
//! # The claim under test
//!
//! `CLAUDE.md` section 0j states it as a theorem rather than an image:
//!
//! > `Gamma = (Z2 - Z1)/(Z2 + Z1)` is Fresnel at normal incidence, the transmission-line
//! > reflection, and the Smith chart — one law. A whip's taper is **adiabatic**, so the
//! > infinitesimal reflections cancel and every link transmits whole: each link is a rebase with
//! > zero remainder and the crack is the composed ratio. **An abrupt step is a compression, and the
//! > reflected wave is its remainder.**
//!
//! That is falsifiable and this driver falsifies it. Two stacks with **the same endpoints** and the
//! same total phase:
//!
//! ```text
//!   TAPER    Y = 1, 2, 3, ..., N+1        N boundaries, each reflecting -1/(2k+1)
//!   STEP     Y = 1, N+1                   ONE boundary, reflecting -N/(N+2)
//! ```
//!
//! The composed reflection is the coherent sum `sum_j r_j * (phase_at_j)^2` — each boundary's
//! reflection returns through everything it came through, so it re-emerges carrying the round
//! trip. Every term is rational, so `|Gamma|^2` is one exact rational and no float appears.
//!
//! **What would refute the claim:** the taper's composed reflection failing to fall as it is
//! subdivided, or failing to sit below the abrupt step's. Either would mean the gear-ratio reading
//! has no instance in this machine and section 0j overstates it.
//!
//! **The second control is the one that matters**, because it says *why*: run the same taper with
//! the phase set to identity. Without a rotating phase the boundary reflections cannot destructively
//! interfere, so the composed reflection must be **larger**. If it is not, the cancellation is not
//! phase-driven and the adiabatic reading is describing something else.
//!
//! # What this may not be reported as
//!
//! `composed_reflection` is **first order**: it sums each boundary once and does not re-reflect
//! between boundaries. For small steps that is the regime the adiabatic claim lives in; it is not
//! the exact scattering solution, and `dimensional_wave::enact_wave` is the owner that resolves
//! multiple reflections by conducting them. No mechanical whip is modelled here — no taper profile,
//! no tension, no moving boundary — only the impedance chain the whip and the stack share.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_taper_transmits_and_the_step_reflects
//! ```

use holonic_engine::analytic_field::{
    ExactRefractionHand, ExactStratifiedLayer, exact_stratified_stack,
};
use holonic_engine::dimensional_wave::ExactWavePhaseTransport;
use relational_geometry::{Rat, RatVec3};

/// The 3-4-5 rational rotation. A point of the exact unit conic that is not the identity, so the
/// round trip genuinely turns and successive boundaries can cancel.
fn turning() -> ExactWavePhaseTransport {
    ExactWavePhaseTransport::new(Rat::new(3.into(), 5.into()), Rat::new(4.into(), 5.into()))
        .expect("3/5, 4/5 is on the unit conic")
}

fn integer(value: i64) -> Rat {
    Rat::from_integer(value.into())
}

/// Every layer carries the same wave number, so no boundary turns and the whole chain is traversed.
/// The impedance is what varies, which is the object under test.
///
/// The incident covector is taken along the normal below, so the conserved tangential square is
/// **zero** and every boundary propagates. An earlier version of this driver set the wave number
/// equal to the tangential square and every boundary GRAZED — returning an open fiber that
/// contributes nothing — so every figure came back zero and the run reported REFUTED. The reading
/// was right and the fixture was wrong; normal incidence is also the frame in which
/// `(Y_i - Y_t)/(Y_i + Y_t)` is exactly the Fresnel coefficient the whip shares.
fn layer(admittance: Rat, phase_transport: ExactWavePhaseTransport) -> ExactStratifiedLayer {
    ExactStratifiedLayer {
        wave_number_square: integer(25),
        admittance,
        phase_transport,
    }
}

/// The endpoints, held FIXED while the subdivision varies.
const FROM: i64 = 1;
const TO: i64 = 33;

/// `Y` from [`FROM`] to [`TO`] in `steps` equal rational increments — a genuine **subdivision** of
/// one taper.
///
/// An earlier version ran `Y = 1, 2, ..., steps + 1`, which moves the far endpoint with the step
/// count: that lengthens the taper rather than subdividing it, and the monotonicity question is
/// then being asked of a different taper at every row. The comparison against the abrupt step was
/// still fair, because it used each taper's own endpoints; the comparison *across rows* was not.
fn taper(steps: i64, phase_transport: ExactWavePhaseTransport) -> Vec<ExactStratifiedLayer> {
    (0..=steps)
        .map(|at| {
            let admittance = Rat::from_integer(FROM.into())
                + Rat::new((TO - FROM).into(), steps.into()) * Rat::from_integer(at.into());
            layer(admittance, phase_transport.clone())
        })
        .collect()
}

/// The same endpoints in one boundary.
fn abrupt(phase_transport: ExactWavePhaseTransport) -> Vec<ExactStratifiedLayer> {
    vec![
        layer(integer(FROM), phase_transport.clone()),
        layer(integer(TO), phase_transport),
    ]
}

fn read(layers: &[ExactStratifiedLayer]) -> Rat {
    exact_stratified_stack(
        RatVec3::from_i64(0, 0, 5),
        RatVec3::from_i64(0, 0, 1),
        layers,
        ExactRefractionHand::AlongNormal,
    )
    .expect("the incident covector is on its own shell and every layer propagates")
    .composed_reflection_square()
}

fn main() {
    println!("{}", "=".repeat(96));
    println!("THE TAPER TRANSMITS AND THE STEP REFLECTS");
    println!("{}", "=".repeat(96));
    println!(
        "\n  |Gamma|^2, composed coherently over the boundaries each stack reached.\n  \
         Exact rationals throughout; no float appears anywhere in this run."
    );

    println!("\n{}", "-".repeat(96));
    println!("SUBDIVIDING ONE TAPER — endpoints held at Y = {FROM} to Y = {TO}, boundaries vary");
    println!("{}", "-".repeat(96));
    println!(
        "  {:>6} {:>26} {:>26} {:>12}",
        "steps", "taper |Gamma|^2", "abrupt |Gamma|^2", "taper<abrupt"
    );

    let mut previous: Option<Rat> = None;
    let mut monotone = true;
    let mut always_below = true;
    for steps in [1i64, 2, 4, 8, 16, 32] {
        let tapered = read(&taper(steps, turning()));
        let stepped = read(&abrupt(turning()));
        let below = tapered < stepped;
        always_below &= below || steps == 1;
        if let Some(held) = &previous {
            // Past the first subdivision the taper's composed reflection must not rise.
            monotone &= tapered <= *held;
        }
        println!(
            "  {steps:>6} {:>26} {:>26} {:>12}",
            format!("{tapered}"),
            format!("{stepped}"),
            if below { "yes" } else { "NO" }
        );
        previous = Some(tapered);
    }

    println!(
        "\n  the taper's composed reflection is monotone non-increasing under subdivision: {}",
        if monotone {
            "YES"
        } else {
            "NO — the adiabatic reading is refuted on this material"
        }
    );
    println!(
        "  and sits strictly below the abrupt step of the same endpoints: {}",
        if always_below {
            "YES"
        } else {
            "NO — the adiabatic reading is refuted on this material"
        }
    );

    println!("\n{}", "-".repeat(96));
    println!("THE CONTROL — the same taper with NO phase, so nothing can cancel");
    println!("{}", "-".repeat(96));
    println!(
        "  {:>6} {:>26} {:>26} {:>14}",
        "steps", "turning |Gamma|^2", "identity |Gamma|^2", "phase cancels"
    );
    let mut phase_does_work = true;
    for steps in [2i64, 4, 8, 16, 32] {
        let turned = read(&taper(steps, turning()));
        let flat = read(&taper(steps, ExactWavePhaseTransport::identity()));
        let cancels = turned < flat;
        phase_does_work &= cancels;
        println!(
            "  {steps:>6} {:>26} {:>26} {:>14}",
            format!("{turned}"),
            format!("{flat}"),
            if cancels { "yes" } else { "NO" }
        );
    }
    println!(
        "\n  the cancellation is PHASE-DRIVEN: {}",
        if phase_does_work {
            "YES — without a rotating phase the same taper reflects more"
        } else {
            "NO — the cancellation is not phase-driven and the reading describes something else"
        }
    );

    println!("\n{}", "-".repeat(96));
    println!("WHAT THIS RUN DOES NOT ESTABLISH");
    println!("{}", "-".repeat(96));
    println!("  The composed reflection is FIRST ORDER: each boundary is summed once and nothing");
    println!("  re-reflects between boundaries. For small steps that is the regime the adiabatic");
    println!("  claim lives in; it is not the exact scattering solution, and enact_wave is the");
    println!("  owner that resolves multiple reflections by conducting them.");
    println!("  No taper profile, no tension, and no moving boundary is modelled — only the");
    println!("  impedance chain a whip and a stratified stack share.");

    let verdict = monotone && always_below && phase_does_work;
    println!("\n{}", "=".repeat(96));
    println!(
        "{}",
        if verdict {
            "HELD -- the taper transmits, the step reflects, and the phase is what cancels"
        } else {
            "REFUTED -- section 0j's adiabatic reading has no instance on this material"
        }
    );
    println!("{}", "=".repeat(96));
    if !verdict {
        std::process::exit(1);
    }
}

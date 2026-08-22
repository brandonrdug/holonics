//! **Two determination laws in one chain, and the coordinate that separates them is invisible to
//! the quantity the chain was carrying.**
//!
//! ```text
//! cargo run --release --example the_committed_step_is_a_link_and_the_winding_cannot_see_it
//! ```
//!
//! **Station four of
//! [`blueprint/THE_WORK_VECTOR_THE_HANDS_POLARITY_AND_THE_COMMITTED_STEP.md`](../../../blueprint/THE_WORK_VECTOR_THE_HANDS_POLARITY_AND_THE_COMMITTED_STEP.md).**
//!
//! ## What was already standing, and what was not
//!
//! `leader_quadrature::integrate_by_leaders` has composed two genuinely different determination laws
//! since it was written:
//!
//! ```text
//!   FOUND   the material is re-read at this tip; the span is one grain      a closed loop
//!   RIDE    licensed ONLY by a run of exact agreement, then one jet         ballistic, open loop
//!           extrapolated across the whole reach with no landing check
//! ```
//!
//! and the residual at the next tip revokes the licence and refounds the axis. **They lived inside
//! one integrator and nothing could compose them.** Measured 2026-08-17 by
//! `grep -rn "impl Relating for" --include='*.rs' crates soma` → **3**, and neither was among them.
//!
//! `CommittedStep` is that lift. The question it makes askable is the one no existing chain in this
//! tree could ask: **what separates going through from going straight, when some of the steps were
//! committed ballistically?**
//!
//! ## The surface
//!
//! Serial path, declared. The deed is one exact rational growth over a piecewise material of a few
//! germs — there is no front to distribute, and this run's whole cost is microseconds. `CLAUDE.md`'s
//! diagnosis rule applies in the other direction too: no card activity on material this small is an
//! aperture statement, not a surface defect.

use holonic_engine::leader_quadrature::{
    CommittedTransport, LeaderLaw, LeaderQuadrature, LocalJet, MaterialBoundary, RationalGerm,
    RideDiscipline, WitnessDepth, chain_of, integrate_by_leaders,
};
use holonic_structure::{Composes, Hand, Relating};
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;

fn rational(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn whole(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

/// The declared material: three germs whose jets do not align at their seams, so the founded axis
/// genuinely fails to predict across them and the growth must refound.
fn declared_material() -> MaterialBoundary {
    let germ = |extent: Rat, coefficients: &[(i64, i64)]| {
        RationalGerm::new(
            extent,
            LocalJet::new(
                coefficients
                    .iter()
                    .map(|(numerator, denominator)| rational(*numerator, *denominator))
                    .collect(),
            )
            .expect("a non-empty jet"),
        )
        .expect("a germ of positive extent")
    };
    MaterialBoundary::new(vec![
        germ(whole(1), &[(1, 1), (2, 1)]),
        germ(rational(3, 2), &[(2, 1), (-1, 1)]),
        germ(rational(1, 2), &[(5, 1)]),
    ])
    .expect("a non-empty material boundary")
}

fn grow(material: &MaterialBoundary, grain: &Rat, discipline: RideDiscipline) -> LeaderQuadrature {
    integrate_by_leaders(
        material,
        &LeaderLaw::new(grain.clone(), discipline, WitnessDepth::ReadOffTheJet),
    )
    .expect("a lawful growth")
}

fn hand_name(hand: Hand) -> &'static str {
    match hand {
        Hand::Cohere => "COHERE",
        Hand::Anti => "ANTI",
        Hand::Ortho => "ORTHO",
    }
}

fn main() {
    let material = declared_material();
    let grain = rational(1, 4);

    println!("{}", "=".repeat(100));
    println!("THE COMMITTED STEP IS A LINK, AND THE WINDING CANNOT SEE IT");
    println!("{}", "=".repeat(100));
    println!();
    println!("  Two determination laws over ONE material:");
    println!();
    println!("    FOUND   the material is re-read at this tip; the span is one grain");
    println!("    RIDE    licensed only by a run of exact agreement, then one jet extrapolated");
    println!(
        "            across the whole reach WITH NO LANDING CHECK -- ballistic, and its error"
    );
    println!("            is legible only at the next tip, where the residual refounds the axis");
    println!();
    println!(
        "  declared material: 3 germs, span {}, grain {grain}",
        material.span()
    );

    let walked = grow(&material, &grain, RideDiscipline::GrainOnly);
    let ridden = grow(&material, &grain, RideDiscipline::GermBounded);

    println!();
    println!("{}", "=".repeat(100));
    println!("[1]  THE TWO GROWTHS");
    println!("{}", "=".repeat(100));
    println!();
    println!(
        "  {:<14} {:>10} {:>8} {:>7} {:>14} {:>12}",
        "discipline", "extensions", "found", "ridden", "obstructions", "area"
    );
    for (name, growth) in [("GrainOnly", &walked), ("GermBounded", &ridden)] {
        println!(
            "  {:<14} {:>10} {:>8} {:>7} {:>14} {:>12}",
            name,
            growth.extension_count(),
            growth.found_count(),
            growth.ride_count(),
            growth.obstructions.len(),
            growth.area
        );
    }
    assert!(
        ridden.ride_count() > 0,
        "nothing rode; there is one law, not two"
    );
    assert_eq!(walked.ride_count(), 0, "the control must never ride");
    println!();
    println!("  THE CONTROL IS THE FIRST ROW: a growth that never rides re-reads the material at");
    println!("  every grain, so it is the same deed with one determination law instead of two.");

    // ------------------------------------------------------------------ the composition
    println!();
    println!("{}", "=".repeat(100));
    println!("[2]  WHAT SEPARATES GOING THROUGH FROM GOING STRAIGHT");
    println!("{}", "=".repeat(100));
    println!();
    let walked_chain = chain_of(&walked);
    let ridden_chain = chain_of(&ridden);
    let straight = walked_chain.compose();
    let through = ridden_chain.compose();

    println!("  {:<24} {:>14} {:>16}", "", "winding", "uninspected");
    println!(
        "  {:<24} {:>14} {:>16}",
        "straight (never rides)", straight.winding, straight.uninspected
    );
    println!(
        "  {:<24} {:>14} {:>16}",
        "through (rides)", through.winding, through.uninspected
    );
    println!();
    println!(
        "  >> THE WINDINGS AGREE EXACTLY. That is this module's own theorem and it is why riding"
    );
    println!("  >> is lawful at all: a commitment licensed by exact agreement deposits what the");
    println!("  >> re-reading would have deposited.");
    assert_eq!(straight.winding, through.winding);
    println!();
    println!(
        "  >> AND THE COMMITTED REMAINDERS DO NOT. A chain carrying only the running sum would"
    );
    println!(
        "  >> have reported these two growths as IDENTICAL -- the difference between a closed"
    );
    println!("  >> loop and a ballistic commitment is invisible to the quantity being integrated.");
    assert!(straight.uninspected.is_zero());
    assert!(through.uninspected.is_positive());
    println!();
    let defect = ridden_chain.defect_against(&straight);
    println!(
        "  the cocycle defect, going through against going straight:  winding {}   uninspected {}",
        defect.winding, defect.uninspected
    );
    println!(
        "  closed: {}",
        <CommittedTransport as Composes>::closed(&defect)
    );
    assert!(defect.winding.is_zero());
    assert!(!defect.uninspected.is_zero());
    println!();
    println!(
        "  THE ONE COORDINATE IS THE DETERMINATION-LAW MISMATCH, and it is a transport defect"
    );
    println!("  rather than a value defect. `Chain::defect_against` returns it because the two");
    println!(
        "  species are now LINKS; before 2026-08-17 nothing in this tree could form the pair."
    );
    println!();
    println!(
        "  is_rebase   straight {}   through {}",
        walked_chain.is_rebase(),
        ridden_chain.is_rebase()
    );
    println!("  A chain that re-reads every grain is a rebase with no remainder. Riding is not.");

    // ------------------------------------------------------------------ the steps
    println!();
    println!("{}", "=".repeat(100));
    println!("[3]  THE STEPS, AND THE HAND AS THE SIGN OF THE STORED FACE");
    println!("{}", "=".repeat(100));
    println!();
    println!(
        "  `Hand::Ortho` is \"cohere-null with the cross MAXIMAL -- the founding hand\", so it"
    );
    println!("  names the step that stored NOTHING and transported everything. At an arrow the");
    println!(
        "  stored face is `aim`; at a junction it is `M21`, the half that came back; here it is"
    );
    println!("  the RESIDUAL -- what the material returned against this step's own prediction.");
    println!();
    println!(
        "  {:>5} {:>8} {:>10} {:>14} {:>14} {:>8}",
        "index", "kind", "span", "winding", "residual", "hand"
    );
    let mut committed = 0usize;
    let mut stored = 0usize;
    for step in ridden_chain.links() {
        let kind = if step.is_committed() { "RIDE" } else { "found" };
        if step.is_committed() {
            committed += 1;
        }
        if !step.residual.is_zero() {
            stored += 1;
        }
        println!(
            "  {:>5} {:>8} {:>10} {:>14} {:>14} {:>8}",
            step.index,
            kind,
            step.span,
            step.transport().winding,
            step.residual,
            hand_name(step.hand())
        );
    }
    println!();
    println!("  {committed} committed step(s); {stored} step(s) stored a residual.");
    println!();
    println!(
        "  >> EVERY COMMITTED STEP READS ORTHO: it stored nothing, which is exactly the run of"
    );
    println!(
        "  >> exact agreement that licensed it. The convention and the licence are one thing."
    );
    println!(
        "  >> AND A REFOUNDING STEP DOES NOT, so the hand is reading the material rather than"
    );
    println!("  >> being a constant wearing an enum.");
    assert!(
        ridden_chain
            .links()
            .iter()
            .filter(|step| step.is_committed())
            .all(|step| step.hand() == Hand::Ortho)
    );
    assert!(
        ridden_chain
            .links()
            .iter()
            .filter(|step| !step.residual.is_zero())
            .all(|step| step.hand() != Hand::Ortho)
    );

    println!();
    println!("{}", "=".repeat(100));
    println!("WHAT THIS RUN DOES NOT CLAIM");
    println!("{}", "=".repeat(100));
    println!();
    println!(
        "  It does not wire a prediction into a routing decision. `approach_front.rs` holds the"
    );
    println!(
        "  predicted-crossing signal and refuses to route on it in writing -- \"it reports; it"
    );
    println!(
        "  never routes. If it ever reaches a min, sort or argmax that discards a member it has"
    );
    println!(
        "  become a governor.\" Whether a predicted crossing may determine a transport without"
    );
    println!("  becoming a governor is a policy question and is not answered here.");
    println!();
    println!(
        "  The zero remainder of the straight chain is A DEFINITION and not evidence: a chain"
    );
    println!(
        "  that re-reads at every grain commits past nothing by construction. The evidence is"
    );
    println!("  the mixed chain, whose remainder is not zero and whose refoundings are named.");
    println!();
    println!("  And the offset in the bookkeeping is reported rather than smoothed: a refounding");
    println!(
        "  obstruction is attributed to the extension whose founded axis failed, which is not"
    );
    println!("  the index of the tip at which the failure was discovered. A first version of this");
    println!("  reading assumed otherwise and was refuted by its own test.");
}

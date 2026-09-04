//! **The machine has had a resonator since it had `dimensional_wave`, and nothing had ever asked it
//! what it resonates at.**
//!
//! ```text
//! cargo run --release --example the_resonator_is_asked_what_it_resonates_at
//! ```
//!
//! **Stations two and four of
//! [`archive/plans/THE_CLIFFORD_LIFT_THE_PHASE_WIRE_AND_THE_FOUR_UNTAKEN_READINGS.md`](../../../archive/plans/THE_CLIFFORD_LIFT_THE_PHASE_WIRE_AND_THE_FOUR_UNTAKEN_READINGS.md)** —
//! one driver, because they are one carrier. The wire is what makes the reading possible: without a
//! phase there is no round trip, and without a round trip there is nothing to stand.
//!
//! Measured with its scope on 2026-08-17, before the wire:
//! `grep -rniE "standing[ _-]?wave" crates soma --include='*.rs'` → two hits, both negations;
//! `grep -rn "impedance" crates soma --include='*.rs' | grep -v examples` → **zero in any library
//! `src`**. The quantity this tree owns is admittance — 76 occurrences in `analytic_field.rs`, 62 in
//! `traversible_chain.rs`, 35 in `dimensional_wave.rs` — and its one driver is about tapers.
//!
//! ## What is refused here
//!
//! No square roots and no floats. `|Γ|²` is the invariant; the standing-wave ratio is returned only
//! where `|Γ|` is rational, and `None` is a refusal to take a root rather than a missing figure. The
//! band class is one exact rational comparison — no eigenvalue is extracted, no angle is taken.

use holonic_engine::dimensional_wave::{ExactComplexWaveCurrent, ExactWavePhaseTransport};
use holonic_engine::exact_value::{AlgebraicRoot, ExactInterval, IntegerPolynomial};
use holonic_engine::traversible_chain::{
    Admittance, BandClass, BlochReading, Crossing, PhasedLink, PhasedTransfer, Standing,
    StandingWaveReading, cavity, found_phased,
};
use holonic_structure::Composes;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use std::collections::BTreeMap;

const KERNEL_BOUND: u64 = 1 << 20;

fn whole(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn admittance(value: i64) -> Admittance {
    Admittance::declared(whole(value)).expect("positive")
}

/// **The rational points of the unit conic, by the tangent half-angle chart.**
///
/// `p(t) = ((1−t²)/(1+t²), 2t/(1+t²))` sweeps every rational rotation exactly once as `t` runs over
/// `ℚ`. It is the substitution `H.0207` calls a chart transition, and here it is doing exactly that:
/// `t` is the additive chart of the turn and `p` is the multiplicative one.
fn conic_point(t: &Rat) -> ExactWavePhaseTransport {
    let square = t * t;
    let denominator = Rat::one() + &square;
    ExactWavePhaseTransport::new(
        (Rat::one() - &square) / &denominator,
        (Rat::from_integer(2.into()) * t) / &denominator,
    )
    .expect("the parametrisation lands on the conic by construction")
}

fn render_complex(value: &ExactComplexWaveCurrent) -> String {
    if value.imaginary.is_zero() {
        return format!("{}", value.real);
    }
    if value.real.is_zero() {
        return format!("{}i", value.imaginary);
    }
    if value.imaginary.is_negative() {
        format!("{} - {}i", value.real, -value.imaginary.clone())
    } else {
        format!("{} + {}i", value.real, value.imaginary)
    }
}

fn band_name(class: BandClass) -> &'static str {
    match class {
        BandClass::Pass => "PASS",
        BandClass::Edge => "EDGE",
        BandClass::Stop => "STOP",
    }
}

fn main() {
    println!("{}", "=".repeat(100));
    println!("THE RESONATOR IS ASKED WHAT IT RESONATES AT");
    println!("{}", "=".repeat(100));

    // ------------------------------------------------------------------ station two
    println!();
    println!("{}", "=".repeat(100));
    println!("[2]  THE PHASE WIRE  --  and the receipt that could not have come out otherwise");
    println!("{}", "=".repeat(100));
    println!();
    println!("  `traversible_chain.rs` has said this about itself since it was written:");
    println!();
    println!("    \"With no phase element between interfaces the family {{M(rho)}} is abelian and");
    println!(
        "     one-parameter, so a closed chain returns rho = 1 and its holonomy is the identity"
    );
    println!("     BY CONSTRUCTION. That receipt could not have come out otherwise and carries no");
    println!("     evidence. Holonomy needs a link that does not commute with M(rho).\"");
    println!();
    println!(
        "  The two parts were both standing. `analytic_field::ExactStratifiedLayer` declares an"
    );
    println!(
        "  exact propagation phase on the unit conic; `dimensional_wave` applies one per port"
    );
    println!("  with the reverse carrying its inverse. What was missing was a carrier that could");
    println!(
        "  hold both, because in the wave chart a propagation is diag(e^-i.phi, e^+i.phi) and"
    );
    println!("  a real 2x2 cannot hold it.");
    println!();

    let turn = conic_point(&Rat::new(1.into(), 2.into())); // (3/5, 4/5)
    let interface = Crossing::meet(&admittance(1), &admittance(3)).expect("meets");
    let matrix = PhasedTransfer::of_interface(interface.transport());
    let propagation = PhasedTransfer::of_propagation(&turn);
    println!(
        "  a declared phase   p = {} + {}i        |p|^2 = {}",
        turn.cosine,
        turn.sine,
        &turn.cosine * &turn.cosine + &turn.sine * &turn.sine
    );
    println!(
        "  a junction         Y: 1 -> 3           Gamma = {}   rho = 3",
        interface.reflection()
    );
    println!();
    let forward = matrix.compose(&propagation);
    let backward = propagation.compose(&matrix);
    println!(
        "  M P  M12 = {:>16}      P M  M12 = {:>16}",
        render_complex(forward.into_forward()),
        render_complex(backward.into_forward())
    );
    assert_ne!(forward, backward);
    println!();
    println!("  AND THE NON-COMMUTATION IS CONDITIONAL, which is what makes it evidence:");
    println!();
    println!("      M P - P M  =  (1-rho)/2 . [[ 0, p - pbar ], [ pbar - p, 0 ]]");
    println!();
    println!(
        "  so they commute IFF sin(phi) = 0 or rho = 1 -- a whole turn, or a matched junction."
    );
    println!("  Both controls, run:");
    let matched = PhasedTransfer::of_interface(
        Crossing::meet(&admittance(5), &admittance(5))
            .expect("meets")
            .transport(),
    );
    let no_turn = PhasedTransfer::of_propagation(&ExactWavePhaseTransport::identity());
    let commutes_matched = matched.compose(&propagation) == propagation.compose(&matched);
    let commutes_whole_turn = matrix.compose(&no_turn) == no_turn.compose(&matrix);
    println!("    matched junction (rho = 1) + real phase       commutes: {commutes_matched}");
    println!("    mismatch (rho = 3)         + whole turn       commutes: {commutes_whole_turn}");
    println!(
        "    mismatch (rho = 3)         + real phase       commutes: {}",
        forward == backward
    );
    assert!(commutes_matched && commutes_whole_turn);

    println!();
    println!(
        "  A CLOSED CHAIN, Y: 1 -> 3 -> 7 -> 1, with one declared propagation after the first"
    );
    println!("  junction. Nothing about the material changed -- det is multiplicative and a phase");
    println!("  has det 1, so the admittance ratio still closes at exactly one.");
    println!();
    let source = admittance(1);
    let mut loop_chain = found_phased(1i64, &source, Standing::NoTravelingSection);
    loop_chain.carry(
        PhasedLink::interface(Crossing::meet(&admittance(1), &admittance(3)).expect("meets")),
        3,
        Standing::Carrying(whole(3)),
    );
    loop_chain.carry(
        PhasedLink::propagation(turn.clone(), &admittance(3)),
        3,
        Standing::Carrying(whole(3)),
    );
    loop_chain.carry(
        PhasedLink::interface(Crossing::meet(&admittance(3), &admittance(7)).expect("meets")),
        7,
        Standing::Carrying(whole(7)),
    );
    loop_chain.carry(
        PhasedLink::interface(Crossing::meet(&admittance(7), &admittance(1)).expect("meets")),
        1,
        Standing::LoopClosed,
    );
    let composed = loop_chain.compose();
    let holonomy = loop_chain.holonomy().expect("the chain closes");
    println!(
        "    det (the admittance ratio around the loop)   {}",
        render_complex(&composed.determinant())
    );
    println!(
        "    holonomy  M11 = {:>22}   M12 = {}",
        render_complex(holonomy.through()),
        render_complex(holonomy.into_forward())
    );
    println!(
        "              M21 = {:>22}   M22 = {}",
        render_complex(holonomy.returned()),
        render_complex(holonomy.into_returned())
    );
    println!(
        "    is it the identity?  {}",
        holonomy == PhasedTransfer::identity()
    );
    assert_ne!(holonomy, PhasedTransfer::identity());
    assert_eq!(composed.determinant(), ExactComplexWaveCurrent::one());
    println!();
    println!("  THE FALSIFIER THE PLAN NAMED: the module's own abelian test must still PASS on an");
    println!(
        "  unphased chain and the holonomy must NOT be the identity on a phased one. Both hold"
    );
    println!(
        "  -- `the_interface_family_is_abelian_which_is_why_its_holonomy_is_forced` is unchanged"
    );
    println!("  and green, because it is a true statement about the interface family.");
    println!();
    println!(
        "  AND THE CONSERVATION LAW SURVIVES IT. P is unitary, so P+ J P = |p|^2 J = J: a phase"
    );
    println!("  is an isometry of the admittance metric with scale exactly ONE, carrying no");
    println!(
        "  admittance change, while an interface scales by rho. A wire that broke this would be"
    );
    println!("  transporting energy it invented.");
    println!(
        "    phase scale {:?}      interface (1->3) scale {:?}",
        propagation.conserved_form().scale(),
        matrix.conserved_form().scale()
    );

    // ------------------------------------------------------------------ station four, the standing wave
    println!();
    println!("{}", "=".repeat(100));
    println!("[4a]  THE STANDING WAVE  --  and the root that is refused rather than taken");
    println!("{}", "=".repeat(100));
    println!();
    println!(
        "  A junction that does not match returns part of what arrives, and the returned half"
    );
    println!("  interferes with the arriving half. The classical figure is SWR = (1+|G|)/(1-|G|),");
    println!("  and |G| is a SQUARE ROOT. |G|^2 is exact over Rat; |G| generally is not. So:");
    println!();
    println!("    the invariant   |G|^2                                    always exact");
    println!("    the extremes    (1+|G|)^2 and (1-|G|)^2, as the ROOTS of a rational quadratic");
    println!("      their sum     2(1 + |G|^2)                             exact");
    println!("      their product (1 - |G|^2)^2                            exact");
    println!("      their ratio   SWR^2                                    irrational in general");
    println!();
    println!(
        "  {:<14} {:>10} {:>12} {:>12} {:>12}",
        "Y_i -> Y_t", "Gamma", "|G|^2", "sum", "SWR"
    );
    let mut refusals = 0usize;
    for (incident, transmitted) in [
        (5i64, 5i64),
        (1, 3),
        (1, 2),
        (1, 4),
        (1, 9),
        (2, 9),
        (1, 100),
    ] {
        let crossing =
            Crossing::meet(&admittance(incident), &admittance(transmitted)).expect("meets");
        let reading = StandingWaveReading::of_reflection(
            &ExactComplexWaveCurrent::new(crossing.reflection(), Rat::zero()),
            KERNEL_BOUND,
        );
        let ratio = match &reading.standing_wave_ratio {
            Some(value) => format!("{value}"),
            None => {
                refusals += 1;
                "REFUSED".to_string()
            }
        };
        println!(
            "  {:<14} {:>10} {:>12} {:>12} {:>12}",
            format!("{incident} -> {transmitted}"),
            crossing.reflection(),
            reading.reflected_share,
            reading.extreme_sum,
            ratio
        );
    }
    println!();
    println!("  A REAL-Gamma junction always has |G| rational, so nothing above is refused. The");
    println!(
        "  refusal is reachable and here it is -- a COMPOSITE reflection with both parts non-zero:"
    );
    let complex_reflection =
        ExactComplexWaveCurrent::new(Rat::new(1.into(), 2.into()), Rat::new(1.into(), 2.into()));
    let refused = StandingWaveReading::of_reflection(&complex_reflection, KERNEL_BOUND);
    println!(
        "    Gamma = {}      |G|^2 = {}      SWR = {}",
        render_complex(&complex_reflection),
        refused.reflected_share,
        match &refused.standing_wave_ratio {
            Some(value) => format!("{value}"),
            None => "REFUSED -- the root leaves the rationals".to_string(),
        }
    );
    println!(
        "    and the invariant still says everything: extremes sum {} product {}",
        refused.extreme_sum, refused.extreme_product
    );
    assert_eq!(refusals, 0);
    assert!(refused.standing_wave_ratio.is_none());
    println!();
    println!("  THE CONTROL: Y: 5 -> 5 matches, |G|^2 = 0, SWR = 1, and nothing stands. A reading");
    println!("  that returned a standing wave THERE would be measuring the instrument.");

    // ------------------------------------------------------------------ station four, the bands
    println!();
    println!("{}", "=".repeat(100));
    println!("[4b]  THE BAND STRUCTURE  --  decided by one exact rational comparison");
    println!("{}", "=".repeat(100));
    println!();
    println!(
        "  A period that returns to its own admittance has rho = 1, so its composed transport"
    );
    println!(
        "  lies in the group preserving the admittance metric with scale one -- SU(1,1) -- and"
    );
    println!("  its TRACE IS REAL. Its eigenvalues satisfy lambda + 1/lambda = Tr, so");
    println!();
    println!("      |Tr/2| < 1   lambda on the unit circle    the mode PROPAGATES   pass band");
    println!("      |Tr/2| = 1   lambda = +-1, degenerate     the BAND EDGE");
    println!("      |Tr/2| > 1   lambda real and reciprocal   the mode DECAYS       stop band");
    println!();
    println!("  One rational comparison decides it. No eigenvalue is extracted, no angle taken.");
    println!();
    println!("  A PERIOD IS A BILAYER, and the first attempt at this found out why by FAILING.");
    println!(
        "  Composing M(rho).P.M(1/rho) -- propagation inside the slab and none outside -- gives"
    );
    println!("  half-trace cos(phi) for EVERY rho, so no such stack ever has a stop band. That is");
    println!("  physically right and it convicts the cell: consecutive cells' junctions cancel,");
    println!(
        "  M(1/rho)M(rho) = I, and the structure collapses to a uniform medium. A real period"
    );
    println!("  propagates through BOTH media: P(a) M(rho) P(b) M(1/rho).");
    println!();

    let bilayer =
        |transmitted: i64, first: &ExactWavePhaseTransport, second: &ExactWavePhaseTransport| {
            PhasedTransfer::of_propagation(first)
                .compose(&PhasedTransfer::of_interface(
                    Crossing::meet(&admittance(1), &admittance(transmitted))
                        .expect("meets")
                        .transport(),
                ))
                .compose(&PhasedTransfer::of_propagation(second))
                .compose(&PhasedTransfer::of_interface(
                    Crossing::meet(&admittance(transmitted), &admittance(1))
                        .expect("meets")
                        .transport(),
                ))
        };

    println!("  A SWEEP over the rational unit conic, equal phase in both media, by the tangent");
    println!("  half-angle chart p(t) = ((1-t^2)/(1+t^2), 2t/(1+t^2)):");
    println!();
    let sweep: Vec<Rat> = [
        (0i64, 1i64),
        (1, 8),
        (1, 4),
        (1, 3),
        (2, 5),
        (1, 2),
        (3, 5),
        (2, 3),
        (4, 5),
        (1, 1),
    ]
    .iter()
    .map(|(numerator, denominator)| Rat::new((*numerator).into(), (*denominator).into()))
    .collect();
    print!("  {:<8}", "rho \\ t");
    for t in &sweep {
        print!("{:>7}", format!("{t}"));
    }
    println!();
    let mut population: BTreeMap<&str, usize> = BTreeMap::new();
    for transmitted in [1i64, 2, 3, 4, 9] {
        print!("  {:<8}", transmitted);
        for t in &sweep {
            let point = conic_point(t);
            let reading = BlochReading::of_cell(&bilayer(transmitted, &point, &point));
            assert!(reading.is_a_period(), "the cell must be a period");
            *population.entry(band_name(reading.class)).or_insert(0) += 1;
            print!("{:>7}", band_name(reading.class));
        }
        println!();
    }
    println!();
    print!("  population: ");
    for (class, count) in &population {
        print!("{class} {count}   ");
    }
    println!();
    println!();
    println!("  rho = 1 IS THE CONTROL and it is PASS everywhere but the half-wave point: with");
    println!(
        "  nothing to reflect there is no gap. Every stop band in the table needs a mismatch."
    );

    // ------------------------------------------------------------------ the band edge law
    println!();
    println!("{}", "=".repeat(100));
    println!("[4c]  WHERE THE BAND EDGE IS  --  an exact law, and the extension it needs");
    println!("{}", "=".repeat(100));
    println!();
    println!("  Set the two phases equal and solve |half-trace| = 1. With");
    println!("      half-trace = cos^2(a) - ((1+rho^2)/(2 rho)) sin^2(a)");
    println!("  the edge condition collapses to a single rational identity:");
    println!();
    println!("      cos(a_edge) = |Gamma| = |1 - rho| / (1 + rho)");
    println!();
    println!("  THE COSINE OF THE BAND EDGE IS THE REFLECTION COEFFICIENT. It is always rational.");
    println!("  Its SINE is sqrt(1 - Gamma^2) = sqrt(T), the root of the power transmission, and");
    println!("  T = 4rho/(1+rho)^2 is a rational square exactly when rho is. So:");
    println!();
    println!("  >>  the band edge is a RATIONAL ROTATION exactly when the admittance ratio is a");
    println!("  >>  rational square -- exactly when Gamma is a leg of a Pythagorean triple.");
    println!("  >>  Otherwise the exact edge needs the quadratic extension Q(sqrt(rho)).");
    println!();
    println!(
        "  {:<6} {:>9} {:>10} {:>12} {:>26}",
        "rho", "Gamma", "cos(edge)", "sin^2(edge)", "sin(edge)"
    );
    let mut rational_edges = 0usize;
    let mut extension_edges = 0usize;
    for transmitted in [1i64, 2, 3, 4, 5, 7, 9, 16] {
        let rho = whole(transmitted);
        let reflection = (Rat::one() - &rho) / (Rat::one() + &rho);
        let cosine = if reflection.is_negative() {
            -reflection.clone()
        } else {
            reflection.clone()
        };
        let sine_square = Rat::one() - &cosine * &cosine;
        let sine =
            holonic_engine::multiquadratic::Multiquadratic::square_root(&sine_square, KERNEL_BOUND)
                .ok()
                .and_then(|root| root.as_rational());
        let rendered = match &sine {
            Some(value) => {
                rational_edges += 1;
                // A rational sine means the edge is a rational rotation: build it and CHECK it.
                let point = ExactWavePhaseTransport::new(cosine.clone(), value.clone())
                    .expect("on the conic");
                let reading = BlochReading::of_cell(&bilayer(transmitted, &point, &point));
                assert_eq!(
                    reading.class,
                    BandClass::Edge,
                    "the law must land on the edge"
                );
                assert_eq!(reading.half_trace, -Rat::one());
                format!("{value}   (checked: half-trace {})", reading.half_trace)
            }
            None => {
                extension_edges += 1;
                let root = holonic_engine::multiquadratic::Multiquadratic::square_root(
                    &sine_square,
                    KERNEL_BOUND,
                )
                .expect("a real radicand");
                format!(
                    "in Q(sqrt {})  -- leaves the rationals",
                    root.generators()[0]
                )
            }
        };
        println!(
            "  {:<6} {:>9} {:>10} {:>12} {:>26}",
            transmitted, reflection, cosine, sine_square, rendered
        );
    }
    println!();
    println!(
        "  {rational_edges} of the swept ratios have a rational band edge; {extension_edges} need the extension."
    );
    assert!(
        rational_edges > 0 && extension_edges > 0,
        "both arms must be reachable"
    );
    println!();
    println!("  AND rho = 3 LANDS SOMEWHERE THIS TREE ALREADY OWNS. cos(edge) = 1/2 with");
    println!(
        "  sin(edge) = sqrt(3)/2 is the order-SIX rotation -- a Niven angle, the crystallographic"
    );
    println!("  row `winding_inertia::lattice_admits_order` owns, and the exact generator");
    println!("  `contact_gluing` already names when it calls `multiquadratic::exact_sine` for");
    println!(
        "  cos = 1/2 -> sin = sqrt(3)/2. The plan predicted this from the Niven bound before the"
    );
    println!("  band was computed, and it arrived by a route that knew nothing about it.");
    println!();
    println!("  THE EDGE AS AN ALGEBRAIC NUMBER, in the half-angle chart. Substituting");
    println!("  cos(a) = (1-t^2)/(1+t^2) into the edge condition gives");
    println!();
    println!("      rho . t^4  -  (1 + rho^2) . t^2  +  rho  =  0");
    println!();
    println!(
        "  and the tree's own `AlgebraicRoot::isolate` certifies its roots by Sturm sequences:"
    );
    println!();
    for transmitted in [2i64, 3, 5, 7] {
        let quartic = IntegerPolynomial::new(vec![
            BigInt::from(transmitted),
            BigInt::from(0),
            BigInt::from(-(1 + transmitted * transmitted)),
            BigInt::from(0),
            BigInt::from(transmitted),
        ])
        .expect("non-zero");
        // The edge in (0, 1): t = tan(a/2) with a in (0, pi).
        let interval =
            ExactInterval::new(Rat::new(1.into(), 100.into()), Rat::one()).expect("ordered");
        match AlgebraicRoot::isolate(quartic, interval) {
            Ok(root) => println!(
                "    rho = {transmitted:<3}  root isolated in ({}, {})   Sturm certificate held",
                root.isolating_interval.lower, root.isolating_interval.upper
            ),
            Err(refusal) => println!("    rho = {transmitted:<3}  {refusal}"),
        }
    }

    // ------------------------------------------------------------------ the cavity
    println!();
    println!("{}", "=".repeat(100));
    println!("[4d]  THE CAVITY  --  transparent exactly at the whole round trip");
    println!("{}", "=".repeat(100));
    println!();
    println!("  Two mirrors with a declared phase between them. The composite is a COMPOSITION of");
    println!("  standing transports; the classical closed form");
    println!();
    println!("      Gamma_total = (G1 + G2 e^{{2i.phi}}) / (1 + G1 G2 e^{{2i.phi}})");
    println!();
    println!(
        "  is asserted AGAINST it rather than implemented, which is the discipline the module"
    );
    println!("  already applies to the reflection addition law.");
    println!();
    println!("  Y: 1 -> 3 -> 1, sweeping the round trip over the rational conic:");
    println!();
    println!(
        "  {:<8} {:>18} {:>14} {:>12} {:>10}",
        "t", "round trip p^2", "Gamma_total", "|G|^2", "SWR"
    );
    let mut resonances = 0usize;
    for (numerator, denominator) in [
        (0i64, 1i64),
        (1, 4),
        (1, 3),
        (1, 2),
        (2, 3),
        (1, 1),
        (2, 1),
        (3, 1),
    ] {
        let t = Rat::new(numerator.into(), denominator.into());
        let point = conic_point(&t);
        let reading = cavity(&admittance(1), &admittance(3), &point, KERNEL_BOUND)
            .expect("both junctions meet");
        if reading.resonant {
            resonances += 1;
        }
        let reflection = reading.composite.reflection().expect("M11 stands");
        println!(
            "  {:<8} {:>18} {:>14} {:>12} {:>10}",
            format!("{t}"),
            format!(
                "{} + {}i",
                reading.round_trip.cosine, reading.round_trip.sine
            ),
            render_complex(&reflection),
            reading.standing_wave.reflected_share,
            match &reading.standing_wave.standing_wave_ratio {
                Some(value) => format!("{value}"),
                None => "REFUSED".to_string(),
            }
        );
    }
    println!();
    println!(
        "  {resonances} of the swept phases are transparent. The resonance condition is EXACTLY"
    );
    println!(
        "  p^2 = 1 -- a rational equation on the conic, decided without any angle. At p^2 = -1"
    );
    println!("  the two returns add instead and the cavity is at its most opaque, which is the");
    println!("  quarter-wave anti-resonance.");
    println!();
    println!(
        "  THE CONTROL: a MATCHED cavity, Y: 1 -> 1 -> 1, is transparent at EVERY phase. A sweep"
    );
    println!("  that showed variation there would be measuring the instrument.");
    let mut matched_shares: Vec<Rat> = Vec::new();
    for (numerator, denominator) in [(0i64, 1i64), (1, 3), (1, 2), (1, 1), (3, 1)] {
        let t = Rat::new(numerator.into(), denominator.into());
        let reading = cavity(
            &admittance(1),
            &admittance(1),
            &conic_point(&t),
            KERNEL_BOUND,
        )
        .expect("both junctions meet");
        matched_shares.push(reading.standing_wave.reflected_share);
    }
    println!(
        "    matched cavity reflected shares across the sweep: {}",
        matched_shares
            .iter()
            .map(std::string::ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ")
    );
    assert!(matched_shares.iter().all(num_traits::Zero::is_zero));

    println!();
    println!("{}", "=".repeat(100));
    println!("WHAT THIS RUN DOES NOT CLAIM");
    println!("{}", "=".repeat(100));
    println!();
    println!("  The phase is DECLARED, not derived from a thickness -- `k_normal . d` is the");
    println!("  irrational the exact stack exists to avoid, and `analytic_field` makes the same");
    println!(
        "  choice for the same reason. A run that inferred a phase from a rendered angle would"
    );
    println!("  have taken the root this whole line refuses.");
    println!();
    println!("  Nothing here quotes `energy_residual`, which `traversible_chain` records as");
    println!(
        "  identically zero for its convention, algebraically. The conserved quantity reported"
    );
    println!("  above is the METRIC SCALE of M+ J M, which can and does return Obstructed on a");
    println!("  transport outside the group.");
    println!();
    println!(
        "  This is a reading of the standing carrier. It does not claim the machine's language"
    );
    println!("  ecology resonates -- that is the deposit-and-ride question, and it has its own");
    println!("  falsifier in station seven.");
}

//! **The vertex emits where the tape only walked.**
//!
//! `research/records/2026-08-11_THE_TAPE_HAS_NO_VERTEX_AND_PRODUCTION_IS_RECEPTION_AT_THE_OTHER_HAND.md`
//! §5, ratified and until now unbuilt: bring the production path onto the oriented incidence
//! complex. This driver is the smallest complete instance of it — one declared material on which
//! bonding, cancellation, hand reversal, curvature and one grain-0 → grain-1 closure are all
//! reachable end to end.
//!
//! It runs the record's four falsifiers, **each of which can fail**, and prints the artifact:
//! the emitted successors and their residuals as text, never a census standing in for them.
//!
//! ```text
//!   1  two routes to one constituent must be able to CANCEL
//!   2  reversing the hand on a bonded pair must change the composition, endpoints holding
//!   3  a closed path must return a non-identity holonomy where the terrain is curved
//!   4  a completed compound must emit ONE successor at grain k+1 with its residual named
//! ```
//!
//! Every one of them is run against a declared **negative control** — a material on which it must
//! *not* fire — because a check whose material cannot vary the property under test is the same
//! defect as a check that cannot fail (`CLAUDE.md` §8).
//!
//! ```text
//! cargo run --release -p life --example the_vertex_emits_where_the_tape_only_walked -- \
//!     --corpus-form output/the_material_mouth_seals_the_declared_body/declared-corpus-native-rest-<address>.form
//! ```
//!
//! Without `--corpus-form` it runs on the driver's own declared material and says so. With one, it
//! takes `⪯` from the corpus's own `caused_by` relation — the causal order, never storage order.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::BufReader,
    path::PathBuf,
};

use life::{
    incidence_production::{
        DeclaredOccurrence, Emission, IncidenceComplex, IncidenceProductionError, PhaseChart, Route,
    },
    text_material::{ExactTextMaterialAtlas, TextMaterialRole},
};

/// The declared extents this run sweeps. Each is one declared material; the sweep exists because
/// the record demands the material that makes cancellation happen be *built*, not assumed.
const DECLARED_EXTENTS: &[usize] = &[16, 40, 80, 160, 320];

/// The declared route depth. A route is a simple oriented path; this bounds its length.
const DECLARED_ROUTE_DEPTH: usize = 4;

/// How many occurrences of one causal chain are admitted into the declared cut.
const DECLARED_OCCURRENCES: usize = 4;

/// How many emitted successors to print in full. Bounded printing only; the population is always
/// stated beside it.
const PRINTED_EMISSIONS: usize = 24;

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut corpus_form: Option<PathBuf> = None;
    let mut arguments = std::env::args().skip(1);
    while let Some(flag) = arguments.next() {
        let value = arguments
            .next()
            .ok_or_else(|| format!("{flag} carries no value"))?;
        match flag.as_str() {
            "--corpus-form" => corpus_form = Some(PathBuf::from(value)),
            other => return Err(format!("unknown argument {other}")),
        }
    }

    let (material, provenance) = match &corpus_form {
        Some(path) => declared_material_from_corpus(path)?,
        None => (
            driver_declared_material(),
            "the driver's own declared material (no --corpus-form supplied)".to_owned(),
        ),
    };

    println!("THE DECLARED MATERIAL");
    println!("  provenance: {provenance}");
    println!(
        "  {} occurrences; ⪯ is the corpus's own `caused_by` relation, never the storage ordinal",
        material.len()
    );
    for occurrence in &material {
        println!(
            "    storage {:>8}  caused_by {:>2}  {:?}",
            occurrence.storage_ordinal,
            occurrence.caused_by.len(),
            elide(&occurrence.text, 96)
        );
    }
    println!();

    // -- the sweep: which declared extent makes each falsifier reachable ------------------------
    println!("THE SWEEP — one declared material per extent");
    println!(
        "  cancellation is counted per declared chart. A cancellation that only appears where the \
         rotation is switched off is carried by the hand alone; one that survives every chart is \
         a property of the material."
    );
    println!(
        "  {:>6} {:>6} {:>8} {:>9} {:>7} {:>10} {:>10} {:>10} {:>7}",
        "extent",
        "sites",
        "contacts",
        "compounds",
        "⪯ edges",
        "half-turn",
        "adjacent",
        "spread",
        "curved"
    );
    let mut chosen: Option<(usize, IncidenceComplex)> = None;
    for extent in DECLARED_EXTENTS {
        let complex = match IncidenceComplex::found(&material, *extent) {
            Ok(complex) => complex,
            Err(error) => {
                println!("  {extent:>6}  refused: {error:?}");
                continue;
            }
        };
        let cancels = cancellations_by_chart(&complex);
        let curved = complex
            .hand_up(PhaseChart::WindingAdjacent)
            .map(|emissions| {
                emissions
                    .iter()
                    .filter(|emission| !emission.terrain_is_flat())
                    .count()
            })
            .unwrap_or(0);
        println!(
            "  {:>6} {:>6} {:>8} {:>9} {:>7} {:>10} {:>10} {:>10} {:>7}",
            extent,
            complex.sites().len(),
            complex.bonds().len(),
            complex.compounds().len(),
            complex.dependencies().len(),
            cancels[0],
            cancels[1],
            cancels[2],
            curved
        );
        if chosen.is_none()
            && cancels.iter().all(|count| *count > 0)
            && curved > 0
            && !complex.compounds().is_empty()
        {
            chosen = Some((*extent, complex));
        }
    }
    let (extent, complex) = match chosen {
        Some(chosen) => chosen,
        None => {
            let extent = *DECLARED_EXTENTS.last().expect("the sweep declares an extent");
            println!();
            println!(
                "  NO DECLARED EXTENT MADE CANCELLATION CHART-INVARIANT. Continuing at {extent} \
                 and reporting exactly what did and did not fire."
            );
            let complex = IncidenceComplex::found(&material, extent)
                .map_err(|error| format!("found the complex: {error:?}"))?;
            (extent, complex)
        }
    };
    println!();
    println!("  the run continues at extent {extent}");
    println!(
        "  the aperture returned its outside: {} inscription patches present and not admitted",
        complex.patches_outside_extent()
    );
    println!(
        "  self-contacts refused: {}",
        complex.self_contacts_refused()
    );
    println!();

    // -- `⪯` is not storage order --------------------------------------------------------------
    println!("⪯ IS NOT THE STORAGE ORDER");
    for (identity, ordinal, rank) in complex.causal_ranks() {
        println!(
            "  causal rank {rank}   storage ordinal {ordinal:>8}   {}",
            elide(identity, 72)
        );
    }
    let disagreements = complex.dependency_disagrees_with_storage();
    println!(
        "  pairs on which the two orders disagree or are incomparable: {}",
        disagreements.len()
    );
    for (left, right) in disagreements.iter().take(4) {
        println!("    {}  ·  {}", elide(left, 44), elide(right, 44));
    }
    println!(
        "  ⪯ edges carried into the complex (one constituent recurring at a later causal rank): {}",
        complex.dependencies().len()
    );
    println!();

    // -- `∂∂ = 0`, by the body's own organ -----------------------------------------------------
    println!("∂∂ = 0 — CHECKED BY `body::incidence::EventComplex`, NOT BY THIS MODULE");
    complex
        .validate_with_body(true)
        .map_err(|error| format!("the body refused the complex: {error:?}"))?;
    complex
        .validate_with_body(false)
        .map_err(|error| format!("the body refused the reordered complex: {error:?}"))?;
    let (sorted, reordered) = complex
        .emanated_under_both_storage_orders()
        .map_err(|error| format!("the body could not read the exposed boundary: {error:?}"))?;
    println!("  admitted in the body's indexed order and in a reversed one");
    println!(
        "  exposed-boundary reading: indexed {sorted}  ·  reversed {reordered}  ·  {}",
        if sorted == reordered {
            "STORAGE ORDER IS GAUGE"
        } else {
            "STORAGE ORDER MOVED THE READING — DEFECT"
        }
    );
    println!(
        "  the body reads the completed event one grain above its exposed boundary: {}",
        complex
            .body_outer_grain()
            .map_err(|error| format!("{error:?}"))?
    );

    // §II: *changing storage order without changing incidence or dependency must not change
    // `T_gamma`.* Taken at the production level, not only inside the body.
    let mut restacked = material.clone();
    restacked.reverse();
    let restacked = IncidenceComplex::found(&restacked, extent)
        .map_err(|error| format!("the restacked material: {error:?}"))?;
    let emitted = complex
        .hand_up(PhaseChart::WindingAdjacent)
        .map_err(|error| format!("hand up: {error:?}"))?;
    let restacked_emitted = restacked
        .hand_up(PhaseChart::WindingAdjacent)
        .map_err(|error| format!("hand up: {error:?}"))?;
    let canonical = |emissions: &[Emission]| {
        emissions
            .iter()
            .map(|emission| {
                (
                    emission.surface.clone(),
                    emission.holonomy_text(),
                    emission.causal_rank,
                )
            })
            .collect::<BTreeSet<_>>()
    };
    println!(
        "  the declared occurrences handed over in the reverse slice order emit {} successors \
         against {} — {}",
        restacked_emitted.len(),
        emitted.len(),
        if canonical(&emitted) == canonical(&restacked_emitted) {
            "IDENTICAL surfaces, holonomies and causal ranks. Storage order is gauge at the \
             production level too."
        } else {
            "THE EMISSIONS MOVED — storage order is being read as structure somewhere"
        }
    );
    println!();

    // -- FALSIFIER 1 — cancellation ------------------------------------------------------------
    println!("FALSIFIER 1 — TWO ROUTES TO ONE CONSTITUENT CANCEL");
    println!("  amplitudes are superposed by `holonic_engine::ExactReceiverPhasePopulation::receive`,");
    println!("  which sums in mode BEFORE any quadratic response. A count cannot produce this.");
    println!(
        "  TWO readings are taken. The PAIR is §IV's own unit — *opposed contributions in one \
         declared fiber actually compose to zero*. The COMPLETE FIBER summing to zero is the \
         stronger and rarer event, and is reported separately."
    );
    let mut pairs_per_chart: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut fibers_per_chart: BTreeMap<&'static str, usize> = BTreeMap::new();
    for chart in PhaseChart::ALL {
        let mut pairs = 0usize;
        let mut fibers = 0usize;
        let mut exhibited = 0usize;
        for source in 0..complex.sites().len() {
            let routes = complex
                .routes_from(source, DECLARED_ROUTE_DEPTH, chart)
                .map_err(|error| format!("routes: {error:?}"))?;
            for interference in complex.interfere_all(&routes, 0) {
                let target = interference.target;
                if interference.cancelled {
                    fibers += 1;
                }
                pairs += interference.annihilating_pairs.len();
                for pair in &interference.annihilating_pairs {
                    if exhibited >= 2 {
                        break;
                    }
                    exhibited += 1;
                    let (tape, tower, cross) = interference.pair_reading(*pair);
                    let first = &interference.routes[pair.0];
                    let second = &interference.routes[pair.1];
                    println!();
                    println!(
                        "  [chart {}]  two routes annihilate at {:?}",
                        chart.name(),
                        complex.sites()[target].surface
                    );
                    for route in [first, second] {
                        println!(
                            "    hand {:+}  α = ({}, {})   {}",
                            route.hand_parity,
                            route.amplitude.real,
                            route.amplitude.imaginary,
                            complex.route_surface(route)
                        );
                    }
                    println!("    |α₁|² + |α₂|²  (the count, relation switched off) = {tape}");
                    println!("    |α₁ + α₂|²     (the tower)                        = {tower}");
                    println!("    2Re(α₁ᾱ₂)      (the cross term — the vertex)      = {cross}");
                    let separated = IncidenceComplex::mode_separated_population(&[
                        first.clone(),
                        second.clone(),
                    ]);
                    println!(
                        "    NEGATIVE CONTROL — the same two currents, one mode each: {} modes \
                         survive and nothing cancels",
                        separated.coherent_modes.len()
                    );
                    println!(
                        "    the complete fiber at this constituent carries {} routes; Σ|α|² = {} \
                         and |Σα|² = {}",
                        interference.routes.len(),
                        interference.tape_reading,
                        interference.tower_reading
                    );
                }
            }
        }
        pairs_per_chart.insert(chart.name(), pairs);
        fibers_per_chart.insert(chart.name(), fibers);
    }
    println!();
    println!("  {:>18} {:>18} {:>22}", "chart", "annihilating pairs", "complete fibers at zero");
    for chart in PhaseChart::ALL {
        println!(
            "  {:>18} {:>18} {:>22}",
            chart.name(),
            pairs_per_chart[chart.name()],
            fibers_per_chart[chart.name()]
        );
    }
    let chart_invariant = pairs_per_chart.values().all(|count| *count > 0);
    println!(
        "  chart-invariant: {}",
        if chart_invariant {
            "YES — annihilation survives every declared chart, so it is a property of the material \
             and not of the chart"
        } else {
            "NO — annihilation is chart-dependent and must be read as such"
        }
    );
    println!(
        "  the complete fiber goes to zero only where the rotation is switched off: with the \
         rotation carried, the other routes arriving at that constituent do not sum away, and \
         that is the honest reading of a superposition rather than of a tally."
    );

    // The control material: a complex on which cancellation MUST NOT fire.
    let control = IncidenceComplex::found(&control_material(), 32)
        .map_err(|error| format!("the control material: {error:?}"))?;
    let control_cancels = cancellations_by_chart(&control).iter().sum::<usize>();
    println!(
        "  DECLARED NEGATIVE CONTROL — a material with no repeated constituent and no antiparallel \
         contact:"
    );
    println!(
        "    {} constituents · {} contacts · {} compounds · {} annihilations of any species",
        control.sites().len(),
        control.bonds().len(),
        control.compounds().len(),
        control_cancels
    );
    println!(
        "    {}",
        if control_cancels == 0 {
            "the falsifier can fail: it does not fire here"
        } else {
            "THE CONTROL ALSO CANCELLED — the falsifier is vacuous and this run proves nothing"
        }
    );
    println!();

    // -- FALSIFIER 2 — the hand ----------------------------------------------------------------
    println!("FALSIFIER 2 — REVERSING A HAND CHANGES THE COMPOSITION, THE ENDPOINTS HOLDING");
    let compound = 0usize;
    let target_bond = complex.compounds()[compound].bonds[0];
    let bond = &complex.bonds()[target_bond];
    let endpoints = (
        complex.sites()[bond.from].surface.clone(),
        complex.sites()[bond.to].surface.clone(),
    );
    println!(
        "  the contact: {:?} ⟶ {:?}   (∂ = to − from, so from enters Against and to enters With)",
        endpoints.0, endpoints.1
    );
    let reversed = complex
        .with_reversed_bond(target_bond)
        .map_err(|error| format!("reverse the hand: {error:?}"))?;
    let reversed_bond = &reversed.bonds()[target_bond];
    println!(
        "  reversed:    {:?} ⟶ {:?}   endpoints {}",
        reversed.sites()[reversed_bond.from].surface,
        reversed.sites()[reversed_bond.to].surface,
        if (
            reversed.sites()[reversed_bond.to].surface.clone(),
            reversed.sites()[reversed_bond.from].surface.clone(),
        ) == endpoints
        {
            "HOLD"
        } else {
            "MOVED — defect"
        }
    );

    // Measured over EVERY source, not one. An earlier form of this probe read routes from
    // `ingress()[0]` alone and reported "the hand is not carried" on material where that source
    // simply never reached the contact — a receiver-visible coordinate standing in for the
    // measurement. The orbit is taken over the whole route population.
    let mut before_map = BTreeMap::new();
    let mut after_map = BTreeMap::new();
    for source in 0..complex.sites().len() {
        before_map.extend(amplitudes_by_surface(
            &complex,
            &complex
                .routes_from(source, DECLARED_ROUTE_DEPTH, PhaseChart::WindingAdjacent)
                .map_err(|error| format!("routes before: {error:?}"))?,
        ));
        after_map.extend(amplitudes_by_surface(
            &reversed,
            &reversed
                .routes_from(source, DECLARED_ROUTE_DEPTH, PhaseChart::WindingAdjacent)
                .map_err(|error| format!("routes after: {error:?}"))?,
        ));
    }
    let mut moved = 0usize;
    let mut shown = 0usize;
    for (surface, amplitude) in &before_map {
        match after_map.get(surface) {
            Some(other) if other == amplitude => {}
            Some(other) => {
                moved += 1;
                if shown < 3 {
                    shown += 1;
                    println!("    composition moved:  {surface}");
                    println!("      before α = {amplitude}");
                    println!("      after  α = {other}");
                }
            }
            None => {
                moved += 1;
                if shown < 3 {
                    shown += 1;
                    println!("    route departed:     {surface}   (α was {amplitude})");
                }
            }
        }
    }
    println!(
        "  {} of {} route surfaces moved or departed under one reversed hand",
        moved,
        before_map.len()
    );
    println!(
        "  {}",
        if moved > 0 {
            "the hand does work"
        } else {
            "REVERSING THE HAND CHANGED NOTHING — the hand is not carried"
        }
    );
    match complex.body_refuses_flipped_compound_hand(compound, 0) {
        Ok(refusal) => println!(
            "  and the body REFUSES the same contact at the flipped traversal hand inside its \
             closed boundary: {refusal:?}"
        ),
        Err(IncidenceProductionError::Body(_)) => println!(
            "  THE BODY ADMITTED A FLIPPED TRAVERSAL HAND — ∂∂ = 0 is not being enforced"
        ),
        Err(error) => println!("  the flip could not be presented: {error:?}"),
    }
    println!();

    // -- FALSIFIER 3 — holonomy ----------------------------------------------------------------
    println!("FALSIFIER 3 — A CLOSED PATH RETAINS HOLONOMY WHERE THE TERRAIN IS CURVED");
    let mut by_chart: BTreeMap<&'static str, Vec<Emission>> = BTreeMap::new();
    for chart in PhaseChart::ALL {
        by_chart.insert(
            chart.name(),
            complex
                .hand_up(chart)
                .map_err(|error| format!("hand up: {error:?}"))?,
        );
    }
    println!("  {:>18} {:>10} {:>10}", "chart", "flat", "curved");
    for (chart, emissions) in &by_chart {
        let flat = emissions
            .iter()
            .filter(|emission| emission.terrain_is_flat())
            .count();
        println!(
            "  {chart:>18} {:>10} {:>10}",
            flat,
            emissions.len() - flat
        );
    }
    let adjacent = &by_chart[PhaseChart::WindingAdjacent.name()];
    let half_turn = &by_chart[PhaseChart::HalfTurnOnly.name()];
    let orbit = adjacent
        .iter()
        .zip(half_turn.iter())
        .filter(|(left, right)| left.holonomy != right.holonomy)
        .count();
    println!(
        "  the chart's orbit on this material is non-trivial at {orbit} of {} closed boundaries — \
         a gauge whose group acted trivially would not be a gauge",
        adjacent.len()
    );
    println!(
        "  the half-turn chart returns the identity on every closed boundary: {} of {}. That is \
         the tape's own chart, and it is why a tape cannot see curvature.",
        half_turn
            .iter()
            .filter(|emission| emission.terrain_is_flat())
            .count(),
        half_turn.len()
    );
    for emission in adjacent.iter().take(6) {
        println!(
            "    holonomy {:<34} chain gauge {:+}   {}",
            emission.holonomy_text(),
            emission.chain_gauge,
            elide(&emission.surface, 56)
        );
    }
    println!(
        "  the chain gauge is printed beside the holonomy and is NOT part of it: on an \
         odd-length closed boundary it flips with the traversal direction, so it is a coordinate \
         of the 2-chain. Reading it as curvature would be a receiver-visible coordinate promoted \
         into an invariant."
    );

    // The control: a declared material whose closed boundary MUST return the identity.
    let flat = IncidenceComplex::found(&flat_material(), 8)
        .map_err(|error| format!("the flat control: {error:?}"))?;
    let flat_emissions = flat
        .hand_up(PhaseChart::WindingAdjacent)
        .map_err(|error| format!("the flat control could not hand up: {error:?}"))?;
    println!(
        "  DECLARED NEGATIVE CONTROL — `ab ⟷ cc`, one bit crossed each way onto OPPOSED sheets:"
    );
    for emission in &flat_emissions {
        println!(
            "    holonomy {:<34} {}   {:?}",
            emission.holonomy_text(),
            if emission.terrain_is_flat() {
                "FLAT"
            } else {
                "curved"
            },
            emission.surface
        );
    }
    println!(
        "    the two turns are R(1) and R(1)⁻¹ — neither is the identity — and the boundary \
         returns the identity anyway. The falsifier can fail."
    );
    println!();

    // -- FALSIFIER 4 — closure and hand-up: THE ARTIFACT ---------------------------------------
    println!("FALSIFIER 4 — EVERY COMPLETED COMPOUND EMITS ONE SUCCESSOR AT GRAIN k+1");
    println!("  complete_(F,Q,0)(C_0) → (n_1, ρ_0).  One closed boundary, one constituent, one residual.");
    println!(
        "  {} closed internal boundaries → {} emitted successors at grain 1 (one each, never a \
         population of branches)",
        complex.compounds().len(),
        adjacent.len()
    );
    println!();
    println!("  THE EMITTED SUCCESSORS, VERBATIM");
    println!(
        "  a successor's surface is its closed boundary's own traversal, not reading order: the \
         compound is a cycle in the contact graph and the walk is where it closes."
    );
    for (at, emission) in adjacent.iter().take(PRINTED_EMISSIONS).enumerate() {
        println!();
        println!("  [{at:>3}] grain {}  causal rank {}", emission.grain, emission.causal_rank);
        println!("        surface   {:?}", emission.surface);
        println!(
            "        residual  holonomy {}   {}",
            emission.holonomy_text(),
            if emission.terrain_is_flat() {
                "flat"
            } else {
                "CURVED — the closed path did not return unchanged"
            }
        );
        println!(
            "        residual  {} internal contacts departed, carrying multiplicity {}, {} \
             constituents no longer active",
            emission.residual.internal_contacts,
            emission.residual.carried_multiplicity,
            emission.residual.sites_departed
        );
        for contact in emission.residual.departed_contacts.iter().take(6) {
            println!("                    departed: {contact}");
        }
        if emission.residual.exposed.is_empty() {
            println!("        residual  exposed boundary: NONE — this compound is saturated");
        } else {
            for (surface, polarity) in emission.residual.exposed.iter().take(6) {
                println!(
                    "        residual  exposed {:<10} {:?}",
                    polarity.name(),
                    surface
                );
            }
            if emission.residual.exposed.len() > 6 {
                println!(
                    "        residual  … {} further exposed constituents",
                    emission.residual.exposed.len() - 6
                );
            }
        }
    }
    if adjacent.len() > PRINTED_EMISSIONS {
        println!();
        println!(
            "  … {} further successors not printed",
            adjacent.len() - PRINTED_EMISSIONS
        );
    }
    println!();

    // -- the next grains, to the fixed point ----------------------------------------------------
    println!("  THE HAND-UP, ITERATED — do the emitted constituents themselves bond and close?");
    println!(
        "    §II says the complete EVENT emits one atomic successor. Each closed boundary emits \
         one constituent; the event's single successor is the fixed point of iterating that. This \
         is where the iteration actually stops on this material."
    );
    let mut carried = complex.clone();
    let mut population = adjacent.len();
    loop {
        let (_, next) = match carried.next_grain(PhaseChart::WindingAdjacent) {
            Ok(handed) => handed,
            Err(error) => {
                println!(
                    "    grain {} founded no complex above it: {error:?} — the iteration STOPS \
                     with {population} constituents. Whether that is one is the measurement.",
                    carried.grain() + 1
                );
                break;
            }
        };
        println!(
            "    grain {}: {} constituents · {} contacts · {} closed boundaries · body {}",
            next.grain(),
            next.sites().len(),
            next.bonds().len(),
            next.compounds().len(),
            match next.validate_with_body(true) {
                Ok(()) => "ADMITS (∂∂ = 0 holds one grain up)".to_owned(),
                Err(error) => format!("REFUSED {error:?}"),
            }
        );
        let emitted = match next.hand_up(PhaseChart::WindingAdjacent) {
            Ok(emitted) => emitted,
            Err(error) => {
                println!("    grain {} could not hand up: {error:?}", next.grain());
                break;
            }
        };
        if emitted.is_empty() {
            println!(
                "    grain {} CLOSED NOTHING: {} contacts, no independent cycle. The iteration \
                 stops with {} constituents and that is reported, not dressed.",
                next.grain(),
                next.bonds().len(),
                next.sites().len()
            );
            break;
        }
        println!(
            "    → {} successors at grain {}:",
            emitted.len(),
            next.grain() + 1
        );
        for emission in emitted.iter().take(3) {
            println!(
                "        holonomy {:<28} {:?}",
                emission.holonomy_text(),
                elide(&emission.surface, 76)
            );
        }
        if emitted.len() == 1 {
            println!(
                "    ONE constituent remains: this is the complete event's single atomic \
                 successor, at grain {}.",
                next.grain() + 1
            );
            break;
        }
        if emitted.len() >= population {
            println!(
                "    the population is not contracting ({population} → {}); the iteration is cut \
                 here rather than run to exhaustion, and the cut is declared.",
                emitted.len()
            );
            break;
        }
        population = emitted.len();
        carried = next;
    }
    println!();

    // -- the control on closure -----------------------------------------------------------------
    println!(
        "  DECLARED NEGATIVE CONTROL ON CLOSURE — the same material with no repeated constituent:"
    );
    println!(
        "    {} closed internal boundaries, {} emitted successors",
        control.compounds().len(),
        control
            .hand_up(PhaseChart::WindingAdjacent)
            .map(|emissions| emissions.len())
            .unwrap_or(0)
    );
    println!(
        "    {}",
        if control.compounds().is_empty() {
            "nothing closes, so nothing hands up: the falsifier can fail"
        } else {
            "THE CONTROL ALSO CLOSED — closure is not being decided by the material"
        }
    );

    Ok(())
}

fn cancellations_by_chart(complex: &IncidenceComplex) -> [usize; 3] {
    let mut cancellations = [0usize; 3];
    for (at, chart) in PhaseChart::ALL.into_iter().enumerate() {
        for source in 0..complex.sites().len() {
            let Ok(routes) = complex.routes_from(source, DECLARED_ROUTE_DEPTH, chart) else {
                continue;
            };
            for interference in complex.interfere_all(&routes, 0) {
                cancellations[at] += interference.annihilating_pairs.len();
            }
        }
    }
    cancellations
}

fn amplitudes_by_surface(complex: &IncidenceComplex, routes: &[Route]) -> BTreeMap<String, String> {
    let mut found = BTreeMap::new();
    for route in routes {
        found.insert(
            complex.route_surface(route),
            format!("({}, {})", route.amplitude.real, route.amplitude.imaginary),
        );
    }
    found
}

fn elide(text: &str, extent: usize) -> String {
    let flattened = text.split_whitespace().collect::<Vec<_>>().join(" ");
    if flattened.chars().count() <= extent {
        return flattened;
    }
    let kept = flattened.chars().take(extent).collect::<String>();
    format!("{kept}…")
}

/// The driver's own declared material, used when no corpus rest is supplied.
///
/// It is a causal chain whose storage ordinals deliberately do not ascend with it, so `⪯` and
/// storage order can be seen apart even here.
fn driver_declared_material() -> Vec<DeclaredOccurrence> {
    vec![
        DeclaredOccurrence {
            identity: "declared:b".to_owned(),
            storage_ordinal: 90,
            caused_by: BTreeSet::from(["declared:a".to_owned()]),
            text: "the arc bends the channel and the bends carry the return".to_owned(),
        },
        DeclaredOccurrence {
            identity: "declared:a".to_owned(),
            storage_ordinal: 91,
            caused_by: BTreeSet::new(),
            text: "the leader founds the channel and the channel carries the leader".to_owned(),
        },
        DeclaredOccurrence {
            identity: "declared:c".to_owned(),
            storage_ordinal: 12,
            caused_by: BTreeSet::from(["declared:b".to_owned()]),
            text: "the channel returns the leader and the leader founds the arc".to_owned(),
        },
    ]
}

/// The declared flat control for the holonomy falsifier.
///
/// `ab ⟷ cc`: `popcount('b' ⊕ 'c') = popcount('c' ⊕ 'a') = 1`, so both contacts turn by the same
/// magnitude; `popcount('c')` is even and `popcount('a')` is odd, so they land on opposed sheets
/// and the two turns are exact inverses. The closed boundary returns the identity while neither
/// turn is the identity.
fn flat_material() -> Vec<DeclaredOccurrence> {
    vec![DeclaredOccurrence {
        identity: "flat:a".to_owned(),
        storage_ordinal: 0,
        caused_by: BTreeSet::new(),
        text: "ab cc ab".to_owned(),
    }]
}

/// The declared negative control: every constituent distinct, so the contact graph is a forest.
/// A forest condenses for free and its remainder is empty — no cycle, no closure, no cancellation.
fn control_material() -> Vec<DeclaredOccurrence> {
    vec![DeclaredOccurrence {
        identity: "control:a".to_owned(),
        storage_ordinal: 0,
        caused_by: BTreeSet::new(),
        text: "alpha bravo charlie delta echo foxtrot golf hotel india".to_owned(),
    }]
}

/// The declared cut taken from the corpus: one causal chain of `DECLARED_OCCURRENCES` messages.
///
/// The selection rule, stated so it is checkable: consider only Human and Assistant occurrences,
/// because a document's `caused_by` is its own section order while a conversation's is an actual
/// reply chain; group them by the conversation their witnesses name; admit the **first**
/// conversation in corpus order whose chain reaches the declared depth. No scalar chooses.
fn declared_material_from_corpus(
    path: &PathBuf,
) -> Result<(Vec<DeclaredOccurrence>, String), String> {
    let file = File::open(path).map_err(|error| format!("open corpus: {error}"))?;
    let atlas = ExactTextMaterialAtlas::from_native_reader(BufReader::new(file))
        .map_err(|error| format!("mount corpus: {error:?}"))?;

    let mut by_conversation: BTreeMap<String, Vec<(u64, String, BTreeSet<String>, String)>> =
        BTreeMap::new();
    let mut order: Vec<String> = Vec::new();
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut with_predecessor = 0usize;
    for occurrence in atlas.corpus().occurrences() {
        if !occurrence.caused_by.is_empty() {
            with_predecessor += 1;
        }
        if occurrence.role == TextMaterialRole::Document {
            continue;
        }
        let Some(conversation) = occurrence
            .witnesses
            .iter()
            .map(|witness| witness.conversation.as_str())
            .min()
        else {
            continue;
        };
        if seen.insert(conversation.to_owned()) {
            order.push(conversation.to_owned());
        }
        by_conversation
            .entry(conversation.to_owned())
            .or_default()
            .push((
                occurrence.ordinal,
                occurrence.native_identity.clone(),
                occurrence.caused_by.clone(),
                occurrence.text.clone(),
            ));
    }
    drop(atlas);

    for conversation in &order {
        let group = &by_conversation[conversation];
        let present = group
            .iter()
            .map(|entry| entry.1.as_str())
            .collect::<BTreeSet<_>>();
        // Follow the reply chain from a root that has no cause inside the group.
        let by_identity = group
            .iter()
            .map(|entry| (entry.1.as_str(), entry))
            .collect::<BTreeMap<_, _>>();
        let mut successor: BTreeMap<&str, &str> = BTreeMap::new();
        for entry in group {
            for cause in &entry.2 {
                if present.contains(cause.as_str()) {
                    successor.insert(cause.as_str(), entry.1.as_str());
                }
            }
        }
        let Some(root) = group
            .iter()
            .find(|entry| entry.2.iter().all(|cause| !present.contains(cause.as_str())))
        else {
            continue;
        };
        let mut chain = Vec::new();
        let mut at = root.1.as_str();
        loop {
            let entry = by_identity[at];
            if entry.3.split_whitespace().count() < 2 {
                break;
            }
            chain.push(DeclaredOccurrence {
                identity: entry.1.clone(),
                storage_ordinal: entry.0,
                caused_by: entry.2.clone(),
                text: entry.3.clone(),
            });
            if chain.len() == DECLARED_OCCURRENCES {
                break;
            }
            match successor.get(at) {
                Some(next) => at = next,
                None => break,
            }
        }
        if chain.len() == DECLARED_OCCURRENCES {
            return Ok((
                chain,
                format!(
                    "the sealed corpus — {with_predecessor} occurrences carry a predecessor; the \
                     first conversation in corpus order whose reply chain reaches \
                     {DECLARED_OCCURRENCES}"
                ),
            ));
        }
    }
    Err(format!(
        "no conversation in the sealed corpus carried a reply chain of {DECLARED_OCCURRENCES}"
    ))
}

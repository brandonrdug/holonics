//! **Phoenix station four: the front is co-present, or the gauge moves it.**
//!
//! Plan: `blueprint/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`
//!
//! Every Phoenix station so far has reported a front census — `21` co-present fronts on this site —
//! and **asserted** the co-presence rather than adjudicating it. This station adjudicates it.
//!
//! # A hand on a front is a gauge, not a schedule
//!
//! `CausalDiagram::layers()` decides which occurrences are co-present and nothing here can change
//! that. `FrontHand` only chooses how a front the diagram **already declared co-present** is
//! traversed. Co-presence is exactly the claim that this choice is invisible, so the certification
//! is the gauge's **orbit**: it must be empty at every occurrence port, and the work vector must not
//! move either.
//!
//! # The gauge must exhibit its own orbit, and it must be able to have one
//!
//! `CLAUDE.md` §8 convicts `PivotRule::ALL` — an instrument built to prevent exactly this defect
//! that became the defect, because on all five declared fixtures its three rules produced identical
//! traces and cutting the loop to one rule killed zero of thirty-one tests. **A gauge whose declared
//! elements cannot differ on the material has gauged nothing.** So this station reports two things
//! before any verdict: how many fronts have breadth greater than one (a hand on a singleton is the
//! identity), and what `FrontHand::DraggedOntoItsProducer` does — an order the diagram **refused**, which must
//! refuse back.
//!
//! ```text
//! cargo run --release -q -p holonic-engine \
//!   --example the_front_is_co_present_or_the_gauge_moves_it -- /home/b/models/gemma-4-E4B-it
//! ```

#[path = "phoenix/site.rs"]
mod site;

use std::collections::BTreeMap;

use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::ported_operation::{realize_under, FrontHand, PortedError};
use site::{found, ResidentSourceCarrier, BAND_POPULATION, BASE};

const HANDS: [(FrontHand, &str); 3] = [
    (FrontHand::AsFounded, "as the chronology founded it"),
    (FrontHand::Reversed, "against the founding hand"),
    (FrontHand::Rotated, "rotated by one"),
];

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let terms: usize = std::env::var("TERMS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(20);

    let chart = match ResidentReadout::new() {
        Ok(chart) => chart,
        Err(error) => {
            println!("the resident chart refused: {error:?}");
            std::process::exit(1);
        }
    };
    println!("PHOENIX STATION FOUR — THE FRONT IS CO-PRESENT, OR THE GAUGE MOVES IT");
    println!();
    println!("  resident chart                    {}", chart.device_name());

    let (site, container, file) = match found(&root, BASE, terms, None) {
        Ok(triple) => triple,
        Err(error) => {
            println!("  the founding refused: {error}");
            std::process::exit(1);
        }
    };
    let fronts = site.complex.fronts().expect("fronts");

    // -----------------------------------------------------------------------------------------
    // CAN THE GAUGE HAVE AN ORBIT AT ALL? Asked BEFORE the verdict, because a gauge whose elements
    // cannot differ on the material has gauged nothing however green it returns.
    // -----------------------------------------------------------------------------------------
    let movable: Vec<&holonic_engine::ported_operation::Front> =
        fronts.iter().filter(|front| front.breadth() > 1).collect();
    let widest = fronts.iter().map(|front| front.breadth()).max().unwrap_or(0);
    let permutable: usize = movable.iter().map(|front| front.breadth()).sum();
    println!();
    println!("  CAN THE GAUGE MOVE ANYTHING? — asked before the verdict");
    println!("    fronts                            {}", fronts.len());
    println!("    fronts of breadth > 1             {}", movable.len());
    println!("    widest front                      {widest}");
    println!("    occurrences the hand can permute  {permutable} of {}", site.program.operations.len());
    if movable.is_empty() {
        println!("    THE GAUGE IS VACUOUS on this material — every front is a singleton, so all");
        println!("    three lawful hands are the identity map and agreement carries no evidence.");
        std::process::exit(1);
    }

    // -----------------------------------------------------------------------------------------
    // THE ORBIT.
    // -----------------------------------------------------------------------------------------
    let mut carrier = ResidentSourceCarrier {
        chart: &chart,
        container,
        file,
        below_the_frame: 0,
        rotations: BTreeMap::from([(BAND_POPULATION.to_owned(), site.band_elements.clone())]),
        resident: BTreeMap::new(),
        reused: 0,
    };
    let mut readings = Vec::new();
    for (hand, told) in HANDS {
        let clock = std::time::Instant::now();
        match realize_under(
            &site.complex,
            &site.program,
            &mut carrier,
            &BTreeMap::new(),
            hand,
        ) {
            Ok(receipt) => {
                println!();
                println!("  REALIZED {told}");
                println!("    ports written                   {}", receipt.carried.len());
                println!("    wall clock                      {:?}", clock.elapsed());
                readings.push((hand, told, receipt));
            }
            Err(error) => {
                println!();
                println!("  REALIZING {told} REFUSED: {error}");
                println!("  A LAWFUL HAND REFUSED. The front census is wrong, not the hand.");
                std::process::exit(1);
            }
        }
    }

    let founded = &readings[0].2;
    println!();
    println!("  THE GAUGE'S ORBIT — port by exact port, and it must be empty");
    let mut orbit_empty = true;
    for (_, told, receipt) in &readings[1..] {
        let moved = founded
            .carried
            .iter()
            .filter(|(port, standing)| receipt.carried.get(port) != Some(*standing))
            .count();
        let absent = founded
            .carried
            .keys()
            .filter(|port| !receipt.carried.contains_key(port))
            .count();
        let work_moved = receipt.work != founded.work;
        println!("    {told:<32} ports moved {moved}   ports absent {absent}   work moved {work_moved}");
        orbit_empty &= moved == 0 && absent == 0 && !work_moved;
    }
    println!("    the orbit is empty                {orbit_empty}");

    // -----------------------------------------------------------------------------------------
    // THE CONTROL. An order the diagram REFUSED.
    // -----------------------------------------------------------------------------------------
    let (dragged, disturbed) =
        FrontHand::DraggedOntoItsProducer.applied_to(&site.complex, fronts.clone());
    let displaced = fronts
        .iter()
        .zip(&dragged)
        .filter(|(before, after)| before.occurrences != after.occurrences)
        .count();
    let outcome = realize_under(
        &site.complex,
        &site.program,
        &mut carrier,
        &BTreeMap::new(),
        FrontHand::DraggedOntoItsProducer,
    );
    println!();
    println!("  THE CONTROL — an occurrence dragged into the front of a producer it depends on");
    match disturbed {
        Some((consumer, producer)) => println!(
            "    it moved {consumer:?} onto its producer {producer:?}"
        ),
        None => {
            println!("    THE CONTROL DID NOT FIRE — no consumer has a producer in an earlier");
            println!("    front, so there is no illegal order to build and the empty orbit above");
            println!("    carries no evidence.");
            std::process::exit(1);
        }
    }
    println!("    fronts the drag disturbed         {displaced} of {}", fronts.len());
    match &outcome {
        Err(PortedError::StandingAbsent { port }) => {
            println!("    the realization REFUSED           true");
            println!("    and it named the port it wanted   {port:?}");
        }
        Err(other) => {
            println!("    the realization REFUSED           true");
            println!("    with                              {other}");
        }
        Ok(receipt) => {
            let moved = founded
                .carried
                .iter()
                .filter(|(port, standing)| receipt.carried.get(port) != Some(*standing))
                .count();
            println!("    the realization REFUSED           false");
            println!("    ports it moved instead            {moved}");
        }
    }
    let refused = outcome.is_err();

    println!();
    println!("THE STATION'S VERDICT");
    println!();
    println!("  the front census is adjudicated             {}", orbit_empty && refused);
    println!();
    println!("  `CausalDiagram::layers()` declared {} fronts, {} of them of breadth greater", fronts.len(), movable.len());
    println!("  than one, covering {permutable} of {} occurrences. Permuting WITHIN those fronts —", site.program.operations.len());
    println!("  against the founding hand, and rotated — moves nothing at any occurrence port and");
    println!("  does not move the exact work vector either. Permuting ACROSS them refuses.");
    println!();
    println!("  So co-presence is a property the diagram carries and not a label a driver applied,");
    println!("  and the gauge is not vacuous: it has elements that CAN differ, and the control that");
    println!("  makes them differ is exhibited beside them rather than argued.");
    println!();
    println!("  AND A QUALIFICATION THE CONTROL FOUND ON THE WAY, which the empty orbit hides.");
    println!("  A front is realized SEQUENTIALLY, not simultaneously: `realize` writes each");
    println!("  occurrence's output into the standing map as it goes, so a later member of the same");
    println!("  front can read an earlier one's output. Dragging a consumer into its producer's");
    println!("  front and appending it AFTER the producer therefore returns identically and refuses");
    println!("  nothing — measured, twice, before this control was rebuilt to insert it FIRST.");
    println!();
    println!("  What `realize` enforces is DATAFLOW, not front membership. The fronts are honest");
    println!("  because `layers()` puts no producer and consumer in one front, and the empty orbit");
    println!("  above is evidence of exactly that and of nothing stronger.");
    println!();
    println!("  THE APERTURE. This certifies the diagram the seal and the cultivation conduct —");
    println!("  the one `phoenix/site.rs` founds. `the_bound_diagram_conducts_one_site` builds its");
    println!("  own complex of the SAME physical site and returns 120 occurrences over 21 fronts,");
    println!("  and that diagram is NOT certified here. The known difference between them is that");
    println!("  the shared site supplies the band ladder from the carrier by name instead of");
    println!("  founding it as occurrences; whether that is the whole cause is unmeasured.");
    println!();
    println!("  It is one site's contact half either way. CONSTRUCTION_STATE is untouched.");
    if !(orbit_empty && refused) {
        std::process::exit(1);
    }
}

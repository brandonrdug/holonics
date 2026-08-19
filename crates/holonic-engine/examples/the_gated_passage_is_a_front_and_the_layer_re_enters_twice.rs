//! **Phoenix station six: the gated passage is a front, and the layer re-enters twice.**
//!
//! Plan: `blueprint/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`
//!
//! Every station before this one conducted the site's **contact half** and said so. This one reaches
//! the whole layer the source's testimony decides: the contact's return projected back, the first
//! re-entry, the gated passage, and the second re-entry.
//!
//! # Three things the governing scope requires, checked here rather than asserted
//!
//! **`gate` and `up` are a FRONT, not a serial matrix chain.** Neither reads the other, so
//! `CausalDiagram::layers()` puts them in one front — and this station names the front they land in
//! rather than claiming co-presence in prose. Station four already certified that a front's hand is
//! a gauge with an empty orbit on this diagram.
//!
//! **The activation is the source's, read exactly.** `config.json` declares `gelu_pytorch_tanh`, so
//! the turn's inner argument is `s·(x + c·x³)` with both constants read from their `binary64` bits
//! through the standing IEEE-754 mouth. No float arithmetic occurs; the bits are integer literals.
//! Before this, the operation computed `x·sigmoid(2x)`, which is a different function.
//!
//! **What the source does not decide is not guessed.** Four populations layer zero carries —
//! `per_layer_input_gate`, `per_layer_projection`, `post_per_layer_input_norm` and `layer_scalar` —
//! have no composition fixed by the configuration or the model card, and appear in **no** operation
//! of this diagram. They are returned as the open questions they are.
//!
//! ```text
//! cargo run --release -q -p holonic-engine \
//!   --example the_gated_passage_is_a_front_and_the_layer_re_enters_twice -- /home/b/models/gemma-4-E4B-it
//! ```

#[path = "phoenix/site.rs"]
mod site;

use std::collections::BTreeMap;

use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::interaction::OccurrencePort;
use holonic_engine::ported_operation::{realize, PortedOperationKind};
use num_traits::Zero;
use site::{
    found_reaching, gelu_inner, Reach, ResidentSourceCarrier, BAND_POPULATION, BASE,
    WHOLE_LAYER_OPEN,
};

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
    println!("PHOENIX STATION SIX — THE GATED PASSAGE IS A FRONT, AND THE LAYER RE-ENTERS TWICE");
    println!();
    println!("  resident chart                    {}", chart.device_name());

    let (half, _, _) = found_reaching(&root, BASE, terms, None, Reach::ContactHalf).expect("half");
    let (site, container, file) = match found_reaching(&root, BASE, terms, None, Reach::WholeLayer) {
        Ok(triple) => triple,
        Err(error) => {
            println!("  the founding refused: {error}");
            std::process::exit(1);
        }
    };
    let fronts = site.complex.fronts().expect("fronts");
    let half_fronts = half.complex.fronts().expect("fronts");

    println!();
    println!("  THE DIAGRAM, AGAINST THE CONTACT HALF THE OTHER STATIONS CONDUCT");
    println!(
        "    operations                      {} against {}",
        site.program.operations.len(),
        half.program.operations.len()
    );
    println!(
        "    dependency span                 {} fronts against {}",
        fronts.len(),
        half_fronts.len()
    );
    println!(
        "    widest front                    {} against {}",
        fronts.iter().map(|f| f.breadth()).max().unwrap_or(0),
        half_fronts.iter().map(|f| f.breadth()).max().unwrap_or(0)
    );
    println!("    stored populations NAMED        {}", site.populations.len());
    for population in &site.populations {
        println!("        {population}");
    }
    let census = site.complex.species_census();
    println!("    species census");
    for (species, count) in &census {
        println!("        {species:?}   {count}");
    }

    // -----------------------------------------------------------------------------------------
    // THE GATE AND THE CARRIED BRANCH ARE CO-PRESENT. Named, not asserted.
    // -----------------------------------------------------------------------------------------
    let named_event = |suffix: &str| -> Vec<holonic_engine::causal::EventId> {
        site.program
            .operations
            .iter()
            .filter(|(_, operation)| {
                matches!(operation, PortedOperationKind::Contract { population } if population.ends_with(suffix))
            })
            .map(|(event, _)| *event)
            .collect()
    };
    let gates = named_event("mlp.gate_proj.weight");
    let ups = named_event("mlp.up_proj.weight");
    println!();
    println!("  THE GATE AND THE CARRIED BRANCH ARE ONE FRONT — read off the chronology");
    let mut co_present = 0usize;
    for (gate, up) in gates.iter().zip(&ups) {
        let front_of = |event: &holonic_engine::causal::EventId| {
            fronts
                .iter()
                .position(|front| front.occurrences.contains(event))
        };
        let (left, right) = (front_of(gate), front_of(up));
        println!(
            "    gate {gate:?} at front {left:?}   up {up:?} at front {right:?}   co-present {}",
            left == right && left.is_some()
        );
        if left == right && left.is_some() {
            co_present += 1;
        }
    }
    println!("    co-present pairs                {co_present} of {}", gates.len());

    let (scale, cubic) = gelu_inner();
    println!();
    println!("  THE TURN'S INNER ARGUMENT — the source's, read from its bits");
    println!("    `hidden_activation`             gelu_pytorch_tanh");
    println!("    scale, exactly                  {scale}");
    println!("    cubic, exactly                  {cubic}");

    // -----------------------------------------------------------------------------------------
    // THE CONDUCT.
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
    let clock = std::time::Instant::now();
    let receipt = match realize(&site.complex, &site.program, &mut carrier, &BTreeMap::new()) {
        Ok(receipt) => receipt,
        Err(error) => {
            println!();
            println!("  THE LAYER REFUSED: {error}");
            println!("  That is the station's return. The obstruction is named and nothing is claimed.");
            std::process::exit(1);
        }
    };
    let (entries, nonzero, widest) = receipt.retained_population();
    println!();
    println!("  THE LAYER'S RETURN");
    println!("    fronts conducted                {}", receipt.fronts.len());
    println!("    ports written                   {}", receipt.carried.len());
    println!("    wall clock                      {:?}", clock.elapsed());
    println!("    entries retained below the frame {}", carrier.below_the_frame);
    println!("    retained fibre                  {entries} entries, {nonzero} nonzero");
    if let Some((event, value)) = &widest {
        let text = value.to_string();
        println!(
            "    widest single residual          {event:?}  {}",
            if text.len() > 44 { format!("{}…", &text[..44]) } else { text }
        );
    }
    println!("    exact work                      {:?}", receipt.work);

    let returns: Vec<Vec<relational_geometry::Rat>> = site
        .returns
        .iter()
        .map(|event| receipt.carried[&OccurrencePort::output(*event, 0)].clone())
        .collect();
    println!("    positions returned              {}", returns.len());
    println!("    width                           {}", returns[0].len());

    // -----------------------------------------------------------------------------------------
    // THE RE-ENTRY CARRIED SOMETHING. Read as a population, at every position.
    // -----------------------------------------------------------------------------------------
    let re_entries: Vec<holonic_engine::causal::EventId> = site
        .program
        .operations
        .iter()
        .filter(|(_, operation)| matches!(operation, PortedOperationKind::ReEntry))
        .map(|(event, _)| *event)
        .collect();
    // `realize` writes only OUTPUT ports, so an input port is read through the bond map — the
    // diagram's own dataflow — rather than looked up directly. The first form of this read
    // `carried[input(event, 0)]`, got nothing, and printed "0 of 2560" as though the passage had
    // contributed nothing. A measurement that returns zero because it addressed the wrong port is
    // not a finding.
    let mut arriving: BTreeMap<OccurrencePort, OccurrencePort> = BTreeMap::new();
    for interaction in site.complex.shape.interactions.values() {
        for bond in &interaction.bonds {
            arriving.insert(bond.target, bond.source);
        }
    }
    let through = |port: OccurrencePort| -> Vec<relational_geometry::Rat> {
        arriving
            .get(&port)
            .and_then(|source| receipt.carried.get(source))
            .cloned()
            .unwrap_or_default()
    };
    println!();
    println!("  THE RE-ENTRIES — {} of them, two per position", re_entries.len());
    for (position, event) in site.returns.iter().enumerate() {
        let returned = &receipt.carried[&OccurrencePort::output(*event, 0)];
        let retained = through(OccurrencePort::input(*event, 0));
        let contributed = through(OccurrencePort::input(*event, 1));
        let moved = returned
            .iter()
            .zip(&retained)
            .filter(|(after, before)| after != before)
            .count();
        let carried_something = contributed.iter().filter(|value| !value.is_zero()).count();
        println!(
            "    position {position}   the re-entry moved {moved} of {}   the passage carried {carried_something} of {}",
            returned.len(),
            contributed.len()
        );
    }

    // -----------------------------------------------------------------------------------------
    // WHAT THE SOURCE DOES NOT DECIDE.
    // -----------------------------------------------------------------------------------------
    println!();
    println!("  THE OPEN CANDIDATE POPULATIONS — layer zero carries them and this diagram does not");
    for (population, question) in WHOLE_LAYER_OPEN {
        let bound = site.populations.iter().any(|held| held.ends_with(population));
        println!("    {population}");
        println!("        bound by this diagram       {bound}");
        println!("        {question}");
    }

    println!();
    println!("THE STATION'S VERDICT");
    println!();
    println!("  The whole layer the source's testimony decides conducts. `gate` and `up` land in");
    println!("  ONE front at every position — {co_present} of {} — so the passage is a front rather", gates.len());
    println!("  than a serial chain, and station four already certified that a front's hand is a");
    println!("  gauge whose orbit is empty on this diagram.");
    println!();
    println!("  The turn is the source's `gelu_pytorch_tanh`, with both constants read exactly from");
    println!("  their stored `binary64` words rather than approximated. Before this station the");
    println!("  operation computed `x·sigmoid(2x)`, which is a different function, and the diagram");
    println!("  that used it is retained readable rather than rewritten.");
    println!();
    println!("  Four populations the source does not decide are bound by NO operation here and are");
    println!("  returned as questions. A layer that guessed them would conduct just as well and");
    println!("  would be a fiction, which is the whole reason they are named.");
    println!();
    println!("  This is ONE layer of forty-two, and no emission head. CONSTRUCTION_STATE is untouched.");
}

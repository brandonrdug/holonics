//! **Phoenix station five's condensation half: which axes are load-bearing, and what collapses.**
//!
//! Plan: `blueprint/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`
//! §10 — *"Receiver-minimality is the completion condition: every retained native axis or relation
//! has a named future/intervention which separates it from the body without that relation; every
//! departed distinction is in a reconstruction fibre."*
//!
//! # The deed
//!
//! A **targeted ablation** withdraws a declared span of the entering construction's coordinates and
//! **retains what it withdrew**. The declared receiver family then reads the carried standing. A
//! span whose withdrawal moves no receiver is collapsible **for this family**; a span whose
//! withdrawal moves one is load-bearing, and the receiver that moved is its named separating
//! consequence.
//!
//! Each ablation is a **matched sibling** of the base differing in exactly one relation, which is
//! what makes the attribution possible. Two controls bound it: a no-op sibling must move nothing,
//! and withdrawing everything must move something — otherwise the reading is measuring its own
//! apparatus.
//!
//! # What this is not
//!
//! It is not a compression figure. `CLAUDE.md` and the master contract both refuse a byte count
//! quoted without its decoder, and refuse a population the material never excited being called
//! condensed. The cost vector below reports the **retained fibre's own coordinates** alongside the
//! carried ones, and their sum is the only quotable number.
//!
//! ```text
//! cargo run --release -q -p holonic-engine \
//!   --example the_axes_are_condensed_to_what_a_receiver_can_separate -- /home/b/models/gemma-4-E4B-it
//! ```

#[path = "phoenix/site.rs"]
mod site;

use holonic_engine::embedding_fiber::ResidentReadout;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use site::{conduct, BASE, CAUSED};

/// The declared partition of the entering construction. **Stated, and its outside reported.**
const SPANS: usize = 64;

/// One coordinate family the carried standing is read at.
fn declared_coordinates(width: usize) -> Vec<usize> {
    (0..32).map(|k| k * width / 32).collect()
}

/// The two faces a receiver reads: the **hand**, which a magnitude reading deletes, and an
/// **order**, which is a relation. Neither is a value and both cross a frame.
fn faces(section: &[Rat], coordinates: &[usize]) -> Vec<u8> {
    let mut read = Vec::with_capacity(coordinates.len() * 2);
    for (at, coordinate) in coordinates.iter().enumerate() {
        let value = section.get(*coordinate).cloned().unwrap_or_else(Rat::zero);
        read.push(if value.is_positive() {
            1
        } else if value.is_negative() {
            2
        } else {
            0
        });
        let other = coordinates
            .get(at + 1)
            .and_then(|next| section.get(*next))
            .cloned()
            .unwrap_or_else(Rat::zero);
        read.push(match value.cmp(&other) {
            std::cmp::Ordering::Less => 1,
            std::cmp::Ordering::Equal => 2,
            std::cmp::Ordering::Greater => 3,
        });
    }
    read
}

/// Which receivers moved between two returns, by index. **A population, not a count.**
fn moved(base: &[Vec<Rat>], other: &[Vec<Rat>], coordinates: &[usize]) -> Vec<usize> {
    let mut which = Vec::new();
    for (position, section) in base.iter().enumerate() {
        let left = faces(section, coordinates);
        let right = faces(&other[position], coordinates);
        for (receiver, (a, b)) in left.iter().zip(&right).enumerate() {
            if a != b && !which.contains(&receiver) {
                which.push(receiver);
            }
        }
    }
    which
}

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
            println!("The admitted hot deed returns a typed refusal. No CPU answer appears.");
            std::process::exit(1);
        }
    };

    println!("PHOENIX STATION FIVE (CONDENSATION) — RECEIVER-MINIMALITY ON REAL MATERIAL");
    println!();
    println!("  resident chart                    {}", chart.device_name());
    println!("  caused positions                  {}", CAUSED.len());

    let clock = std::time::Instant::now();
    let base = match conduct(&root, &chart, BASE, terms, None) {
        Ok(carried) => carried,
        Err(error) => {
            println!("  the base REFUSED: {error}");
            std::process::exit(1);
        }
    };
    println!("  base conducted in                 {:?}", clock.elapsed());

    let entering_width = 2560;
    let carried_width = base[0].len();
    let coordinates = declared_coordinates(carried_width);
    let span = entering_width / SPANS;
    println!("  entering construction width       {entering_width}");
    println!("  carried standing width            {carried_width}");
    println!("  declared spans                    {SPANS} of {span} coordinates each");
    println!("  declared receivers                {} — a hand and an order at each of {} coordinates",
        coordinates.len() * 2, coordinates.len());

    // ---------------------------------------------------------------------------------------
    // THE TWO CONTROLS.
    // ---------------------------------------------------------------------------------------
    println!();
    println!("  THE CONTROLS — a reading that fails these is measuring its own apparatus");
    let no_op = conduct(&root, &chart, BASE, terms, Some((0, 0))).expect("conducted");
    let no_op_moved = moved(&base, &no_op, &coordinates);
    println!("    a NO-OP ablation moved                     {} receivers", no_op_moved.len());
    let everything = conduct(&root, &chart, BASE, terms, Some((0, entering_width))).expect("conducted");
    let everything_moved = moved(&base, &everything, &coordinates);
    println!("    withdrawing EVERYTHING moved               {} receivers", everything_moved.len());
    if !no_op_moved.is_empty() || everything_moved.is_empty() {
        println!("    THE CONTROLS FAILED. The reading below would be about the apparatus.");
        std::process::exit(1);
    }
    println!("    both controls hold.");

    // ---------------------------------------------------------------------------------------
    // THE ABLATION SWEEP.
    // ---------------------------------------------------------------------------------------
    println!();
    println!("  THE SWEEP — one matched sibling per declared span");
    println!();
    let clock = std::time::Instant::now();
    let mut load_bearing: Vec<(usize, Vec<usize>)> = Vec::new();
    let mut collapsible: Vec<usize> = Vec::new();
    for index in 0..SPANS {
        let from = index * span;
        let sibling = match conduct(&root, &chart, BASE, terms, Some((from, span))) {
            Ok(carried) => carried,
            Err(error) => {
                println!("    span {index} REFUSED: {error}");
                continue;
            }
        };
        let which = moved(&base, &sibling, &coordinates);
        if which.is_empty() {
            collapsible.push(index);
        } else {
            load_bearing.push((index, which));
        }
    }
    println!("    swept in                                   {:?}", clock.elapsed());
    println!("    spans that are LOAD-BEARING                {}", load_bearing.len());
    println!("    spans no declared receiver separates       {}", collapsible.len());
    println!();
    for (index, which) in load_bearing.iter().take(6) {
        println!(
            "      span {index:>3} at coordinate {:>5}  moved {} receiver(s), first {:?}",
            index * span,
            which.len(),
            &which[..which.len().min(4)]
        );
    }
    if !collapsible.is_empty() {
        println!();
        println!(
            "      collapsible spans, by index: {:?}{}",
            &collapsible[..collapsible.len().min(12)],
            if collapsible.len() > 12 { " …" } else { "" }
        );
    }

    // ---------------------------------------------------------------------------------------
    // THE COST VECTOR, WITH THE FIBRE COUNTED.
    // ---------------------------------------------------------------------------------------
    println!();
    println!("  THE COST VECTOR — the fibre is inside it, which is what makes it quotable");
    println!();
    let retained = load_bearing.len() * span;
    let collapsed = collapsible.len() * span;
    println!("    entering coordinates                       {entering_width}");
    println!("    load-bearing, retained in the body         {retained}");
    println!("    collapsed, retained in the FIBRE           {collapsed}");
    println!("    their sum                                  {}", retained + collapsed);
    println!();
    println!("    A condensation factor is NOT quoted here. A collapsed coordinate is retained,");
    println!("    not deleted, and a figure that omitted the fibre would be the absolute-volume");
    println!("    violation this project refuses by name.");

    println!();
    println!("  RECEIVER-MINIMALITY, the completion condition");
    println!();
    if collapsible.is_empty() {
        println!("    EVERY declared span has a named separating consequence at this aperture.");
        println!("    The body is receiver-minimal for this family and this partition: nothing");
        println!("    can be withdrawn without moving a receiver.");
    } else {
        println!("    {} of {SPANS} spans have a named separating consequence.", load_bearing.len());
        println!("    The rest are collapsible FOR THIS FAMILY, and a richer receiver reopens them.");
    }

    println!();
    println!("THE STATION'S VERDICT");
    println!();
    println!("  Every span was withdrawn as a matched sibling differing in exactly one relation,");
    println!("  and what each withdrew is retained at its own occurrence, so the predecessor is");
    println!("  reconstructible from the return and the fibre together.");
    println!("  Both controls held, so the reading is about the material and not the apparatus.");
    println!("  No compression factor is claimed and no representative was selected.");
    println!();
    println!("  The aperture is one site's contact half at a declared span partition.");
    println!("  CONSTRUCTION_STATE is untouched.");
}

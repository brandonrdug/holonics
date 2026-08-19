//! **Phoenix station seven: the emission is a section, and the answer is a block.**
//!
//! Plan: `blueprint/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`
//!
//! The layer conducts. This closes the body: the final rebase, the **tied** head — `embed_tokens`
//! read the other way, because `tie_word_embeddings` is `true` and no `lm_head` exists in the
//! container — and the **illicial potential section**, 262,144 wide, returned whole.
//!
//! # No argmax, and the reason is not squeamishness
//!
//! `CLAUDE.md` §0d bans a chooser standing outside the channels, and *"replacing an argmax with 'the
//! one deterministic output' preserves it."* So the return here is the section, and the reading is a
//! **block**: the coordinates a declared receiver cannot separate from the widest. A block of one is
//! a real answer; a block of nine is also a real answer, and collapsing it to a pick would be the
//! deletion this project charges for everywhere else.
//!
//! # The declared softcap is a face, and this station proves it
//!
//! `config.json` declares `final_logit_softcapping = 30.0`, and `30·tanh(x/30)` is **strictly
//! monotone**. A monotone map cannot move any receiver that reads an ORDER — and an order is what
//! crosses a frame where a magnitude does not. So the softcap is not an occurrence in the diagram;
//! it is applied here as the receiver face it is, and the block is required to be **identical** with
//! and without it. If it moves, this reading is wrong and the station says so.
//!
//! ```text
//! cargo run --release -q -p holonic-engine \
//!   --example the_emission_is_a_section_and_the_answer_is_a_block -- /home/b/models/gemma-4-E4B-it
//! ```

#[path = "phoenix/site.rs"]
mod site;

use std::collections::BTreeMap;

use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::exact_value::ieee754::round_into_bfloat16;
use holonic_engine::exact_value::CertifiedSeries;
use holonic_engine::interaction::OccurrencePort;
use holonic_engine::ported_reference::realize;
use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;
use site::{found_reaching, Reach, ResidentSourceCarrier, BAND_POPULATION, BASE, CAUSED};

/// The declared cap, exactly. `config.json` says `final_logit_softcapping = 30.0`.
const SOFTCAP: i64 = 30;

/// **A declared aperture on the softcap reading, and it checks its own boundary.**
///
/// The cap is strictly monotone, so only the widest coordinates can be in the capped block. Turning
/// all 262,144 through an exact series takes minutes on one core and returns nothing the top of the
/// section does not already decide — the first form of this station did exactly that and had to be
/// stopped. So the cap is taken over the widest `SHOULDER` coordinates, and the one **past** the
/// shoulder is taken too and required to fall outside the block. If it does not, the aperture is too
/// narrow and the station refuses instead of reporting a block.
const SHOULDER: usize = 4096;

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
    println!("PHOENIX STATION SEVEN — THE EMISSION IS A SECTION, AND THE ANSWER IS A BLOCK");
    println!();
    println!("  resident chart                    {}", chart.device_name());

    let (site, container, file) =
        match found_reaching(&root, BASE, terms, None, Reach::ThroughEmission) {
            Ok(triple) => triple,
            Err(error) => {
                println!("  the founding refused: {error}");
                std::process::exit(1);
            }
        };
    let fronts = site.complex.fronts().expect("fronts");
    println!();
    println!("  THE BODY");
    println!("    operations                      {}", site.program.operations.len());
    println!("    dependency span                 {} fronts", fronts.len());
    println!("    stored populations NAMED        {}", site.populations.len());
    println!("    the head is tied                embed_tokens read the other way; no lm_head exists");

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
            println!("  THE BODY REFUSED: {error}");
            println!("  That is the station's return. Nothing is claimed.");
            std::process::exit(1);
        }
    };
    let sections: Vec<Vec<Rat>> = site
        .returns
        .iter()
        .map(|event| receipt.carried[&OccurrencePort::output(*event, 0)].clone())
        .collect();
    println!();
    println!("  THE ILLICIAL POTENTIAL SECTION");
    println!("    positions returned              {}", sections.len());
    println!("    width                           {}", sections[0].len());
    println!("    wall clock                      {:?}", clock.elapsed());
    println!("    mounts served from residency    {} — an invariant operand is uploaded ONCE", carrier.reused);
    println!("    entries retained below the frame {}", carrier.below_the_frame);
    println!("    exact work                      {:?}", receipt.work);

    // -----------------------------------------------------------------------------------------
    // THE BLOCK. A declared receiver, and no pick.
    // -----------------------------------------------------------------------------------------
    let cap = Rat::from_integer(BigInt::from(SOFTCAP));
    let block_of = |section: &[Rat]| -> (Vec<usize>, Rat) {
        let widest = section.iter().max().cloned().unwrap_or_else(Rat::zero);
        // **The declared receiver is the stored species.** Two coordinates are within its tolerance
        // exactly when no word in its family separates them — which is `receiver_exact_compression`'s
        // collapsed-pair relation at the grain the body actually carries.
        let mark = round_into_bfloat16(&widest).map(|(word, _)| word).ok();
        let block: Vec<usize> = section
            .iter()
            .enumerate()
            .filter(|(_, value)| round_into_bfloat16(value).map(|(word, _)| word).ok() == mark)
            .map(|(at, _)| at)
            .collect();
        (block, widest)
    };
    let capped = |value: &Rat| -> Rat {
        let turned = CertifiedSeries::hyperbolic_tangent_enclosure(&(value / &cap), terms)
            .expect("the declared cap's turn");
        &cap * (&turned.lower + &turned.upper) / Rat::from_integer(BigInt::from(2))
    };

    println!();
    println!("  THE BLOCK — the coordinates the declared receiver cannot separate from the widest");
    let mut softcap_moved_a_block = false;
    let mut shoulder_held = true;
    for (position, section) in sections.iter().enumerate() {
        let (block, widest) = block_of(section);
        // The declared shoulder: the widest `SHOULDER` coordinates, and the one past them.
        let mut ranked: Vec<usize> = (0..section.len()).collect();
        ranked.sort_by(|a, b| section[*b].cmp(&section[*a]));
        let shoulder: Vec<usize> = ranked.iter().take(SHOULDER).copied().collect();
        let past = ranked.get(SHOULDER).copied();

        let turned: Vec<Rat> = shoulder.iter().map(|at| capped(&section[*at])).collect();
        let mark = turned
            .iter()
            .max()
            .and_then(|widest| round_into_bfloat16(widest).map(|(word, _)| word).ok());
        let capped_block: Vec<usize> = shoulder
            .iter()
            .zip(&turned)
            .filter(|(_, value)| round_into_bfloat16(value).map(|(word, _)| word).ok() == mark)
            .map(|(at, _)| *at)
            .collect();
        let mut sorted_block = capped_block.clone();
        sorted_block.sort_unstable();
        let moved = block != sorted_block;
        softcap_moved_a_block |= moved;

        // **THE BOUNDARY.** The coordinate just past the shoulder must fall outside the block, or
        // the aperture decided the answer instead of the material.
        let boundary = past.map(|at| {
            round_into_bfloat16(&capped(&section[at]))
                .map(|(word, _)| word)
                .ok()
                != mark
        });
        shoulder_held &= boundary.unwrap_or(false);

        let widest_text = widest.to_string();
        println!(
            "    position {position} (symbol {})   block {} of {}   widest {}",
            CAUSED[position],
            block.len(),
            section.len(),
            if widest_text.len() > 30 { format!("{}…", &widest_text[..30]) } else { widest_text }
        );
        println!(
            "        through the declared softcap over the widest {SHOULDER}: block {}   the SAME block {}",
            sorted_block.len(),
            !moved
        );
        println!(
            "        the coordinate past the shoulder falls outside it   {}",
            boundary.map(|held| held.to_string()).unwrap_or_else(|| "no such coordinate".to_owned())
        );
        let shown: Vec<usize> = block.iter().take(8).copied().collect();
        println!("        coordinates {shown:?}{}", if block.len() > 8 { " …" } else { "" });
    }

    // The order face, checked directly on a declared sample rather than inferred from the block.
    let sample: Vec<usize> = (0..64).map(|k| k * 4093 % sections[0].len()).collect();
    let mut order_moved = 0usize;
    for section in &sections {
        for pair in sample.windows(2) {
            let (a, b) = (&section[pair[0]], &section[pair[1]]);
            if a.cmp(b) != capped(a).cmp(&capped(b)) {
                order_moved += 1;
            }
        }
    }
    println!();
    println!("  THE ORDER FACE, checked pair by pair on a declared sample");
    println!("    pairs compared                  {}", sample.len().saturating_sub(1) * sections.len());
    println!("    pairs the softcap reordered     {order_moved}");

    println!();
    println!("THE STATION'S VERDICT");
    println!();
    let held = !softcap_moved_a_block && order_moved == 0 && shoulder_held;
    println!("  the softcap is a face and not a transport   {held}");
    println!("  the declared shoulder held its own boundary {shoulder_held}");
    println!();
    println!("  The body conducts end to end and returns the illicial potential section whole,");
    println!("  262,144 coordinates per position. Nothing picks. The reading is a BLOCK under a");
    println!("  declared receiver — the stored species the body actually carries — and a block of");
    println!("  one is as real an answer as a block of nine.");
    println!();
    println!("  The declared `final_logit_softcapping` is applied as the receiver face it is rather");
    println!("  than as an occurrence, and the claim that licenses that is checked twice: the block");
    println!("  is identical through it, and it reorders no pair of a declared sample. A strictly");
    println!("  monotone map cannot move an order, and an order is what crosses a frame.");
    println!();
    println!("  WHAT THIS IS NOT. One layer of forty-two, so the section is what a one-layer body");
    println!("  emits and not what Gemma emits. The four per-layer populations remain unbound and");
    println!("  unguessed. No agreement with the source is claimed, sought, or measured here.");
    println!();
    println!("  CONSTRUCTION_STATE is untouched.");
    if !held {
        std::process::exit(1);
    }
}

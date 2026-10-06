//! Continuing physical reception on the notebook's already admitted KnownTruth chart.
//!
//! `executed physical-receive <A|B|one> <count> <aperture> <out> <pin> <terrain>=<seed>…`
//! is a prequential law diagnostic, with no unseen or useful-language claim. Each blind damaged
//! section is received on the contemporary material and preceding physical carry. Its whole
//! receipt is published before a comparison observes only its intact stations. The next section
//! consumes the successor. No pair location, authored relation, reference repair or erased target
//! enters the receiver. The identity chart is the terrain owner's KnownTruth chart; arbitrary
//! external bytes still require their founded encoding and admitted clock/decoder join.
//!
//! The source frame is the same declared station origin for each separate section. The physical
//! field's pump clock continues through ReceptionCarry; this is not a claim that arbitrary erased
//! selective advances have been inferred. The command requires its own measured, committed pin;
//! no historical physical-repair pin licenses this changed law.

use super::*;
use holonics::hnn::physical::{PhysicalLearning, PhysicalObservation, PhysicalResident};
use holonics::hnn::prediction::DamagedSection;
use holonics::hnn::word::WordOpening;
use std::io::Write;

pub(super) fn run(
    damage_name: &str,
    count: usize,
    aperture: usize,
    out: &str,
    terrains: &[String],
    pin: &exterior::Pin,
) {
    let bound = pin
        .unit_bound_ms()
        .expect("physical-receive requires a measured reception bound");
    let erased = if damage_name == "one" {
        vec![1]
    } else {
        repair_loop::damage(damage_name)
    };
    let declared = Declared {
        alphabet: repair_loop::CLASSES,
        ..order_declared()
    };
    let field = declare(&declared);
    let shape = Declared {
        request: repair_loop::OPENING,
        stations: repair_loop::STATIONS,
        ..declared
    };
    let current = Current::at_rest(&field);
    let material = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).expect("declared material");
    let mut resident = PhysicalResident::new(&field, material, current, WordOpening::Rest);
    let receiver = ReceiverDeclaration {
        ring: 0,
        aperture,
        ..field.receivers()[0].clone()
    };
    // This comparison is a whole declared section, so its native receiving clock must read it all.
    assert_eq!(
        aperture,
        shape.request + shape.stations,
        "comparison needs the whole section"
    );
    #[allow(clippy::disallowed_methods)] // exterior output, never the retained machine state
    let mut output = std::fs::File::create(out).expect("the requested output file");
    for spec in terrains {
        let (terrain, seed) = spec.split_once('=').expect("<terrain>=<seed>");
        let seed = seed.parse().expect("a seed");
        let encoded = executed_loop::terrain_encoded(terrain, &shape, &field, seed, count);
        for (index, observed) in encoded.into_iter().enumerate() {
            let started = Instant::now();
            let damaged = DamagedSection::damage(&observed, &erased).expect("declared damage");
            let compared = damaged.placed().iter().map(Option::is_some).collect();
            let received = resident
                .receive(&damaged, &receiver, |blind| {
                    // All classes at erased stations are absent from the blind forward constructor.
                    // The same whole blind output is shown and flushed before this observation.
                    let whole = format!("{terrain}/{seed} section {index}: blind {blind:?}\n");
                    print!("{whole}");
                    std::io::stdout().flush().expect("publish blind output");
                    output
                        .write_all(whole.as_bytes())
                        .expect("write whole blind output");
                    output.flush().expect("publish whole blind output");
                    Some(PhysicalObservation {
                        observed,
                        compared,
                        learning: PhysicalLearning::Receiving,
                    })
                })
                .expect("the admitted physical reception");
            let receipt = format!(
                "comparison on intact stations only: {:?}; contemporary commit {}; physical carry at {}; elapsed {} ms\n",
                received.comparison,
                resident.constitution().commit(),
                received.prediction.carry.ticks,
                started.elapsed().as_millis(),
            );
            print!("{receipt}");
            output
                .write_all(receipt.as_bytes())
                .expect("write comparison receipt");
            output.flush().expect("publish comparison receipt");
            if started.elapsed().as_millis() > bound {
                println!(
                    "INCOMPLETE: reception exceeded measured fixed bound {bound} ms; no later section read"
                );
                return;
            }
        }
    }
}

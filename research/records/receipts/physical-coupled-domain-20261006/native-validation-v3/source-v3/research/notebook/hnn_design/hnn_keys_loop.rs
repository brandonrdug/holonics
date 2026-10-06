//! **Keys become material: the pair menu read along the training passage, and the located pair's
//! deposit** (THE_REBUILD U6 step 1, lane B; the
//! [record](../../records/2026-10-05_LOCATED_KEYS_BECOME_THE_SOURCE_PORTS_PAIR_COMPONENT.md); #73,
//! #148, #63).
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_prediction -- executed keys <terrain> <training seed> <count> <out>
//! ```
//!
//! [definition; agent-inferred, October 5] **`executed keys`** reads the training passage in its
//! order, one observation a seen station (the request's cells are context, the stations are the
//! readings), each read against every earlier cell of its passage at every distance of the span
//! (`hnn::keys::station_pairs`). The turn machine's menus (`hnn::keys::PairLocation`) print their
//! survivors at every observation: the read distances, those alive, and the located pair once the
//! survivors are one distance or the windings of the least (`hnn::keys`, "A class of windings is one
//! key"). The machine's count is the first observation from which the pair stays located to the
//! passage's end (and the first at which it locks at all). At the passage's end, the aeon's boundary
//! where the retention quotient is taken, the machine deposits the pair located there on both
//! openings (`hnn::executed::pair_deposit`, against the declared prior `E₀`), and writes each
//! complete continuing state to `<out>.lossless` and `<out>.founded` for `executed evaluate` to read.
//! [agent-inferred, October 5; the regressions'
//! [record](../../records/2026-10-05_THE_REGRESSIONS_LOCATE_THE_LEAST_WINDING_AND_ARE_READ_BY_THE_PAIR_RELEASE.md)
//! §3] The boundary's pair, not the first lock's: a key whose map is still growing at its first lock
//! (on the alternation's training passage the windings of distance 2 publish the identity on two
//! classes at observation 16, three at 18 and four at 33, after a constant first request located
//! distance 1 on one class) would leave the classes it reaches later at their prior. On order-2 the
//! two are one pair (located at 16 and held to the end), so its deposit is unchanged. Only the seen
//! passage enters: the terrain's request and its stations, read in order; nothing of the validation
//! or confirmation sets, of the declared reference family or of the rule is read.

use super::*;
use holonics::hnn::executed::pair_deposit;
use holonics::hnn::keys::{LocatedPair, PairLocation, station_pairs};

use executed_loop::{founded_opening, terrain_encoded, terrain_pairs, write_state};

/// **`executed keys`** (module header).
pub(super) fn keys(terrain: &str, seed: u64, count: usize, out: &str) {
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let ring = engine.refinement.ring();
    let field = &engine.field;
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let passages = terrain_encoded(terrain, &declared, field, seed, count);
    let mut location = PairLocation::open(field, ring);
    let mut first_lock: Option<(u64, LocatedPair)> = None;
    let mut stable: Option<(u64, LocatedPair)> = None;
    // One map class: every alive read distance publishes, and all publish one map (aliases at
    // several distances reading one relation); the first observation from which it holds to the end.
    let mut one_map: Option<(u64, Vec<usize>)> = None;
    let mut curve = String::new();
    for (index, ((request, _), passage)) in pairs.iter().zip(&passages).enumerate() {
        let readings = station_pairs(field, ring, passage, request.len()).expect("the pair menu");
        for (station, observation) in readings.iter().enumerate() {
            location.observe(observation);
            let survivors = location.survivors();
            let located = survivors.located();
            let k = survivors.observations;
            if first_lock.is_none() {
                if let Some(pair) = &located {
                    first_lock = Some((k, pair.clone()));
                }
            }
            match (&located, &stable) {
                (Some(pair), None) => stable = Some((k, pair.clone())),
                (Some(pair), Some((_, known))) if pair != known => stable = Some((k, pair.clone())),
                (None, Some(_)) => stable = None,
                _ => {}
            }
            let maps: Vec<_> = survivors.alive.iter().map(|(_, reading)| reading.map.clone()).collect();
            let agreeing = !maps.is_empty()
                && maps.iter().all(|map| map.is_some() && *map == maps[0]);
            match (agreeing, &one_map) {
                (true, None) => one_map = Some((k, survivors.distances())),
                (true, Some((_, known))) if *known != survivors.distances() => {
                    one_map = Some((k, survivors.distances()))
                }
                (false, Some(_)) => one_map = None,
                _ => {}
            }
            let shown: Vec<String> = survivors
                .alive
                .iter()
                .take(6)
                .map(|(offset, reading)| {
                    format!(
                        "δ {offset}: {} turns, cycle {:?}, map {:?}",
                        reading.turns.len(),
                        reading.cycle,
                        reading.map
                    )
                })
                .collect();
            curve.push_str(&format!(
                "observation {k} (request {index}, station {station}): read {}, alive {} [{}]{}\n",
                survivors.read,
                survivors.alive.len(),
                shown.join("; "),
                match &located {
                    Some(pair) => format!(" located δ {} map {:?}", pair.offset, pair.map),
                    None => String::new(),
                }
            ));
        }
    }
    #[allow(clippy::disallowed_methods)]
    std::fs::write(format!("{out}.curve"), &curve).expect("write the curve");
    let stations = declared.stations as u64;
    let units = |k: u64| format!("{k} observations ({} requests plus {} stations)", k / stations, k % stations);
    println!(
        "keys on {terrain}, seed {seed}, {count} requests: {} observations read",
        location.survivors().observations
    );
    match &first_lock {
        Some((k, pair)) => println!(
            "  first lock at {}: δ {}, map {:?}, cycle {}, turns {:?}",
            units(*k),
            pair.offset,
            pair.map,
            pair.cycle,
            pair.turns
        ),
        None => println!("  no lock in the passage"),
    }
    match &stable {
        Some((k, pair)) => println!(
            "  located from {} to the passage's end: δ {}, map {:?}",
            units(*k),
            pair.offset,
            pair.map
        ),
        None => {
            let survivors = location.survivors();
            println!(
                "  not located at the passage's end: {} distances alive {:?}",
                survivors.alive.len(),
                survivors.distances()
            );
        }
    }
    match &one_map {
        Some((k, distances)) => println!(
            "  one map class from {} to the passage's end: the distances {distances:?} each publish one map",
            units(*k)
        ),
        None => println!("  no single map class at the passage's end"),
    }
    let Some((k, pair)) = stable else {
        println!("executed keys: {} ms; resident {}", clock.elapsed().as_millis(), resident());
        return;
    };
    if first_lock.as_ref().is_some_and(|(_, first)| first != &pair) {
        println!("  the first lock's pair is not the pair located at the passage's end");
    }
    let prior = engine.theta.source_port(ring).expect("the opening's source port").clone();
    for (label, opening) in [("lossless", engine.theta.clone()), ("founded", founded_opening(&engine))] {
        let started = Instant::now();
        match pair_deposit(field, &opening, &prior, ring, &pair) {
            Ok((theta, deposit)) => {
                println!(
                    "  deposit on the {label} opening at observation {k}: δ {}, classes {:?}, slip {} → {}, certified step η {} (a {}, C {}, c {}, decrease {}), consumer (E − B) T = U B {}, storage growth {}, largest entry {}, bits {}, transport {}; {} ms",
                    deposit.offset,
                    deposit.classes,
                    deposit.slip_before,
                    deposit.slip_after,
                    deposit.certificate.step,
                    deposit.certificate.alignment,
                    deposit.certificate.curvature,
                    deposit.certificate.covector,
                    deposit.certificate.decrease(),
                    if deposit.consumer { "holds" } else { "does not hold" },
                    deposit.source.storage_growth,
                    deposit.source.largest,
                    deposit.source.bits,
                    theta.transport(ring),
                    started.elapsed().as_millis()
                );
                #[allow(clippy::disallowed_methods)]
                std::fs::write(format!("{out}.{label}"), write_state(&theta, ring))
                    .expect("write the state");
            }
            Err(refusal) => println!("  deposit on the {label} opening refused: {refusal}"),
        }
    }
    println!("executed keys: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

/// [measured-diagnostic; agent-inferred, October 5; a representation probe, never a learning law]
/// **`executed keys-probe <terrain> <training seed> <count> <scale> <out>`**: locates the pair on the
/// training passage as `executed keys` does, and writes, on both openings, the source port whose
/// located classes are the plugboard's placement on the ring with the pair component,
/// `E e_x = s P^(S(x)) (e_0 + e_(δ − c))` (`S(p₀) = 0` at the least menu port and `c` the least
/// surviving turn: the gauge-fixing convention), every other class at its prior. It reads whether
/// the release consumes a key whose classes carry equal material and coincide exactly with their
/// antecedents (`E T = P^c E` and `(E − E_S) T = P^δ E_S` on the menu's classes). Mounted with
/// `with_ports`: a probe of the representation, not a deposition.
pub(super) fn keys_probe(terrain: &str, seed: u64, count: usize, scale: &str, out: &str) {
    let declared = order_declared();
    let engine = Engine::new(declared);
    let ring = engine.refinement.ring();
    let field = &engine.field;
    let scale: Rat = scale.parse().expect("a rational scale");
    let passages = terrain_encoded(terrain, &declared, field, seed, count);
    let mut location = PairLocation::open(field, ring);
    let mut located = None;
    for passage in &passages {
        for observation in station_pairs(field, ring, passage, declared.request).expect("the pair menu") {
            location.observe(&observation);
            if located.is_none() {
                located = location.survivors().located().map(|pair| (location.survivors().observations, pair));
            }
        }
    }
    let Some((k, pair)) = located else {
        println!("keys-probe: no lock");
        return;
    };
    let geometry = field.ring(ring);
    let period = geometry.period();
    let turn = pair.turns[0];
    // The plugboard's images, gauge-fixed at the least menu port: S(f^j(p₀)) = j c.
    let start = pair.map[0].0;
    let mut images = vec![None; field.alphabet()];
    let (mut port, mut at) = (start, 0u64);
    loop {
        images[port] = Some(at);
        port = pair.map.iter().find(|(y, _)| *y == port).expect("a cycle").1;
        at = (at + turn) % period;
        if port == start {
            break;
        }
    }
    let width = geometry.width();
    let mut wave = vec![Rat::zero(); width];
    wave[0] = scale.clone();
    let lag = (pair.offset as u64 + period - turn) % period;
    wave[2 * lag as usize] += &scale;
    let prior = engine.theta.source_port(ring).expect("the prior").clone();
    let rows: Vec<Vec<Rat>> = (0..width)
        .map(|row| {
            (0..field.alphabet())
                .map(|class| match images[class] {
                    Some(s) => geometry.rotate(&wave, &num_bigint::BigInt::from(s))[row].clone(),
                    None => prior.get(row, class).expect("in range").clone(),
                })
                .collect()
        })
        .collect();
    let port = ExactRatMatrix::shaped(width, field.alphabet(), rows).expect("the port");
    println!(
        "keys-probe at observation {k}: δ {}, turn {turn}, images {images:?}, wave nodes 0 and {lag}, scale {scale}",
        pair.offset
    );
    for (label, opening) in [("lossless", engine.theta.clone()), ("founded", founded_opening(&engine))] {
        let theta = opening.with_ports(ring, None, Some(port.clone()), None).expect("the probe's port");
        #[allow(clippy::disallowed_methods)]
        std::fs::write(format!("{out}.{label}"), write_state(&theta, ring)).expect("write the state");
    }
}

/// [measured-diagnostic; agent-inferred, October 5; lane C's
/// [record](../../records/2026-10-05_THE_RELEASE_READS_THE_LOCATED_PAIR_ON_EQUAL_MATERIAL.md) §3;
/// never a law] **`executed pair-members <terrain> <seed> <count> <state>`**: on each request, along
/// the target's trajectory (each station's target placed once the station is read, the forced
/// release's reading context, never a commit), every candidate's pair storage and its own column
/// alone (`BankPlacement::pair_storage`), read by every member of the bank, each member's growth's
/// lower end at the grain `1/16`, and the candidate's gain on equal material (`prediction::gain`,
/// the joined bank's determinant over the members, its lower end at the grain `1/16`; the joint
/// gain's record, `2026-10-05_THE_PAIR_GAIN_IS_THE_JOINED_BANKS_LOG_DETERMINANT.md`). It reads why
/// the members decide together: a candidate that fits the closed contact gains at every member
/// where its storage carries the contact's line, the antecedent's copy as a wrong class pays on the
/// members where the contact's distance half-turns its line what it gains on the others, and a
/// member at which every candidate's two storages turn alike is neutral.
pub(super) fn pair_members(terrain: &str, seed: u64, count: usize, state: &str) {
    use holonics::hnn::prediction::BankPlacement;
    use holonics::hnn::ring::turn;
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let theta = executed_loop::mount(&engine.theta, state);
    let at = |x: &Rat| executed_loop::cell(&ExactInterval { lower: x.clone(), upper: x.clone() }, 16);
    let passages = terrain_encoded(terrain, &declared, &engine.field, seed, count);
    for ((request, target), passage) in terrain_pairs(terrain, &declared, seed, count).iter().zip(&passages) {
        let (current, moment) =
            ingest(&engine.field, &passage.part(0..request.len()).expect("the request"));
        let placement =
            BankPlacement::of(&engine.field, &theta, &current, &moment, &engine.refinement).expect("the placement");
        println!(
            "request tail {:?} | target {target:?} | closed contacts {:?}",
            &request[request.len() - 2..],
            placement.contacts()
        );
        let mut cells: Vec<Option<usize>> = vec![None; declared.stations];
        for station in 0..declared.stations {
            println!("  station {station}:");
            for class in 0..declared.alphabet {
                match placement.pair_storage(station, class, &cells) {
                    Some((pair, alone)) => {
                        let pair = bank.read_turn(&turn(&pair), BANK_GRAIN).expect("a reading");
                        let alone = bank.read_turn(&turn(&alone), BANK_GRAIN).expect("a reading");
                        let joint = holonics::hnn::prediction::gain(&pair, &alone).expect("a gain");
                        println!(
                            "    class {class}: pair {:?} alone {:?} joint gain ≥ {}",
                            pair.members.iter().map(|m| at(&m.lower)).collect::<Vec<_>>(),
                            alone.members.iter().map(|m| at(&m.lower)).collect::<Vec<_>>(),
                            at(&joint.lower)
                        );
                    }
                    None => println!("    class {class}: no closed contact joins a placed crossing"),
                }
            }
            cells[station] = Some(target[station]);
        }
    }
}

// -------------------------------------------------------------------------------------------
// the same path on text: the refusal

/// [historical; retired October 5 with THE_MACHINE guard 9 at the field's entries] **`executed
/// text`** ran lane B's key location and lane C's release on a text cut through the byte chart
/// (`|A| = 257` on the order-2 field's ports `code mod 60`; the
/// [record](../../records/2026-10-05_THE_SAME_PATH_ON_TEXT_KEY_LOCATION_AND_THE_RELEASE_ON_THE_BYTE_CHART.md)):
/// the residue chart guard 9 deleted. Its source is at
/// [`f91666c0`](https://github.com/brandonrdug/holonics/blob/f91666c0/research/notebook/hnn_design/hnn_keys_loop.rs).
/// [definition; agent-inferred, October 5; guards 9, 21 and 22] The mode still takes its committed
/// pin and reads the cut only through `exterior::read_cut`; its result is guard 9's refusal, since a
/// byte passage enters the field only as an `Encoded` built from a founded encoding, and none is
/// founded for bytes.
pub(super) fn text(cut: &str) {
    let exterior::Cut { population, .. } = exterior::read_cut(cut);
    println!(
        "executed text: the cut's {population} bytes; refused: {} (THE_MACHINE guard 9: a byte \
         passage enters the field only through a founded encoding, and no encoding of bytes is founded)",
        holonics::hnn::EncodingError::Unencoded
    );
}

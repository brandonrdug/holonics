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

use executed_loop::{founded_opening, terrain_pairs, write_state};

/// **`executed keys`** (module header).
pub(super) fn keys(terrain: &str, seed: u64, count: usize, out: &str) {
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let ring = engine.refinement.ring();
    let field = &engine.field;
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let mut location = PairLocation::open(field, ring);
    let mut first_lock: Option<(u64, LocatedPair)> = None;
    let mut stable: Option<(u64, LocatedPair)> = None;
    // One map class: every alive read distance publishes, and all publish one map (aliases at
    // several distances reading one relation); the first observation from which it holds to the end.
    let mut one_map: Option<(u64, Vec<usize>)> = None;
    let mut curve = String::new();
    for (index, (request, target)) in pairs.iter().enumerate() {
        let mut passage = request.clone();
        passage.extend(target);
        let readings = station_pairs(field, ring, &passage, request.len()).expect("the pair menu");
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
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let mut location = PairLocation::open(field, ring);
    let mut located = None;
    for (request, target) in &pairs {
        let mut passage = request.clone();
        passage.extend(target);
        for observation in station_pairs(field, ring, &passage, request.len()).expect("the pair menu") {
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
/// lower end at the grain `1/16`, and the candidate's gain on equal material (the least member's
/// ratio). It reads why the least member decides: a candidate that fits the closed contact gains at
/// every member, the antecedent's copy only at the members where the contact's distance carries
/// its line to itself.
pub(super) fn pair_members(terrain: &str, seed: u64, count: usize, state: &str) {
    use holonics::hnn::prediction::BankPlacement;
    use holonics::hnn::ring::turn;
    let declared = order_declared();
    let engine = Engine::new(declared);
    let ring = engine.refinement.ring();
    let bank = bank_of(declared.period, &bank_strength());
    let theta = executed_loop::mount(&engine.theta, ring, state);
    let at = |x: &Rat| executed_loop::cell(&ExactInterval { lower: x.clone(), upper: x.clone() }, 16);
    for (request, target) in &terrain_pairs(terrain, &declared, seed, count) {
        let (current, moment) = ingest(&engine.field, request);
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
                        let least = pair
                            .members
                            .iter()
                            .zip(&alone.members)
                            .map(|(p, a)| &p.lower / &a.upper)
                            .min()
                            .expect("a member");
                        println!(
                            "    class {class}: pair {:?} alone {:?} least ratio ≥ {}",
                            pair.members.iter().map(|m| at(&m.lower)).collect::<Vec<_>>(),
                            alone.members.iter().map(|m| at(&m.lower)).collect::<Vec<_>>(),
                            at(&least)
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
// the same path on text

/// [definition; agent-inferred, October 5; the
/// [record](../../records/2026-10-05_THE_SAME_PATH_ON_TEXT_KEY_LOCATION_AND_THE_RELEASE_ON_THE_BYTE_CHART.md)
/// §0's pins] **The text pins**: the training passage is the cut's first `128` windows of
/// `n + m = 48` bytes (a request of `40` cells and its section of `8` stations, the order-2 terrain's
/// training shape: `1,024` observations); the requests are `16` windows of `48` bytes in the cut's
/// held-out range, the `i`-th at `start + i·⌊(end − start)/16⌋`.
const TEXT_TRAINING_WINDOWS: usize = 128;
const TEXT_REQUESTS: usize = 16;

/// [definition; agent-inferred, October 5] **The text declaration**: the order-2 field, refinement,
/// bank and opening unchanged ([`order_declared`]), with the exterior chart the byte chart:
/// `|A| = 257`, the bytes `0 … 255` and the termination `256`. The ring's ports are its residue chart
/// `code mod 60` (guard 9), so a port holds four or five bytes.
fn text_declared() -> Declared {
    Declared {
        alphabet: 257,
        ..order_declared()
    }
}

/// [measured; agent-inferred, October 5; the record above] **`executed text <cut> <out dir> <dev|run>`**:
/// lane B's key location and lane C's release, unchanged, on a text cut through the byte chart
/// ([`text_declared`]). The training passage is read as `executed keys` reads a terrain's (each window
/// a request and its section, one observation a station, read against every earlier cell of its
/// window at every distance; `hnn::keys::{station_pairs, PairLocation}`), and each distance's menu
/// is followed to the observation at which it fails, with the edges it had read. Beside it, a
/// terrain-side reading only: the same edges on the bytes themselves (one `TurnMenu` a distance on
/// the byte chart's `256` ports), to separate the residue chart's fold from the passage's own
/// relation. If a pair locates at a first lock, it is deposited on both openings
/// (`hnn::executed::pair_deposit`) and the release reads the deposits; otherwise the release reads the
/// two openings. The release is `hnn::prediction::generate_by_bank`, one per request, read whole.
/// `dev` reads one development window (the one after the training passage) on each state, for the
/// projection; `run` reads the pinned requests. Stdout carries counts only; every byte (the
/// training passage, each request, its truth and each state's release) is written to `<out dir>`,
/// which must be a private directory (`.local/`).
#[allow(clippy::disallowed_methods)]
pub(super) fn text(cut: &str, out: &str, which: &str) {
    use holonics::compression::keys::TurnMenu;
    use rayon::prelude::*;
    use std::fmt::Write as _;
    let clock = Instant::now();
    let declared = text_declared();
    let engine = Engine::new(declared);
    let ring = engine.refinement.ring();
    let field = &engine.field;
    let period = usize::try_from(field.ring(ring).period()).expect("a period fits");
    let (bytes, population, held) = exterior::read_cut(cut);
    let window = declared.request + declared.stations;
    let pair_at = |start: usize| -> (Vec<usize>, Vec<usize>) {
        let cells: Vec<usize> = bytes[start..start + window].iter().map(|&b| usize::from(b)).collect();
        let (request, target) = cells.split_at(declared.request);
        (request.to_vec(), target.to_vec())
    };
    assert!(TEXT_TRAINING_WINDOWS * window <= held.start, "the training passage lies before the held-out range");
    let training: Vec<_> = (0..TEXT_TRAINING_WINDOWS).map(|i| pair_at(i * window)).collect();
    let stride = (held.end - held.start) / TEXT_REQUESTS;
    assert!(stride >= window, "the requests are disjoint");
    let (starts, label): (Vec<usize>, &str) = match which {
        "dev" => (vec![TEXT_TRAINING_WINDOWS * window], "development window"),
        "run" => ((0..TEXT_REQUESTS).map(|i| held.start + i * stride).collect(), "pinned requests"),
        _ => panic!("executed text <cut> <out dir> <dev|run>"),
    };
    let requests: Vec<_> = starts.iter().map(|&start| pair_at(start)).collect();
    std::fs::create_dir_all(out).expect("the private directory");
    std::fs::write(format!("{out}/training.bin"), &bytes[..TEXT_TRAINING_WINDOWS * window]).expect("write");
    for (i, (request, target)) in requests.iter().enumerate() {
        let as_bytes = |cells: &[usize]| cells.iter().map(|&c| u8::try_from(c).expect("a byte")).collect::<Vec<u8>>();
        std::fs::write(format!("{out}/request_{i}.bin"), as_bytes(request)).expect("write");
        std::fs::write(format!("{out}/truth_{i}.bin"), as_bytes(target)).expect("write");
    }
    println!(
        "executed text ({which}): the cut {population} bytes, held-out range {}..{}; training passage bytes 0..{} ({} windows of {window}, {} observations); {} {label} of {window} bytes at stride {stride} from {}; d = {period}, |A| = {}, ports code mod {period}",
        held.start,
        held.end,
        TEXT_TRAINING_WINDOWS * window,
        TEXT_TRAINING_WINDOWS,
        TEXT_TRAINING_WINDOWS * declared.stations,
        requests.len(),
        starts[0],
        declared.alphabet
    );

    // Key location on the field's ports, and the terrain-side reading on the bytes.
    let located_clock = Instant::now();
    let mut location = PairLocation::open(field, ring);
    let mut on_bytes: Vec<TurnMenu> = (1..period).map(|_| TurnMenu::open(256)).collect();
    // Per distance: the observation at which its menu failed and the edges it had read then.
    let mut died: Vec<Option<(u64, u64)>> = vec![None; period];
    let mut died_bytes: Vec<Option<(u64, u64)>> = vec![None; period];
    let mut first_lock: Option<(u64, LocatedPair)> = None;
    let mut curve = String::new();
    let mut emptied: Option<u64> = None;
    let mut emptied_bytes: Option<u64> = None;
    for (request, target) in &training {
        let mut passage = request.clone();
        passage.extend(target);
        let readings = station_pairs(field, ring, &passage, request.len()).expect("the pair menu");
        for (station, observation) in readings.iter().enumerate() {
            location.observe(observation);
            let t = request.len() + station;
            for reading in observation {
                on_bytes[reading.offset - 1].observe(passage[t - reading.offset], passage[t]);
            }
            let k = location.survivors().observations;
            for offset in 1..period {
                let menu = location.menu(offset);
                if died[offset].is_none() && menu.edges() > 0 && !menu.alive() {
                    died[offset] = Some((k, menu.edges()));
                }
                let menu = &on_bytes[offset - 1];
                if died_bytes[offset].is_none() && menu.edges() > 0 && !menu.alive() {
                    died_bytes[offset] = Some((k, menu.edges()));
                }
            }
            let survivors = location.survivors();
            if first_lock.is_none() {
                if let Some(pair) = survivors.located() {
                    first_lock = Some((k, pair));
                }
            }
            let alive_bytes = on_bytes.iter().filter(|m| m.edges() > 0 && m.alive()).count();
            if emptied.is_none() && survivors.alive.is_empty() {
                emptied = Some(k);
            }
            if emptied_bytes.is_none() && alive_bytes == 0 {
                emptied_bytes = Some(k);
            }
            writeln!(
                curve,
                "observation {k}: ports read {}, alive {} {:?}; bytes read {}, alive {alive_bytes}",
                survivors.read,
                survivors.alive.len(),
                survivors.distances(),
                on_bytes.iter().filter(|m| m.edges() > 0).count(),
            )
            .unwrap();
        }
    }
    std::fs::write(format!("{out}/location.curve"), &curve).expect("write the curve");
    let survivors = location.survivors();
    println!(
        "  key location: {} observations, {} distances read, {} alive at the end; the fibre emptied at observation {}; {} ms",
        survivors.observations,
        survivors.read,
        survivors.alive.len(),
        emptied.map_or("never".to_string(), |k| k.to_string()),
        located_clock.elapsed().as_millis()
    );
    for (offset, reading) in &survivors.alive {
        println!(
            "    alive δ {offset}: {} turns, cycle {:?}, map {} ({} edges)",
            reading.turns.len(),
            reading.cycle,
            reading.map.as_ref().map_or("plural".to_string(), |m| format!("published on {} ports", m.len())),
            reading.edges
        );
    }
    let deaths = |died: &[Option<(u64, u64)>]| -> String {
        (1..period)
            .filter_map(|offset| died[offset].map(|(k, edges)| format!("{offset}:{k}/{edges}")))
            .collect::<Vec<_>>()
            .join(" ")
    };
    println!("  ports, δ:observation/edges at the menu's failure: {}", deaths(&died));
    println!(
        "  bytes (terrain-side), δ:observation/edges at the relation's failure: {}; every distance failed by observation {}",
        deaths(&died_bytes),
        emptied_bytes.map_or("never".to_string(), |k| k.to_string())
    );
    match &first_lock {
        Some((k, pair)) => println!("  first lock at observation {k}: δ {}, cycle {}, {} turns", pair.offset, pair.cycle, pair.turns.len()),
        None => println!("  no lock in the passage: no distance's menu survived alone with a published map"),
    }

    // The states: the located pair's deposits, or the two openings.
    let mut states: Vec<(String, Constitution)> = Vec::new();
    let openings = [("lossless", engine.theta.clone()), ("founded", founded_opening(&engine))];
    match &first_lock {
        Some((_, pair)) => {
            let prior = engine.theta.source_port(ring).expect("the opening's source port").clone();
            for (name, opening) in openings {
                match pair_deposit(field, &opening, &prior, ring, pair) {
                    Ok((theta, deposit)) => {
                        println!("  deposit on the {name} opening: slip {} → {}, η {}", deposit.slip_before, deposit.slip_after, deposit.certificate.step);
                        states.push((format!("keys-{name}"), theta));
                    }
                    Err(refusal) => {
                        println!("  deposit on the {name} opening refused: {refusal}; the release reads the opening");
                        states.push((name.to_string(), opening));
                    }
                }
            }
        }
        None => states.extend(openings.into_iter().map(|(name, theta)| (name.to_string(), theta))),
    }

    // The release: one per request on each state, read whole.
    let bank = bank_of(declared.period, &bank_strength());
    for (name, theta) in &states {
        let started = Instant::now();
        let generated: Vec<_> = requests
            .par_iter()
            .map(|(request, _)| {
                let at = Instant::now();
                let (current, moment) = ingest(field, request);
                let generation =
                    generate_by_bank(field, theta, &current, &moment, &engine.refinement, &bank, BANK_GRAIN);
                (generation, at.elapsed().as_millis())
            })
            .collect();
        let (mut released, mut held_count, mut refused, mut whole, mut right, mut tops_right) = (0, 0, 0, 0, 0, 0);
        let (mut emitted_bytes, mut terminated, mut uncertified) = (0, 0, 0);
        let mut by_station = vec![0usize; declared.stations];
        let mut sections = String::new();
        let mut times = Vec::new();
        for (i, ((_, target), (generation, ms))) in requests.iter().zip(&generated).enumerate() {
            times.push(*ms);
            let Ok(generation) = generation else {
                refused += 1;
                writeln!(sections, "request {i}: refused").unwrap();
                std::fs::write(format!("{out}/{name}_{i}.release"), b"").expect("write");
                continue;
            };
            let release = &generation.release;
            uncertified += usize::from(generation.uncertified.is_some());
            terminated += usize::from(release.terminated.is_some());
            for (j, (class, truth)) in release.classes.iter().zip(target).enumerate() {
                tops_right += usize::from(class == truth);
                if release.released() && j < release.emitted.len() && class == truth {
                    right += 1;
                    by_station[j] += 1;
                }
            }
            if release.released() {
                released += 1;
                emitted_bytes += release.emitted.len();
                whole += usize::from(release.emitted.len() == target.len() && release.emitted == *target);
            } else {
                held_count += 1;
            }
            let emitted: Vec<u8> = release.emitted.iter().map(|&c| u8::try_from(c).expect("a byte")).collect();
            std::fs::write(format!("{out}/{name}_{i}.release"), &emitted).expect("write");
            writeln!(
                sections,
                "request {i}: {} | classes {:?} | plural {:?} | terminated {:?} | locks {:?} | refinements {} | uncertified {:?} | {} ms",
                if release.released() { "released" } else { "held" },
                release.classes,
                release.plural,
                release.terminated,
                generation.locks,
                generation.refinements,
                generation.uncertified,
                ms
            )
            .unwrap();
        }
        std::fs::write(format!("{out}/{name}_sections.txt"), &sections).expect("write the sections");
        println!(
            "  release on {name} ({} requests): released {released}, held {held_count}, refused {refused}, refused certificates {uncertified}; whole sections {whole}; released bytes {emitted_bytes}, right {right} of {} by station {by_station:?}; reaching the termination {terminated}; top classes right (held included) {tops_right}; ms a request {times:?}; {} ms",
            requests.len(),
            requests.len() * declared.stations,
            started.elapsed().as_millis()
        );
    }
    println!("executed text: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

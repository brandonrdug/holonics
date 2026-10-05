//! **The first repair terrain: a damaged passage, its located pair, and the repair by reflection**
//! (THE_REBUILD U6, "The task is repair, not continuation"; the
//! [record](../../records/2026-10-05_REPAIR_BY_REFLECTION_THE_LOCATED_PAIR_RESTRICTS_THE_ERASED_CELLS_FROM_BOTH_SIDES.md),
//! whose §0 pins every declaration below; #73, #148, #63).
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_prediction -- executed repair <terrain> <A|B> <seed> <count> <out>
//! ```
//!
//! [definition; agent-inferred, the record's §0] **`executed repair`** draws `count` passages of the
//! terrain (`terrain_pairs` with an opening of 8 cells and 40 stations), drops the declared damage's
//! cells, and from here reads only the damaged cells:
//! 1. **Differentiate**: every intact station, in passage order, is one observation of the turn
//!    menus at every distance its intact antecedents reach (`hnn::keys::damaged_station_pairs`,
//!    `PairLocation`); the pair located at the read set's end is the key.
//! 2. **Integrate by reflection**: each passage restricted through the located pair from both sides
//!    and released or held cell by cell (`compression::keys::repair::{restrict, Restriction::release}`).
//!
//! Only then is the truth read, to score: certified fidelity, valid decode, the codec (the key once,
//! each passage's residual; decoded and checked to reopen every passage), the Fold's bound
//! `⌈log₂ N⌉`, the literal; `n*_machine` and, read-only, `n*_terrain` (THE_TWO_COUNTS' global family
//! of lags `[1, 40]` and maps of `ℤ/4`, reading only intact arguments) twice: at the repair's grain
//! (the union of the survivors' restrictions equals the generating key's at every erased cell) and
//! as the two counts' syntactic class (the least count from which the survivors no longer change;
//! added before the read, the record's §0 amendment). Nothing of the reference reaches the machine. Every passage's damaged, repaired and true cells are
//! written to `<out>.sections`, the location's curve to `<out>.curve`.

use super::*;
use holonics::compression::cost::ceil_log2;
use holonics::compression::keys::repair::{
    CellRelease, DamagedPassage, PairRelation, Restriction, key_code, read_key, reopen,
    residual_code, restrict,
};
use holonics::hnn::keys::{LocatedPair, PairLocation, damaged_station_pairs};
use num_bigint::BigUint;

use executed_loop::terrain_pairs;

/// The declared opening `o` and the stations after it (the record's §0).
const OPENING: usize = 8;
const STATIONS: usize = 40;
/// `|A|`: the terrain's residues `ℤ/4`.
const CLASSES: usize = 4;
/// THE_TWO_COUNTS' reference lags `[1, 40]`.
const LAGS: usize = 40;

/// **The declared damage** (the record's §0): A, the spans; B, the odd cells from 7.
fn damage(name: &str) -> Vec<usize> {
    match name {
        "A" => std::iter::once(3)
            .chain(6..10)
            .chain(20..25)
            .chain(33..37)
            .chain(44..48)
            .collect(),
        "B" => (7..OPENING + STATIONS).step_by(2).collect(),
        _ => panic!("a damage: A | B"),
    }
}

/// The terrain's generating key, read-only instrumentation for `n*_terrain` and the claim.
fn generating(terrain: &str) -> PairRelation {
    let (offset, turn) = match terrain {
        "order2" => (2, 1),
        "line" => (4, 0),
        "alternation" => (2, 0),
        _ => panic!("a terrain: order2 | alternation | line"),
    };
    PairRelation::new(offset, (0..CLASSES).map(|y| Some((y + turn) % CLASSES)).collect())
        .expect("a generating key")
}

fn show(cells: &[Option<usize>]) -> String {
    cells
        .iter()
        .map(|cell| cell.map_or_else(|| "·".to_string(), |class| class.to_string()))
        .collect::<Vec<_>>()
        .join("")
}

fn shown_release(releases: &[CellRelease]) -> String {
    releases
        .iter()
        .map(|release| match release {
            CellRelease::Intact(class) | CellRelease::Released(class) => class.to_string(),
            CellRelease::Held(_) => "?".to_string(),
        })
        .collect::<Vec<_>>()
        .join("")
}

/// One reference lag's fibre: alive, and its map's value at each argument read so far.
#[derive(Clone)]
struct Lag {
    alive: bool,
    map: [Option<usize>; CLASSES],
}

/// The reference family after the first `k` observations (each `(passage, station)`), every lag
/// reading only intact arguments.
fn reference_after(damaged: &[Vec<Option<usize>>], observations: &[(usize, usize)]) -> Vec<Lag> {
    let mut lags = vec![
        Lag {
            alive: true,
            map: [None; CLASSES],
        };
        LAGS
    ];
    for &observation in observations {
        lags = reference_after_one(lags, damaged, observation);
    }
    lags
}

/// The reference family after one more observation.
fn reference_after_one(
    mut lags: Vec<Lag>,
    damaged: &[Vec<Option<usize>>],
    (passage, t): (usize, usize),
) -> Vec<Lag> {
    let value = damaged[passage][t].expect("an observation is an intact station");
    for (index, lag) in lags.iter_mut().enumerate().filter(|(_, lag)| lag.alive) {
        let distance = index + 1;
        if distance > t {
            continue;
        }
        if let Some(argument) = damaged[passage][t - distance] {
            match lag.map[argument] {
                None => lag.map[argument] = Some(value),
                Some(known) if known != value => lag.alive = false,
                Some(_) => {}
            }
        }
    }
    lags
}

/// The alive lags with their maps (`·` unobserved), the first eight and the count.
fn survivors_shown(lags: &[Lag]) -> String {
    let alive: Vec<String> = lags
        .iter()
        .enumerate()
        .filter(|(_, lag)| lag.alive)
        .map(|(index, lag)| {
            let map: Vec<String> = lag
                .map
                .iter()
                .map(|v| v.map_or_else(|| "·".to_string(), |y| y.to_string()))
                .collect();
            format!("ℓ {} [{}]", index + 1, map.join(" "))
        })
        .collect();
    format!("{} alive: {}", alive.len(), alive.iter().take(8).cloned().collect::<Vec<_>>().join("; "))
}

/// **The stopping object at the repair's grain**: at every erased cell of every passage, the union
/// of the families under every surviving key (each completion of an alive lag's map: an unobserved
/// argument emits every class; a completion the passage refuses contributes nothing) equals the
/// family under the generating key.
fn stopping_holds(lags: &[Lag], passages: &[DamagedPassage], target: &[Restriction]) -> bool {
    for (passage, generated) in passages.iter().zip(target) {
        let mut union = vec![vec![false; CLASSES]; passage.cells().len()];
        for (index, lag) in lags.iter().enumerate().filter(|(_, lag)| lag.alive) {
            let free: Vec<usize> = (0..CLASSES).filter(|&a| lag.map[a].is_none()).collect();
            let completions = CLASSES.pow(free.len() as u32);
            for code in 0..completions {
                let mut map: Vec<Option<usize>> = lag.map.to_vec();
                let mut rest = code;
                for &a in &free {
                    map[a] = Some(rest % CLASSES);
                    rest /= CLASSES;
                }
                let relation = PairRelation::new(index + 1, map).expect("a reference key");
                if let Ok(restriction) = restrict(passage, &relation) {
                    for (t, family) in restriction.families().iter().enumerate() {
                        for &class in family {
                            union[t][class] = true;
                        }
                    }
                }
            }
        }
        for t in passage.erased() {
            let joined: Vec<usize> = (0..CLASSES).filter(|&c| union[t][c]).collect();
            if joined != generated.families()[t] {
                return false;
            }
        }
    }
    true
}

/// An observation count as passages plus observations of the next (each passage reads the same
/// count of intact stations under one damage).
fn units(k: usize, per: usize) -> String {
    format!("{k} observations ({} passages plus {})", k / per, k % per)
}

/// **`executed repair`** (module header).
pub(super) fn repair(terrain: &str, damage_name: &str, seed: u64, count: usize, out: &str) {
    let clock = Instant::now();
    let declared = order_declared();
    let field = declare(&declared);
    // The source ring: ring 0 of the declaration (its refinement's ring).
    let ring = 0;
    let period = usize::try_from(declared.period).expect("a period fits");
    let shape = Declared {
        request: OPENING,
        stations: STATIONS,
        ..declared
    };
    let truths: Vec<Vec<usize>> = terrain_pairs(terrain, &shape, seed, count)
        .into_iter()
        .map(|(mut opening, rule)| {
            opening.extend(rule);
            opening
        })
        .collect();
    let erased = damage(damage_name);
    let damaged: Vec<Vec<Option<usize>>> = truths
        .iter()
        .map(|truth| {
            (0..truth.len())
                .map(|t| (!erased.contains(&t)).then_some(truth[t]))
                .collect()
        })
        .collect();
    let truths = truths; // read again only after every release (below)
    println!(
        "executed repair: {terrain}, damage {damage_name}, seed {seed}, {count} passages of {} cells (opening {OPENING}); erased cells {erased:?} ({} of {})",
        OPENING + STATIONS,
        erased.len(),
        OPENING + STATIONS
    );

    // 1. Differentiate: the turn menus over every intact station.
    let mut location = PairLocation::open(&field, ring);
    let mut observed: Vec<(usize, usize)> = Vec::new();
    let mut first_lock: Option<(usize, LocatedPair)> = None;
    let mut stable: Option<(usize, LocatedPair)> = None;
    let mut curve = String::new();
    let mut per_passage_located = 0usize;
    let mut per = 0usize;
    for (index, cells) in damaged.iter().enumerate() {
        let observations =
            damaged_station_pairs(&field, ring, cells, OPENING).expect("the damaged menu");
        per = observations.len();
        let mut own = PairLocation::open(&field, ring);
        for (t, readings) in &observations {
            location.observe(readings);
            own.observe(readings);
            observed.push((index, *t));
            let survivors = location.survivors();
            let located = survivors.located();
            let k = observed.len();
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
            curve.push_str(&format!(
                "observation {k} (passage {index}, station {t}): read {}, alive {} {:?}{}\n",
                survivors.read,
                survivors.alive.len(),
                survivors.distances().iter().take(8).collect::<Vec<_>>(),
                located.as_ref().map_or_else(String::new, |pair| format!(
                    " located δ {} map {:?}",
                    pair.offset, pair.map
                ))
            ));
        }
        if let Some((_, pair)) = &stable {
            if own.survivors().located().as_ref() == Some(pair) {
                per_passage_located += 1;
            }
        }
    }
    #[allow(clippy::disallowed_methods)]
    std::fs::write(format!("{out}.curve"), &curve).expect("write the curve");
    let total = observed.len();
    match &first_lock {
        Some((k, pair)) => println!(
            "  first lock at {}: δ {}, map {:?}",
            units(*k, per),
            pair.offset,
            pair.map
        ),
        None => println!("  no lock in the read set ({total} observations)"),
    }
    let Some((n_machine, located)) = stable else {
        let survivors = location.survivors();
        println!(
            "  not located at the read set's end ({total} observations): distances alive {:?}; every erased cell held",
            survivors.distances()
        );
        println!("executed repair: {} ms; resident {}", clock.elapsed().as_millis(), resident());
        return;
    };
    println!(
        "  n*_machine: located from {} to the read set's end ({total} observations): δ {}, map {:?}, cycle {}, turns {:?}; survivors at the end {:?}",
        units(n_machine, per),
        located.offset,
        located.map,
        located.cycle,
        located.turns,
        location.survivors().distances()
    );
    let relation = located
        .relation(&field, ring, CLASSES)
        .expect("the located pair as a relation on the classes");
    println!(
        "  the relation on ℤ/4: δ {}, consequences {:?}; {} of {count} passages locate it from their own intact cells alone",
        relation.offset(),
        relation.map(),
        per_passage_located
    );

    // 2. Integrate by reflection: restrict and release, reading the damaged cells only.
    let integrate = Instant::now();
    let passages: Vec<DamagedPassage> = damaged
        .iter()
        .map(|cells| DamagedPassage::new(cells.clone(), CLASSES, OPENING).expect("a passage"))
        .collect();
    let mut restrictions = Vec::new();
    let mut releases = Vec::new();
    for passage in &passages {
        match restrict(passage, &relation) {
            Ok(restriction) => {
                releases.push(Some(restriction.release().expect("the release law")));
                restrictions.push(Some(restriction));
            }
            Err(refusal) => {
                releases.push(None);
                restrictions.push(None);
                println!("  a passage refuses the located pair: {refusal}");
            }
        }
    }
    let integrated_ms = integrate.elapsed().as_millis();

    // 3. The truth is read: scoring only.
    let (mut released, mut held, mut right, mut valid) = (0usize, 0usize, 0usize, 0usize);
    let mut held_cells: BTreeMap<usize, usize> = BTreeMap::new();
    let mut held_families: BTreeMap<Vec<usize>, usize> = BTreeMap::new();
    let mut fold_bound = 0u64;
    let mut joints: BTreeMap<BigUint, usize> = BTreeMap::new();
    let mut sweeps_max = 0u64;
    let mut sections = String::new();
    for (index, truth) in truths.iter().enumerate() {
        let (Some(restriction), Some(release)) = (&restrictions[index], &releases[index]) else {
            continue;
        };
        sweeps_max = sweeps_max.max(restriction.sweeps());
        let joint = restriction.joint();
        fold_bound += ceil_log2(&joint);
        *joints.entry(joint).or_default() += 1;
        for &t in &erased {
            match &release[t] {
                CellRelease::Released(class) => {
                    released += 1;
                    right += usize::from(*class == truth[t]);
                    valid += usize::from(*class < CLASSES);
                }
                CellRelease::Held(family) => {
                    held += 1;
                    *held_cells.entry(t).or_default() += 1;
                    *held_families.entry(family.clone()).or_default() += 1;
                }
                CellRelease::Intact(_) => unreachable!("an erased cell is not intact"),
            }
        }
        sections.push_str(&format!(
            "passage {index}\n  damaged  {}\n  repaired {}\n  truth    {}\n",
            show(&damaged[index]),
            shown_release(release),
            truth.iter().map(usize::to_string).collect::<String>()
        ));
    }
    #[allow(clippy::disallowed_methods)]
    std::fs::write(format!("{out}.sections"), &sections).expect("write the sections");
    println!(
        "  released {released}, held {held} of {} erased cells; released equal to the truth {right} of {released}; valid classes of ℤ/4 {valid} of {released}; sweeps at most {sweeps_max}; {integrated_ms} ms",
        erased.len() * count
    );
    println!("  held, by cell: {held_cells:?}; by family: {held_families:?}");
    println!("  joint fibres N (passages): {joints:?}");

    // The codec: the key once, each passage's residual; decoded and checked.
    let key = key_code(&relation, period).expect("the key's code");
    let mut code = key.clone();
    let mut residual_bits = 0usize;
    let mut longest = 0usize;
    for (passage, truth) in passages.iter().zip(&truths) {
        let residual = residual_code(truth, passage, &relation).expect("the residual");
        residual_bits += residual.len();
        longest = longest.max(residual.len());
        code.extend(residual);
    }
    let mut bits = code.clone().into_iter();
    let read = read_key(&mut bits, CLASSES, period).expect("the key reads back");
    let reopened = passages
        .iter()
        .zip(&truths)
        .filter(|(passage, truth)| {
            reopen(passage, &read, &mut bits).expect("the passage reopens") == **truth
        })
        .count();
    let literal = erased.len() * count * usize::try_from(ceil_log2(&BigUint::from(CLASSES))).unwrap();
    println!(
        "  the codec: key {} bits + residual {residual_bits} bits (longest a passage {longest}; the Fold's bound Σ⌈log₂ N⌉ = {fold_bound}) = {} bits, against the literal {literal} bits; decoded: {reopened} of {count} passages reopened exactly, trailing bits {}",
        key.len(),
        code.len(),
        bits.count()
    );
    println!(
        "  per passage: the key {} + its residual against its literal {} bits",
        key.len(),
        erased.len() * 2
    );

    // n*_terrain (read-only): the least k at which the stopping object holds.
    let reference = Instant::now();
    let generated: Vec<Restriction> = passages
        .iter()
        .map(|passage| restrict(passage, &generating(terrain)).expect("the generating key fits"))
        .collect();
    println!(
        "  the generating key {:?} {}",
        generating(terrain).map(),
        if generating(terrain) == relation {
            "is the located relation"
        } else {
            "is not the located relation"
        }
    );
    let holds = |k: usize| stopping_holds(&reference_after(&damaged, &observed[..k]), &passages, &generated);
    if holds(total) {
        let (mut low, mut high) = (0usize, total);
        while low < high {
            let middle = (low + high) / 2;
            if holds(middle) {
                high = middle;
            } else {
                low = middle + 1;
            }
        }
        println!(
            "  n*_terrain (the repair's grain): {} (the global family, lags [1, {LAGS}]); survivors there: {}; {} ms",
            units(low, per),
            survivors_shown(&reference_after(&damaged, &observed[..low])),
            reference.elapsed().as_millis()
        );
    } else {
        println!(
            "  n*_terrain (the repair's grain): the stopping object does not hold at the read set's end ({total} observations); {} ms",
            reference.elapsed().as_millis()
        );
    }
    // The two counts' syntactic class (their pin §4): the least k from which S_k no longer changes.
    let mut lags = reference_after(&damaged, &[]);
    let mut settled = 0usize;
    for k in 1..=total {
        let next = reference_after_one(lags.clone(), &damaged, observed[k - 1]);
        if next.iter().zip(&lags).any(|(a, b)| a.alive != b.alive || a.map != b.map) {
            settled = k;
        }
        lags = next;
    }
    println!(
        "  n*_terrain (the syntactic class, S_k unchanged from here): {}; survivors at the end: {}",
        units(settled, per),
        survivors_shown(&lags)
    );
    println!("executed repair: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

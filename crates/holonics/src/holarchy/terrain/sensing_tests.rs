//! The chase's switches checked exactly on small fixtures (`holarchy::terrain::sensing`, THE_REBUILD
//! F6): the channel menu's separation condition and its location of one turned frame (and the two
//! menus it fails for); the faulty sensor turning one frame on its odd aeons, and a reading inverting
//! to its cell; a candidate's withheld cells revealed after the lag; and the machine under the
//! switches, whose attribution locates the fault on exactly its active ticks, whose constitution
//! equals the prompt one on the true cells (the lag's errors and the faulty frame deposit nothing),
//! and whose released bounds are kept under the lagged capture basin.

use super::chase::*;
use super::chase_tests::{ESCAPE, declaration, family, pursuer, uniform};
use super::pursuit::*;
use super::sensing::*;
use super::switching::AeonFamily;
use super::{Draw, TerrainError};
use crate::receiver::population::{
    ChaseFamily, Likelihood, MachineChaser, MachineDeclaration, Population, selected_fibre,
};

/// **The separation condition, checked on the circuit matrix.** The complete menu on three channels
/// has the circuits `(0, 1)`, `(0, 2)`, `(1, 2)` and `C = [[1, −1, 0], [1, 0, −1], [0, 1, −1]]`; no
/// nonzero vector of support at most `2` lies in `ker C`, so each of the nine one-channel defects
/// (three channels, three turns) is located uniquely from its syndrome, and the zero syndrome names
/// no defect. At `k = 2` the common mode `(1, 1, 1)` breaks it. Two channels detect a defect (the
/// syndrome is nonzero) but locate it nowhere: `(1, 1)` breaks their condition at `k = 1`, and a
/// syndrome of theirs is the syndrome of two one-channel defects.
#[test]
fn the_channel_menu_locates_one_defect_exactly_where_its_kernel_separates() {
    let menu = ChannelMenu::complete(CHANNELS).unwrap();
    assert_eq!(menu.circuits(), &[[0, 1], [0, 2], [1, 2]]);
    assert_eq!(
        menu.matrix(),
        vec![vec![1, -1, 0], vec![1, 0, -1], vec![0, 1, -1]]
    );
    assert!(menu.separates(1));
    assert_eq!(menu.separation_witness(2), Some(vec![1, 1, 1]));
    assert_eq!(menu.locate(&[0, 0, 0], 1), Located::Unique(vec![0, 0, 0]));
    for channel in 0..CHANNELS {
        for turns in 1..TURNS {
            let mut defect = vec![0u8; CHANNELS];
            defect[channel] = turns;
            let syndrome = menu.syndrome(&defect);
            assert!(syndrome.iter().any(|&s| s != 0));
            assert_eq!(menu.locate(&syndrome, 1), Located::Unique(defect));
        }
    }
    let two = ChannelMenu::complete(2).unwrap();
    assert_eq!(two.separation_witness(1), Some(vec![1, 1]));
    assert_eq!(two.syndrome(&[1, 0]), vec![1]);
    assert_eq!(two.locate(&[1], 1), Located::Unattributed(2));
    assert!(ChannelMenu::complete(1).is_err());
}

/// **The loop closure of one tick's readings.** A reading turned on any one channel by any
/// nonidentity turn is located (that channel, that turn) and the cleared reading is the truth; a
/// runner at rest is sighted all the same (its line of sight is never zero), so a turned frame is
/// located there too. Beyond one defect the menu misattributes or refuses: two frames turned alike
/// read as the third channel turned back (the common mode), two turned apart name no one-channel
/// defect. Readings of disagreeing kinds, a zero line of sight, and headings no turn relates are
/// refused.
#[test]
fn the_loop_closure_locates_a_turned_frame_and_names_the_runners_reading() {
    let menu = ChannelMenu::complete(CHANNELS).unwrap();
    let moving = Reading {
        kind: CellKind::Move,
        sight: [3, -2],
        heading: [1, 2],
    };
    let resting = Reading {
        kind: CellKind::Slip,
        sight: [-4, 1],
        heading: [0, 0],
    };
    for truth in [moving, resting] {
        assert_eq!(
            menu.close(&[truth; CHANNELS]).unwrap(),
            Closure {
                reading: truth,
                defect: None
            }
        );
        for channel in 0..CHANNELS {
            for turns in 1..TURNS {
                let mut readings = [truth; CHANNELS];
                readings[channel] = truth.turned(turns);
                assert_eq!(
                    menu.close(&readings).unwrap(),
                    Closure {
                        reading: truth,
                        defect: Some(ChannelDefect { channel, turns })
                    }
                );
            }
        }
    }
    let alike = [moving.turned(1), moving.turned(1), moving];
    assert_eq!(
        menu.close(&alike).unwrap().defect,
        Some(ChannelDefect {
            channel: 2,
            turns: 3
        })
    );
    assert!(
        menu.close(&[moving.turned(1), moving.turned(2), moving])
            .is_err()
    );
    let mut kinds = [moving; CHANNELS];
    kinds[1].kind = CellKind::Slip;
    assert!(menu.close(&kinds).is_err());
    let mut blind = [moving; CHANNELS];
    for reading in &mut blind {
        reading.sight = [0, 0];
    }
    assert!(menu.close(&blind).is_err());
    let mut skew = [moving; CHANNELS];
    skew[0].heading = [2, 1];
    assert!(menu.close(&skew).is_err());
}

/// **The faulty sensor turns one frame on its odd aeons, and a reading inverts to its cell.** A fault
/// drawn on aeons of one to four ticks over 64 ticks: its clock is the `Switching` pattern's
/// (`SwitchTruth::drawn` on the same draw), it is active exactly on the odd aeons, and only its
/// channel's frame carries its turn there. On a uniform grass arena, from a runner at `(8, 8)` moving
/// `(1, 0)` with the chaser at `(2, 3)`, every letter of the alphabet (every move, the slip and the
/// wall) reads as its kind, the line of sight `(6, 5)` and its heading, and the reading names that
/// letter back; the reception turns the faulty channel's reading exactly where the fault is active.
#[test]
fn the_fault_turns_one_frame_on_its_odd_aeons_and_a_reading_names_its_cell() {
    let aeons = AeonFamily {
        shortest: 1,
        longest: 4,
    };
    let fault = FaultTruth::draw(&aeons, 64, &mut Draw::new(20_261_301)).unwrap();
    let mut again = Draw::new(20_261_301);
    let (_, _) = (again.below(CHANNELS), again.below(3));
    assert_eq!(
        fault.clock,
        super::SwitchTruth::drawn(64, &aeons, &mut again).unwrap()
    );
    assert!((1..TURNS).contains(&fault.turns) && fault.channel < CHANNELS);
    let mut active = 0;
    for tick in 0..64 {
        let odd = fault.aeon(tick).unwrap() % 2 == 1;
        assert_eq!(fault.active(tick), odd);
        active += usize::from(odd);
        for channel in 0..CHANNELS {
            let turned = channel == fault.channel && odd;
            assert_eq!(
                fault.turns_of(channel, tick),
                if turned { fault.turns } else { 0 }
            );
        }
    }
    assert!(active > 0 && active < 64);
    let arena = uniform(1);
    let moves = family().moves(&declaration()).unwrap();
    let before = Motion {
        position: [8, 8],
        velocity: [1, 0],
    };
    let chaser = [2, 3];
    let quiet = (0..64).find(|&t| !fault.active(t)).unwrap();
    let loud = (0..64).find(|&t| fault.active(t)).unwrap();
    for cell in 0..moves.alphabet() {
        let after = arena.observe(&moves, &before, cell).unwrap();
        let reading = Reading::of(&moves, cell, &before, chaser, &after).unwrap();
        assert_eq!(reading.sight, [6, 5]);
        assert_eq!(reading.heading, after.velocity);
        assert_eq!(reading.cell(&arena, &moves, &before, chaser).unwrap(), cell);
        for (tick, turned) in [(quiet, false), (loud, true)] {
            let reception =
                Reception::read(&moves, cell, &before, chaser, &after, tick, Some(&fault)).unwrap();
            assert_eq!(reception.tick, tick);
            for (channel, read) in reception.readings.iter().enumerate() {
                let expected = if turned && channel == fault.channel {
                    reading.turned(fault.turns)
                } else {
                    reading
                };
                assert_eq!(*read, expected);
            }
        }
    }
    assert!(
        Switches {
            lag: LAG_LIMIT + 1,
            fault: None
        }
        .check()
        .is_err()
    );
}

/// **A withheld cell is revealed after the lag.** Under a lag of two the first two cells are
/// withheld and each later cell reveals the one emitted two before it; at lag zero each cell is
/// revealed as it is emitted. A candidate that emits against the chaser keeps its state past its own
/// cell and reveals its cell of two ticks before, so the fibre's classes at lag zero are the classes
/// by the cell just emitted, and before the first reveal the fibre is one class.
#[test]
fn a_withheld_cell_is_revealed_after_the_lag() {
    let mut lagged = Pending::new(2).unwrap();
    assert_eq!(lagged.push(5).unwrap(), None);
    assert_eq!(lagged.push(6).unwrap(), None);
    assert_eq!(lagged.push(7).unwrap(), Some(5));
    assert_eq!(lagged.cells(), vec![6, 7]);
    assert_eq!(lagged.push(8).unwrap(), Some(6));
    let mut prompt = Pending::new(0).unwrap();
    assert_eq!(prompt.push(3).unwrap(), Some(3));
    assert!(prompt.cells().is_empty());
    assert!(Pending::new(LAG_LIMIT + 1).is_err());
    let arena = uniform(1);
    let family = family();
    let moves = family.moves(&declaration()).unwrap();
    let opening = [8, 8];
    let chaser = [2, 3];
    let prompt = Candidate::opening(&family, &arena, opening).unwrap();
    let parts = classes(&arena, &moves, &prompt, chaser, 0).unwrap();
    for (revealed, class) in &parts {
        for member in class {
            let own = prompt[member.index]
                .cell(&arena, &moves, chaser, 0)
                .unwrap();
            assert_eq!(*revealed, Some(own));
            assert_eq!(
                member.state,
                prompt[member.index]
                    .receive(&arena, &moves, own)
                    .unwrap()
                    .state
            );
        }
    }
    let lagged = Candidate::lagged(&family, &arena, opening, 2).unwrap();
    let mut fibre = lagged.clone();
    for tick in 0..2u64 {
        let parts = classes(&arena, &moves, &fibre, chaser, tick).unwrap();
        assert_eq!(parts.len(), 1);
        assert_eq!(parts[0].0, None);
        fibre = parts[0].1.clone();
    }
    let parts = classes(&arena, &moves, &fibre, chaser, 2).unwrap();
    for (revealed, class) in &parts {
        for member in class {
            let own = prompt[member.index]
                .cell(&arena, &moves, chaser, 0)
                .unwrap();
            assert_eq!(
                *revealed,
                Some(own),
                "the cell of tick 0, revealed at tick 2"
            );
        }
    }
}

/// **The machine under the switches** on the `8 × 8` arena of the declared law, at the basin horizon
/// `m = 6`, the lag `d = 1` and the fault on aeons of one or two ticks, over the fixtures `s < 8`
/// that open outside capture: every motion it releases is admitted; the fault is located on exactly
/// its active ticks, with its channel and turn, and nowhere else; its constitution equals the prompt
/// one (a reception population receiving the true cells at their own ticks, no lag, no channel) at
/// every decision and exactly at the end, so neither the lag's errors nor the turned frame deposit
/// anything; its released bounds are kept (capture by `t + B_t`) with no pledge broken, the lagged
/// capture basin reading the reveals as they come. At lag zero the switched passage is the plain one:
/// the located fault changes nothing.
#[test]
fn the_switched_machine_attributes_each_error_and_deposits_only_the_contemporary_reading() {
    use rayon::prelude::*;
    let family = family();
    let small = ArenaDeclaration {
        width: 8,
        height: 8,
        ..declaration()
    };
    let action = |switches: Switches| ActionDeclaration {
        pursuer: pursuer(),
        ticks: 48,
        horizon: 2,
        switches,
    };
    let aeons = AeonFamily {
        shortest: 1,
        longest: 2,
    };
    let machine = || {
        MachineChaser::new(MachineDeclaration {
            family: family.clone(),
            escape: ESCAPE,
            horizon: 2,
            basin: 6,
            price: 0,
        })
        .unwrap()
    };
    let caps = pursuer().law.caps(&small).unwrap();
    let disk = Moves::within(caps.top()).unwrap();
    let located: Vec<usize> = (0..8u64)
        .into_par_iter()
        .filter_map(|seed| {
            let (_, _, openings) = Chase::drawn(&small, &family, seed).unwrap();
            if pursuer().captures(openings[0], openings[1]) {
                return None;
            }
            let mut located = 0;
            let mut plain = machine();
            let off = act_drawn(&small, &family, &action(Switches::OFF), seed, &mut plain).unwrap();
            let prompt_fault = Switches {
                lag: 0,
                fault: Some(aeons.clone()),
            };
            let mut corrected = machine();
            let on =
                act_drawn(&small, &family, &action(prompt_fault), seed, &mut corrected).unwrap();
            assert_eq!(
                (on.cells.clone(), on.captured),
                (off.cells.clone(), off.captured)
            );
            let switched = Switches {
                lag: 1,
                fault: Some(aeons.clone()),
            };
            let mut chaser = machine();
            let passage = act_drawn(&small, &family, &action(switched), seed, &mut chaser).unwrap();
            let receipt = chaser.receipt();
            let fault = passage.fault.as_ref().unwrap();
            let received = passage.received();
            assert_eq!(receipt.located.len(), received);
            for (tick, defect) in receipt.located.iter().enumerate() {
                let truth = fault.active(tick).then_some(ChannelDefect {
                    channel: fault.channel,
                    turns: fault.turns,
                });
                assert_eq!(*defect, truth, "seed {seed}, tick {tick}");
                located += usize::from(defect.is_some());
            }
            let motions = passage.ports.chaser.motions();
            for (tick, pair) in motions.windows(2).enumerate() {
                let admitted = pursuer()
                    .motions(&passage.ports.arena, &disk, &caps, &pair[0])
                    .unwrap();
                assert!(admitted.contains(&pair[1]), "seed {seed}, tick {tick}");
            }
            let mut prompt =
                Population::new(ChaseFamily::declare_on(&passage.ports, &family, ESCAPE).unwrap())
                    .unwrap();
            let size = |population: &Population| match selected_fibre(population).len() {
                0 => family.len(),
                n => n,
            };
            let mut sizes = vec![size(&prompt)];
            for &cell in &passage.cells[..received] {
                prompt.receive(cell).unwrap();
                sizes.push(size(&prompt));
            }
            for (tick, &fibre) in receipt.fibre.iter().enumerate() {
                assert_eq!(
                    fibre,
                    sizes[tick.saturating_sub(1)],
                    "seed {seed}, tick {tick}"
                );
            }
            let likelihoods = |population: &Population| -> Vec<Likelihood> {
                population.families().map(|f| f.likelihood()).collect()
            };
            assert_eq!(
                likelihoods(chaser.population().unwrap()),
                likelihoods(&prompt)
            );
            for (tick, bound) in receipt.certified.iter().enumerate() {
                if let Some(ticks) = bound {
                    assert!(
                        passage.captured.is_some_and(|at| at <= tick + ticks),
                        "seed {seed}: tick {tick} released {ticks}, captured {:?}",
                        passage.captured
                    );
                }
            }
            assert_eq!(receipt.broken, 0);
            Some(located)
        })
        .collect();
    assert!(located.len() >= 4, "{} fixtures chased", located.len());
    assert!(
        located.iter().sum::<usize>() > 0,
        "the fault is located on some tick"
    );
    let refused: Result<ActionPassage, TerrainError> = act(
        Arena::new(small.clone(), vec![1; small.patches()]).unwrap(),
        &family,
        0,
        [[6, 6], [1, 1]],
        &action(Switches {
            lag: 1,
            fault: Some(aeons),
        }),
        None,
        &mut PurePursuit,
    );
    assert!(refused.is_err(), "a declared fault is drawn, never absent");
}

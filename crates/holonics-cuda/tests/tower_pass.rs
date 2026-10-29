//! The gated tower's training pass on the card returns the host's bits (`holonics_cuda::hnn::tower`):
//! every face at its target, the whole summed covector, and, section after section, the learner
//! and its streams' states, with and without the pair face, the ring face, the turned modes, the
//! pumped modes, the rotor and the news clock; and the card refuses a declaration it does not carry.
use holonics::hnn::tower::realization::{HostPass, PassRealization, Slot};
use holonics::hnn::tower::{ContactLaw, NewsClock, PairFace, RingFace, RingRank, Rotor, RotorRing, Tower, TowerDeclaration, TowerFace, TowerLearner, TowerState, TurnLadder, FACE_BITS};
use holonics_cuda::hnn::{Card, TowerCard};

/// A declared exterior key stream: a 64-bit linear congruential walk, its high octets.
fn keys(n: usize) -> Vec<u8> {
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    (0..n)
        .map(|_| {
            x = x.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1_442_695_040_888_963_407);
            (x >> 56) as u8
        })
        .collect()
}

/// A small passage with structure to learn: a repeating phrase over the alphabet with a drifting
/// insert, so sections deposit and halve.
fn passage(alphabet: usize, len: usize) -> Vec<usize> {
    (0..len).map(|i| if i % 7 == 3 { (i / 7) % alphabet } else { (i * 5 + i / 13) % (alphabet - 1) }).collect()
}

fn declaration(alphabet: usize, gated: bool, turned: bool, pumped: bool) -> TowerDeclaration {
    TowerDeclaration { alphabet, width: 8, modes: 8, contacts: 16, levels: 2, gated, turned, pumped, contact: ContactLaw::Rectifying }
}

/// The faces a fixture joins to the gated tower: `forms` pair forms (none at zero), the ring face
/// it names, whether its modes are turned, whether they are pumped (a pumped mode is turned),
/// whether a rotor steps them, and the news clock its levels tick on.
#[derive(Clone, Copy, Default)]
struct Faces {
    forms: usize,
    ring: Option<Ringed>,
    turned: bool,
    pumped: bool,
    rotor: bool,
    news: Option<NewsClock>,
}

/// The ring face a fixture joins: the level and mode it rides and the harmonics its readout reads.
#[derive(Clone, Copy)]
struct Ringed {
    level: usize,
    mode: usize,
    harmonics: usize,
}

/// The gated tower founded on the keys, turned when `faces.turned` or `faces.pumped` (its turn
/// opened by `open_turn`), pumped when `faces.pumped` (its pump opened by `open_pump`), with
/// `faces.forms` pair forms joined when there are any (`join_pair`), the ring face when
/// `faces.ring` names one (`join_ring`), the rotor when `faces.rotor` (`join_rotor`) and the news
/// clock last when `faces.news` names one.
fn learners(alphabet: usize, faces: Faces) -> (TowerLearner, TowerLearner) {
    let turned = faces.turned || faces.pumped;
    let tower = Tower::found_on(declaration(alphabet, true, turned, faces.pumped), &keys(1 << 16), TurnLadder::Both).expect("founded");
    let mut learner = TowerLearner::new(tower, 5);
    if turned {
        open_turn(&mut learner);
    }
    if faces.pumped {
        open_pump(&mut learner);
    }
    if faces.forms > 0 {
        join_pair(&mut learner, faces.forms);
    }
    if let Some(ring) = faces.ring {
        join_ring(&mut learner, ring);
    }
    if faces.rotor {
        join_rotor(&mut learner);
    }
    if let Some(clock) = faces.news {
        learner.join_news(clock).expect("the clock joins");
    }
    (learner.clone(), learner)
}

/// A turned tower founds its turn at zero, on its gated twin; the fixture opens each level's turn
/// `W_φ` (about ±¼ on `2^(−24)`) and bias `b_φ` (about ±2 half turns on `2^(−16)`) off the key
/// stream, so every mode turns through the whole ladder from the first section.
fn open_turn(learner: &mut TowerLearner) {
    let d = learner.tower.declaration;
    let k = keys(1 << 16);
    let law = learner.tower.resident_law().expect("the law");
    let mut j = 12000;
    for lv in &law.levels {
        for i in lv.turn..lv.turn + d.modes * d.width {
            learner.tower.theta[i] = (k[j] as i32 - 128) << 15;
            j += 1;
        }
        for i in lv.turn_bias..lv.turn_bias + d.modes {
            learner.tower.theta[i] = (k[j] as i32 - 128) << 10;
            j += 1;
        }
    }
}

/// A pumped tower founds its pump at zero (`κ = 0`, `β = 0`), on its turned twin; the fixture opens
/// each level's depth `W_κ` and axis `W_ψ` (about ±¼ on `2^(−24)`) and their biases (about ±2 on
/// `2^(−16)`: a depth logit of ±2, so `|κ|` reaches about ¾ and modes pass the bifurcation, and an
/// axis of ±2 half turns) off the key stream, so the pump turns and boosts from the first section.
fn open_pump(learner: &mut TowerLearner) {
    let d = learner.tower.declaration;
    let k = keys(1 << 16);
    let law = learner.tower.resident_law().expect("the law");
    let mut j = 20000;
    for lv in &law.levels {
        for (material, bias) in [(lv.pump, lv.pump_bias), (lv.pump_axis, lv.pump_axis_bias)] {
            for i in material..material + d.modes * d.width {
                learner.tower.theta[i] = (k[j] as i32 - 128) << 15;
                j += 1;
            }
            for i in bias..bias + d.modes {
                learner.tower.theta[i] = (k[j] as i32 - 128) << 10;
                j += 1;
            }
        }
    }
}

/// A rotor of three rings on a level's first seven modes, of moduli 9, 11 and 101 and widths 1, 2
/// and 4 (the orders of 10 modulo each), the eighth mode still; its steps and turns are read off the
/// key stream, so some turns are zero, and the first class steps and turns nothing at any level.
fn join_rotor(learner: &mut TowerLearner) {
    let d = learner.tower.declaration;
    let rings = vec![RotorRing { width: 1, modulus: 9 }, RotorRing { width: 2, modulus: 11 }, RotorRing { width: 4, modulus: 101 }];
    let k = keys(1 << 16);
    let mut j = 30000;
    let mut key = |class: usize, below: u32| {
        j += 1;
        if class == 0 { 0 } else { u32::from(k[j]) % below }
    };
    let mut steps = Vec::new();
    let mut turns = Vec::new();
    for _ in 0..d.levels {
        for class in 0..d.alphabet {
            for g in &rings {
                steps.push(key(class, g.width as u32));
            }
            for g in &rings {
                for _ in 0..g.width {
                    turns.push(key(class, g.modulus));
                }
            }
        }
    }
    let rotor = Rotor::new(&d, rings, steps, turns).expect("the rotor");
    learner.tower.join_rotor(rotor).expect("the rotor joins");
}

/// A ring rank whose factors are read off the key stream at `at` (as the host's fixture reads
/// them), released by 8 at its founding, its push by 24 and its read by `read_shift`.
fn ring_rank(learner: &TowerLearner, at: usize, read_shift: u32) -> RingRank {
    let d = learner.tower.declaration;
    let (dims, hat) = (2 * d.modes, d.width + 1);
    let k = keys(1 << 16);
    let w = |from: usize, n: usize| -> Vec<i64> { (0..n).map(|j| k[at + from + j] as i64 - 128).collect() };
    RingRank { a: [w(0, dims), w(100, dims)], b: [w(200, hat), w(300, hat)], g: w(400, dims + 1), release: [8, 8, 8], push_shift: 24, read_shift }
}

/// The fixture's ring face: three ranks, the first riding its mode at every cell and read at the
/// push's grain, the other two read 8 bits coarser and riding founded pair moves at pairs the
/// passage meets (a turn, a reflection that reverses the hand, and the start's pair), each
/// restarting its hand at its own class; joined with its readout opened away from zero.
fn join_ring(learner: &mut TowerLearner, ring: Ringed) {
    let d = learner.tower.declaration;
    let opening: Vec<i32> = (0..d.alphabet).flat_map(|u| learner.tower.encoding(u).to_vec()).collect();
    let ranks = vec![ring_rank(learner, 7000, 0), ring_rank(learner, 7600, 8), ring_rank(learner, 8200, 8)];
    let turn = [644_245_094, 322_122_547, 107_374_182, -53_687_091];
    let reflection = [107_374_182, 0, 644_245_094, 322_122_547];
    let start = d.alphabet;
    let moves = vec![Vec::new(), vec![(0, 6, turn), (4, 0, reflection), (start, 0, turn)], vec![(2, 7, reflection), (8, 4, turn)]];
    let face = RingFace::new(&d, ring.level, ring.mode, ranks, opening, moves)
        .and_then(|f| f.with_harmonics(ring.harmonics))
        .and_then(|f| f.with_restarts(vec![None, Some(2), Some(10)]))
        .expect("a ring face");
    learner.join_ring_face(face).expect("joined");
    let law = learner.tower.resident_law().expect("the law").ring.expect("the ring face");
    let k = keys(1 << 16);
    let channels = (d.width + 1) * 2 * law.ranks * law.harmonics;
    let readout: Vec<i32> = (0..d.alphabet * channels).map(|j| (i32::from_be_bytes([k[4 * j + 9000], k[4 * j + 9001], k[4 * j + 9002], k[4 * j + 9003]]) >> 8) / 4).collect();
    learner.tower.open_ring_readout(&readout).expect("opened");
}

/// The fixture's pair face: `forms` forms whose weights are read off the key stream, each released
/// so that its values sit near the face's unit (as the host's own fixture does), joined with its
/// readout and lift opened away from zero so that they move the faces and carry a covector.
fn join_pair(learner: &mut TowerLearner, forms: usize) {
    let d = learner.tower.declaration;
    let hat = d.width + 1;
    let k = keys(1 << 16);
    let weights: Vec<Vec<i64>> = (0..forms).map(|v| (0..hat * hat).map(|j| k[3000 + v * hat * hat + j] as i64 - 128).collect()).collect();
    let opening: Vec<i32> = (0..d.alphabet).flat_map(|u| learner.tower.encoding(u).to_vec()).collect();
    let shifts = weights
        .iter()
        .map(|w| {
            let top = PairFace::exact_values(d.alphabet, d.width, &opening, w).iter().map(|v| v.unsigned_abs()).max().unwrap_or(0);
            (128 - top.leading_zeros() as i32 - FACE_BITS as i32).max(0)
        })
        .collect();
    let face = PairFace::new(d.alphabet, d.width, opening, weights, shifts).expect("a pair face");
    learner.join_pair_face(face).expect("joined");
    let pair = learner.tower.resident_law().expect("the law").pair.expect("the pair face");
    let opened = (pair.readout..pair.readout + d.alphabet * forms).chain(pair.lift..pair.lift + d.width * forms);
    for (j, i) in opened.enumerate() {
        learner.tower.theta[i] = (i32::from_be_bytes([k[4 * j + 8000], k[4 * j + 8001], k[4 * j + 8002], k[4 * j + 8003]]) >> 8) / 4;
    }
}

/// Host against card in lockstep: the opening read and its covector on the same material, then
/// both learners take the section; `compared` holds every other place out of the comparison.
fn lockstep(alphabet: usize, streams: usize, section: usize, sections: usize, holding: bool, faces: Faces) {
    let card = Card::open(0).expect("the card");
    let mut realized = TowerCard::open(&card).expect("the tower's image");
    let (mut host, mut carded) = learners(alphabet, faces);
    let classes = passage(alphabet, streams * (sections * section + 1));
    let chunk = classes.len() / streams;
    let mut states_h: Vec<TowerState> = (0..streams).map(|_| host.tower.rest()).collect();
    let mut states_c = states_h.clone();
    let mut deposits = 0;
    for k in 0..sections {
        let parts: Vec<&[usize]> = (0..streams).map(|s| &classes[s * chunk + k * section..s * chunk + (k + 1) * section + 1]).collect();
        let masks: Vec<Vec<Option<usize>>> = parts.iter().map(|p| p.iter().enumerate().map(|(i, &c)| (!holding || i % 2 == 0).then_some(c)).collect()).collect();
        let compared: Vec<&[Option<usize>]> = masks.iter().map(|m| m.as_slice()).collect();
        let compared = holding.then_some(compared.as_slice());
        let targets: Vec<Vec<Option<usize>>> = masks.iter().map(|m| m[1..].to_vec()).collect();
        let mut reference = HostPass::default();
        let read_h = reference.forward(&host.tower, &states_h, &parts, &targets, Slot::Opened).expect("host forward");
        let g_h = reference.reverse(&host.tower, &states_h, &parts, compared).expect("host reverse");
        let read_c = realized.forward(&host.tower, &states_h, &parts, &targets, Slot::Opened).expect("card forward");
        let g_c = realized.reverse(&host.tower, &states_h, &parts, compared).expect("card reverse");
        assert_eq!(read_h, read_c, "section {k}: the faces and the swell");
        assert_eq!(g_h, g_c, "section {k}: the summed covector");
        let receipt_h = host.section_realized(&mut states_h, &parts, compared, &mut HostPass::default()).expect("host section");
        let receipt_c = carded.section_realized(&mut states_c, &parts, compared, &mut realized).expect("card section");
        assert_eq!(receipt_h, receipt_c, "section {k}: the receipt");
        assert_eq!(states_h, states_c, "section {k}: the continuing states");
        assert_eq!(host.to_text(), carded.to_text(), "section {k}: the learner");
        deposits += usize::from(receipt_h.deposited);
    }
    assert!(deposits > 0, "the passage deposits");
}

#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_pass_is_the_hosts_section_after_section() {
    lockstep(11, 3, 9, 6, false, Faces::default());
}

#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_pass_holds_an_uncompared_place_as_the_host_does() {
    lockstep(11, 2, 12, 4, true, Faces::default());
}

/// The pair face's acceptance (the record `2026-10-27_THE_LEARNER_RUNS_ON_THE_CARD…`): 32 sections
/// equal face by face and covector entry by entry, the learners and their states after each.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_pair_faced_pass_is_the_hosts_for_thirty_two_sections() {
    lockstep(11, 3, 9, 32, false, Faces { forms: 3, ..Faces::default() });
}

#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_pair_faced_pass_holds_an_uncompared_place_as_the_host_does() {
    lockstep(11, 2, 12, 8, true, Faces { forms: 2, ..Faces::default() });
}

/// The ring face's acceptance: 32 sections equal face by face and covector entry by entry, the
/// learners and their states (each rank's value and hand) after each; the ring on the top level,
/// read through three characters of its turn.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_ring_faced_pass_is_the_hosts_for_thirty_two_sections() {
    lockstep(11, 3, 9, 32, false, Faces { ring: Some(Ringed { level: 1, mode: 3, harmonics: 3 }), ..Faces::default() });
}

/// The ring on the bottom level beside the pair face, read through its turn alone, an uncompared
/// place held.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_ring_and_pair_faced_pass_holds_an_uncompared_place_as_the_host_does() {
    lockstep(11, 2, 12, 8, true, Faces { forms: 2, ring: Some(Ringed { level: 0, mode: 1, harmonics: 1 }), ..Faces::default() });
}

/// The turned modes' acceptance: 32 sections equal face by face and covector entry by entry, the
/// learners and their states after each, every mode turned through the ladder.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_turned_pass_is_the_hosts_for_thirty_two_sections() {
    lockstep(11, 3, 9, 32, false, Faces { turned: true, ..Faces::default() });
}

/// Turned modes beside the pair face and the ring face, the ring riding a turned mode, an
/// uncompared place held.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_turned_ring_and_pair_faced_pass_holds_an_uncompared_place_as_the_host_does() {
    lockstep(11, 2, 12, 8, true, Faces { forms: 2, ring: Some(Ringed { level: 1, mode: 5, harmonics: 2 }), turned: true, ..Faces::default() });
}

/// The pumped modes' acceptance: 32 sections equal face by face and covector entry by entry, the
/// learners and their states after each, every mode turned through the ladder and pumped, some
/// past the bifurcation.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_pumped_pass_is_the_hosts_for_thirty_two_sections() {
    lockstep(11, 3, 9, 32, false, Faces { pumped: true, ..Faces::default() });
}

/// Pumped modes beside the pair face and the ring face, the ring riding a pumped mode (its move's
/// `α` and `β`), an uncompared place held.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_pumped_ring_and_pair_faced_pass_holds_an_uncompared_place_as_the_host_does() {
    lockstep(11, 2, 12, 8, true, Faces { forms: 2, ring: Some(Ringed { level: 1, mode: 5, harmonics: 2 }), pumped: true, ..Faces::default() });
}

/// The pumped tower's advance is the host's, class by class.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_pumped_advance_is_the_hosts_class_by_class() {
    advance_class_by_class(Faces { pumped: true, ..Faces::default() });
}

/// The rotor's acceptance: 32 sections equal face by face and covector entry by entry, the learners
/// and their states after each, three rings stepped and turned at every class but the first.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_rotor_pass_is_the_hosts_for_thirty_two_sections() {
    lockstep(11, 3, 9, 32, false, Faces { rotor: true, ..Faces::default() });
}

/// The rotor stepping pumped modes beside the pair face, an uncompared place held.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_pumped_rotor_and_pair_faced_pass_holds_an_uncompared_place_as_the_host_does() {
    lockstep(11, 2, 12, 8, true, Faces { forms: 2, pumped: true, rotor: true, ..Faces::default() });
}

/// The rotor tower's advance is the host's, class by class, the still first class among them.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_rotor_advance_is_the_hosts_class_by_class() {
    advance_class_by_class(Faces { pumped: true, rotor: true, ..Faces::default() });
}

/// The news clock's acceptance: 32 sections equal face by face and covector entry by entry, the
/// learners and their states (each stream's open face and phase) after each. Level 1's section is
/// two bits, under the four or so a class carries, so it ticks none, once or several times at an
/// arrival.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_news_clocked_pass_is_the_hosts_for_thirty_two_sections() {
    lockstep(11, 3, 9, 32, false, Faces { news: Some(NewsClock::new(2, 2).expect("a clock")), ..Faces::default() });
}

/// The news clock beside turned modes and the pair face, an uncompared place held.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_turned_pair_faced_news_clocked_pass_holds_an_uncompared_place_as_the_host_does() {
    lockstep(11, 2, 12, 8, true, Faces { forms: 2, turned: true, news: Some(NewsClock::new(3, 2).expect("a clock")), ..Faces::default() });
}

/// The card's advance is the host's, class by class: three prompts read whole together, then one
/// class at a time on every stream, each stream's whole face and continuing state equal.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_advance_is_the_hosts_class_by_class() {
    advance_class_by_class(Faces::default());
}

/// The same under a news clock: each prompt's open face and phase carried from one advance to the
/// next on the card as on the host.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_news_clocked_advance_is_the_hosts_class_by_class() {
    advance_class_by_class(Faces { news: Some(NewsClock::new(2, 2).expect("a clock")), ..Faces::default() });
}

fn advance_class_by_class(faces: Faces) {
    let card = Card::open(0).expect("the card");
    let mut realized = TowerCard::open(&card).expect("the tower's image");
    let alphabet = 13;
    let (host, _) = learners(alphabet, faces);
    let tower = &host.tower;
    let classes = passage(alphabet, 27);
    let prompts: Vec<&[usize]> = classes.chunks(9).collect();
    let mut expected_states: Vec<TowerState> = prompts.iter().map(|_| tower.rest()).collect();
    let expected: Vec<_> = prompts
        .iter()
        .zip(expected_states.iter_mut())
        .map(|(p, s)| p.iter().map(|&u| tower.advance(s, u).expect("advance")).last().expect("a face"))
        .collect();
    let mut states: Vec<TowerState> = prompts.iter().map(|_| tower.rest()).collect();
    let (faces, _) = tower.advance_realized(&mut states, &prompts, &mut realized).expect("card advance");
    assert_eq!(faces, expected, "the prompts' faces");
    assert_eq!(states, expected_states, "the prompts' states");
    for u in [2usize, 0, 7, 12] {
        let expected: Vec<_> = expected_states.iter_mut().map(|s| tower.advance(s, u).expect("advance")).collect();
        let step = [u];
        let steps = vec![&step[..]; prompts.len()];
        let (faces, _) = tower.advance_realized(&mut states, &steps, &mut realized).expect("card advance");
        assert_eq!(faces, expected, "class {u}: the faces");
        assert_eq!(states, expected_states, "class {u}: the states");
    }
}

#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_card_refuses_a_declaration_it_does_not_carry() {
    let card = Card::open(0).expect("the card");
    let mut realized = TowerCard::open(&card).expect("the tower's image");
    let ungated = Tower::found_on(declaration(11, false, false, false), &keys(1 << 16), TurnLadder::Both).expect("founded");
    let classes = passage(11, 10);
    let parts: Vec<&[usize]> = vec![&classes[..]];
    let targets = vec![classes[1..].iter().map(|&c| Some(c)).collect::<Vec<_>>()];
    assert!(realized.forward(&ungated, &[ungated.rest()], &parts, &targets, Slot::Opened).is_err());
    let paired = Tower::found_on(TowerDeclaration { contact: ContactLaw::Pair, ..declaration(11, true, false, false) }, &keys(1 << 16), TurnLadder::Both).expect("founded");
    assert!(realized.forward(&paired, &[paired.rest()], &parts, &targets, Slot::Opened).is_err());
    let (host, _) = learners(11, Faces::default());
    assert!(realized.forward(&host.tower, &[host.tower.rest_with_credit()], &parts, &targets, Slot::Opened).is_err());
    let ragged: Vec<&[usize]> = vec![&classes[..], &classes[..9]];
    let ragged_targets = vec![targets[0].clone(), targets[0][..8].to_vec()];
    assert!(realized.forward(&host.tower, &[host.tower.rest(), host.tower.rest()], &ragged, &ragged_targets, Slot::Opened).is_err());
    // An open face or a news phase without a news clock, and a phase past the clock's period.
    let mut opened = host.tower.rest();
    opened.open = Some(TowerFace { masses: vec![1; 11], total: 11 });
    assert!(realized.forward(&host.tower, &[opened], &parts, &targets, Slot::Opened).is_err());
    let clock = NewsClock::new(8, 2).expect("a clock");
    let mut clocked = host.tower.clone();
    clocked.join_news(clock).expect("joined");
    let mut past = clocked.rest();
    past.news = clock.period(2).expect("the period");
    assert!(realized.forward(&clocked, &[past], &parts, &targets, Slot::Opened).is_err());
}

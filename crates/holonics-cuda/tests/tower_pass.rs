//! The gated tower's training pass on the card returns the host's bits (`holonics_cuda::hnn::tower`):
//! every face at its target, the whole summed covector, and, section after section, the learner
//! and its streams' states, with and without the pair face, the ring face, the turned modes, the
//! pumped modes, the rotor, the strands and the news clock, on rectifying contacts, the pair contact
//! or its foil; and the card refuses a declaration it does not carry.
use holonics::hnn::tower::body::{Answer, TowerBody};
use holonics::hnn::tower::participation::ParticipationDeclaration;
use holonics::hnn::tower::realization::{HostPass, PassRealization, Slot};
use holonics::hnn::tower::{ContactLaw, NewsClock, PairFace, RingFace, RingRank, Rotor, RotorRing, Sheet, StrandKey, StrandLaw, StrandRing, Strands, Tower, TowerDeclaration, TowerFace, TowerLearner, TowerState, TurnLadder, FACE_BITS};
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
/// whether a rotor steps them, whether strands are read at its second level's contacts, the news
/// clock its levels tick on, and its contact law when it is not rectifying.
#[derive(Clone, Copy, Default)]
struct Faces {
    forms: usize,
    ring: Option<Ringed>,
    turned: bool,
    pumped: bool,
    rotor: bool,
    strands: bool,
    news: Option<NewsClock>,
    contact: Option<ContactLaw>,
    /// Participation joined last over sections of this length (`open_participation`).
    participation: Option<usize>,
    /// The mutual contact joined at the founding (`open_mutual`).
    mutual: bool,
    /// The passage joined last (`open_passage`); it needs the news clock.
    passage: bool,
    /// The packets joined after the passage (`join_packets`); they need the news clock.
    packets: bool,
    /// The heading joined after the packets (`open_heading`); it needs them.
    heading: bool,
    /// The levels (two when zero).
    levels: usize,
    /// The learners' declared reading of each refused step on the opening's ticks
    /// (`TowerLearner::refusal_ticks`).
    refusal_ticks: bool,
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
/// `faces.ring` names one (`join_ring`), the rotor when `faces.rotor` (`join_rotor`), the strands
/// when `faces.strands` (`join_strands`) and the news clock last when `faces.news` names one; on
/// `faces.contact`'s law, its second drive opened (`open_pair_contacts`).
fn learners(alphabet: usize, faces: Faces) -> (TowerLearner, TowerLearner) {
    let turned = faces.turned || faces.pumped;
    let contact = faces.contact.unwrap_or(ContactLaw::Rectifying);
    let levels = if faces.levels == 0 { 2 } else { faces.levels };
    let tower = Tower::found_on(TowerDeclaration { contact, levels, ..declaration(alphabet, true, turned, faces.pumped) }, &keys(1 << 16), TurnLadder::Both).expect("founded");
    let mut learner = TowerLearner::new(tower, 5);
    if faces.mutual {
        open_mutual(&mut learner);
    }
    if contact != ContactLaw::Rectifying {
        open_pair_contacts(&mut learner);
    }
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
    if faces.strands {
        learner = join_strands(learner);
    }
    if let Some(clock) = faces.news {
        learner.join_news(clock).expect("the clock joins");
    }
    if let Some(section) = faces.participation {
        open_participation(&mut learner, section);
    }
    if faces.passage {
        open_passage(&mut learner);
    }
    if faces.packets {
        learner.join_packets().expect("the packets join");
    }
    if faces.heading {
        open_heading(&mut learner);
    }
    learner.refusal_ticks = faces.refusal_ticks;
    (learner.clone(), learner)
}

/// The heading joined last, the descent `D` of each level the clock holds opened about ±1/8 on
/// `2^(−24)` off the key stream (it founds at zero), so every heading after a cell moves the face's
/// top and the descent carries a covector from the first section; `C^→` opens as the level's read
/// (`join_heading`).
fn open_heading(learner: &mut TowerLearner) {
    learner.join_heading().expect("the heading joins");
    let d = learner.tower.declaration;
    let first = learner.tower.news().expect("the heading's clock").first();
    let law = learner.tower.resident_law().expect("the law");
    let k = keys(1 << 16);
    let mut j = 44000;
    for lv in &law.levels[first..] {
        for i in lv.descent..lv.descent + d.width * d.width {
            learner.tower.theta[i] = (k[j] as i32 - 128) << 14;
            j += 1;
        }
    }
}

/// The passage joined last, the `W₁ˣ` of each level the clock holds opened about ±¼ on `2^(−24)`
/// off the key stream (where participation's `W₁ᵃ` opens), so every arrival's current moves those
/// contacts' drive and the family carries a covector from the first section.
fn open_passage(learner: &mut TowerLearner) {
    learner.join_passage().expect("the passage joins");
    let d = learner.tower.declaration;
    let first = learner.tower.news().expect("the passage's clock").first();
    let law = learner.tower.resident_law().expect("the law");
    let k = keys(1 << 16);
    let mut j = 40000;
    for lv in &law.levels[first..] {
        for i in lv.passage..lv.passage + d.contacts * d.width {
            learner.tower.theta[i] = (k[j] as i32 - 128) << 15;
            j += 1;
        }
    }
}

/// Participation joined over sections of `section`, its heads the founded memory's runs; its
/// contacts' `W₁ᵃ` opened about ±¼ on `2^(−24)` off the key stream and its probe and key charts
/// doubled, so the current moves the drives and every family carries a covector from the first
/// section.
fn open_participation(learner: &mut TowerLearner, section: usize) {
    let d = learner.tower.declaration;
    let law = learner.tower.resident_law().expect("the law");
    let moduli: Vec<i128> = law.levels[0].moduli.iter().map(|&m| m as i128).collect();
    learner.join_participation(ParticipationDeclaration::founded(&moduli, section).expect("declared")).expect("participation joins");
    let law = learner.tower.resident_law().expect("the law");
    let k = keys(1 << 16);
    let mut j = 60000;
    for lv in &law.levels {
        let p = lv.participation;
        for i in p[8]..p[8] + d.contacts * d.width {
            learner.tower.theta[i] = (k[j] as i32 - 128) << 15;
            j += 1;
        }
        for i in p[0]..p[0] + 4 * d.modes * d.width {
            learner.tower.theta[i] *= 2;
        }
    }
}

/// The mutual contact joined at `β = 2^(−2)` on the founded tower, its geometry `J` opened about
/// ±¼ on `2^(−24)` off the key stream, so the contact has closed and the levels below receive its
/// covector from the first section.
fn open_mutual(learner: &mut TowerLearner) {
    learner.join_mutual_contact(2).expect("the contact joins");
    let law = learner.tower.resident_law().expect("the law");
    let w = learner.tower.declaration.width;
    let k = keys(1 << 16);
    for (i, v) in learner.tower.theta[law.readout..law.readout + w * w].iter_mut().enumerate() {
        *v = (k[50000 + i] as i32 - 128) << 15;
    }
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

/// The pair contact founds its second drive at zero material and unit bias, so it opens one-sided
/// (`v = a`); the fixture opens each level's second drive `W_b` (about ±¼ on `2^(−24)`) and moves
/// both drives' biases by about ±¼ on `2^(−16)` off the key stream, so the product and the foil's
/// cross terms move the faces and carry covectors from the first section.
fn open_pair_contacts(learner: &mut TowerLearner) {
    let d = learner.tower.declaration;
    let k = keys(1 << 16);
    let law = learner.tower.resident_law().expect("the law");
    let mut j = 40000;
    for lv in &law.levels {
        for i in lv.pair..lv.pair + d.contacts * d.width {
            learner.tower.theta[i] = (k[j] as i32 - 128) << 15;
            j += 1;
        }
        for i in (lv.contact_bias..lv.contact_bias + d.contacts).chain(lv.pair_bias..lv.pair_bias + d.contacts) {
            learner.tower.theta[i] += (k[j] as i32 - 128) << 7;
            j += 1;
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

/// Strands read at the second level's contacts, on the staircase rings 9, 99 and 999 (multipliers
/// 1, 10 and 10), digit `d` turning each by `d`, the laws held, stepped and turned, and the record's
/// keys: `<` clears the third strand on the sheet `+1`, `+` and `-` hand it to the first and clear
/// it on the sheets `+1` and `−1`, `=` hands it to the second and the first's reflection to it on
/// `+1`. The classes' words cycle through numerals, operators and bytes that move nothing, so the
/// strands step, turn, transfer, reflect and clear on both sheets. Their materials `W_sa` and, on a
/// pair law, `W_sb` (founded at zero) are opened about ±1/16 on `2^(−24)` off the key stream, so
/// the faces move the drives and the materials carry covectors from the first section. Joining adds
/// material, so the learner is founded again on the joined tower, its moments at zero as before.
fn join_strands(learner: TowerLearner) -> TowerLearner {
    let mut tower = learner.tower;
    let d = tower.declaration;
    let rings = vec![StrandRing { modulus: 9, multiplier: 1 }, StrandRing { modulus: 99, multiplier: 10 }, StrandRing { modulus: 999, multiplier: 10 }];
    let digits = (0..10u32).map(|v| (b'0' + v as u8, vec![v % 9, v, v])).collect();
    let keys_of = vec![
        (b'+', StrandKey { source: [3, 2, 0], sheet: Sheet::Plus }),
        (b'-', StrandKey { source: [3, 2, 0], sheet: Sheet::Minus }),
        (b'<', StrandKey { source: [1, 2, 0], sheet: Sheet::Plus }),
        (b'=', StrandKey { source: [1, 3, -1], sheet: Sheet::Plus }),
    ];
    let pieces = ["1", "23", "+", "-4", "=", "<5", "67", "8=", "9-", "0", " ", "+1=", "-="];
    let words = (0..d.alphabet).map(|c| pieces[c % pieces.len()].as_bytes().to_vec()).collect();
    let strands = Strands::new(&d, 1, rings, [StrandLaw::Held, StrandLaw::Stepped, StrandLaw::Turned], digits, keys_of, words).expect("strands");
    tower.join_strands(strands).expect("the strands join");
    let law = tower.resident_law().expect("the law").strands.expect("the strands");
    let extent = d.contacts * 6 * law.rings;
    let k = keys(1 << 16);
    let mut j = 50000;
    let pair = if d.contact == ContactLaw::Rectifying { 0..0 } else { law.pair..law.pair + extent };
    for i in (law.contact..law.contact + extent).chain(pair) {
        tower.theta[i] = (k[j] as i32 - 128) << 13;
        j += 1;
    }
    TowerLearner::new(tower, 5)
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

/// Participation's acceptance on the card (record `2026-10-28_ATTENTION_IS_THE_FIELDS_PARTICIPATION…`,
/// §7.2): 32 sections equal face by face, covector entry by entry, learner for learner and state
/// for state; with the pair contact and an uncompared place; and turned, stranded and paired.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_participating_pass_is_the_hosts_for_thirty_two_sections() {
    lockstep(11, 3, 9, 32, false, Faces { participation: Some(9), ..Faces::default() });
}

/// The mutual contact's acceptance on the card (record `2026-10-29_MUTUAL_CONTACT_…`, §5.2): 32
/// sections equal face by face, covector entry by entry, learner for learner and state for state;
/// and pumped on the pair contact with an uncompared place.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_mutual_pass_is_the_hosts_for_thirty_two_sections() {
    lockstep(11, 3, 9, 32, false, Faces { mutual: true, ..Faces::default() });
}

#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_pumped_mutual_pair_contact_holds_an_uncompared_place_as_the_host_does() {
    lockstep(11, 2, 12, 8, true, Faces { mutual: true, pumped: true, contact: Some(ContactLaw::Pair), ..Faces::default() });
}

#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_participating_pair_contact_holds_an_uncompared_place_as_the_host_does() {
    lockstep(11, 2, 12, 8, true, Faces { participation: Some(12), contact: Some(ContactLaw::Pair), ..Faces::default() });
}

#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_turned_stranded_participating_pass_is_the_hosts_for_eight_sections() {
    lockstep(11, 2, 12, 8, false, Faces { participation: Some(12), turned: true, strands: true, contact: Some(ContactLaw::Pair), ..Faces::default() });
}

/// A read that ends inside its participation's section carries the open section's sites, on the
/// card as on the host, and the card reads on from them across calls, as a release does, and
/// closes the section within a call: the first read leaves seven of twelve sites open, the second
/// closes the section at its fifth cell and leaves two of the next open, and the third leaves
/// seven. Each read's covector, its opening's carried sites read as constants, is the host's.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_participation_reads_a_section_on_across_calls_and_closes_it_within_one_as_the_host_does() {
    let card = Card::open(0).expect("the card");
    let mut realized = TowerCard::open(&card).expect("the tower's image");
    let (host, _) = learners(11, Faces { participation: Some(12), ..Faces::default() });
    let classes = passage(11, 40);
    let mut reference = HostPass::default();
    let (mut states_h, mut states_c) = (vec![host.tower.rest(); 2], vec![host.tower.rest(); 2]);
    for (round, (from, to, open)) in [(0, 8, 7), (7, 15, 2), (14, 20, 7)].into_iter().enumerate() {
        let parts: Vec<&[usize]> = vec![&classes[from..to], &classes[20 + from..20 + to]];
        let targets: Vec<Vec<Option<usize>>> = parts.iter().map(|p| p[1..].iter().map(|&c| Some(c)).collect()).collect();
        let read_h = reference.forward(&host.tower, &states_h, &parts, &targets, Slot::Opened).expect("host forward");
        let read_c = realized.forward(&host.tower, &states_c, &parts, &targets, Slot::Opened).expect("card forward");
        assert_eq!(read_h, read_c, "round {round}: the faces and the swell");
        let g_h = reference.reverse(&host.tower, &states_h, &parts, None).expect("host reverse");
        let g_c = realized.reverse(&host.tower, &states_c, &parts, None).expect("card reverse");
        assert_eq!(g_h, g_c, "round {round}: the covector over the carried sites");
        let (opening_h, opening_c) = (states_h.clone(), states_c.clone());
        reference.carry(&host.tower, &mut states_h, &opening_h, Slot::Opened).expect("host carry");
        realized.carry(&host.tower, &mut states_c, &opening_c, Slot::Opened).expect("card carry");
        assert_eq!(states_h, states_c, "round {round}: the continuing states with their sections");
        assert!(states_h.iter().all(|s| s.sites.iter().all(|sites| sites.len() == open)), "round {round}: {open} sites open");
    }
}

/// [agent-inferred, October 29] **Participation on the news clock's ticks on the card** (record
/// `2026-10-29_A_COARSE_LEVELS_SITES_ARE_ITS_OWN_TICKS…`, acceptance 6): each level admits its
/// sites at its own ticks, holds its current between them and closes its section at its own count,
/// within a learner's section or across sections; 32 sections equal face by face, covector entry
/// by entry, learner for learner and state for state. Level 1's clock is two bits, under the four
/// or so a class carries, so it ticks none, once or several times at an arrival; a participation
/// section of twelve over learner sections of nine closes level 0's within a call as well.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_clocked_participating_pass_is_the_hosts_for_thirty_two_sections() {
    lockstep(11, 3, 9, 32, false, Faces { news: Some(NewsClock::new(2, 2).expect("a clock")), participation: Some(12), ..Faces::default() });
}

/// The same on the pair contact, an uncompared place held, on a clock of three bits that leaves
/// level 1 still at some arrivals; and without a clock, sections of twelve over learner sections of
/// nine, so the card closes level 0's section within a call and reverses over carried sites.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_clocked_participating_pair_contact_holds_an_uncompared_place_as_the_host_does() {
    lockstep(11, 2, 12, 8, true, Faces { news: Some(NewsClock::new(3, 2).expect("a clock")), participation: Some(12), contact: Some(ContactLaw::Pair), ..Faces::default() });
    lockstep(11, 2, 9, 8, false, Faces { participation: Some(12), ..Faces::default() });
}

/// [agent-inferred, October 29] **The passage on the card** (record
/// `2026-10-29_A_CLOCKED_LEVELS_CONTACTS_HEAR_THE_PASSING_CURRENT…`, acceptance 3, and §8): the
/// contacts of every level the news clock holds read the current passing it, `W₁ˣ x`, beside
/// their read of the level's face; 32 sections equal face by face, covector entry by entry, learner
/// for learner and state for state, on the clock from level 1 (level 1 ticking none, once or
/// several times at an arrival), on three levels from level 2 (levels 0 and 1 ticking at every
/// arrival and carrying no `W₁ˣ`), and on six levels from level 4, past the four levels the law's
/// parameter words once held in place (each level's words now resident on the card).
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_clocked_passage_is_the_hosts_for_thirty_two_sections() {
    lockstep(11, 3, 9, 32, false, Faces { news: Some(NewsClock::new(2, 2).expect("a clock")), passage: true, ..Faces::default() });
    lockstep(11, 3, 9, 32, false, Faces { news: Some(NewsClock::above(2, 2, 2).expect("a clock")), levels: 3, passage: true, ..Faces::default() });
    lockstep(11, 3, 9, 32, false, Faces { news: Some(NewsClock::above(2, 2, 4).expect("a clock")), levels: 6, passage: true, ..Faces::default() });
}

/// [agent-inferred, October 30] **The packets on the card** (record
/// `2026-10-30_A_CLOCKED_LEVEL_HEARS_THE_PACKET_ITS_CLOCK_CLOSED…`, acceptance 6): each clocked
/// level's push, gate and turn hear the read of the packet the fine level's moves carried since its
/// last tick, and the read's covector returns to the fine level's read and scan; 32 sections equal
/// face by face, covector entry by entry, learner for learner and state for state (the open
/// packets among it), on the clock from level 1, on three levels from level 2 with the passage, and
/// at the race's declaration, six levels from level 4 with the passage; then advanced class by
/// class, a stream's open packets carried from each call into the next.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_clocked_packets_are_the_hosts_for_thirty_two_sections() {
    lockstep(11, 3, 9, 32, false, Faces { news: Some(NewsClock::new(2, 2).expect("a clock")), packets: true, ..Faces::default() });
    lockstep(11, 3, 9, 32, false, Faces { news: Some(NewsClock::above(2, 2, 2).expect("a clock")), levels: 3, passage: true, packets: true, ..Faces::default() });
    lockstep(11, 3, 9, 32, false, Faces { news: Some(NewsClock::above(2, 2, 4).expect("a clock")), levels: 6, passage: true, packets: true, ..Faces::default() });
    lockstep(11, 2, 9, 8, false, Faces { news: Some(NewsClock::new(3, 2).expect("a clock")), turned: true, contact: Some(ContactLaw::Pair), packets: true, ..Faces::default() });
    advance_class_by_class(Faces { news: Some(NewsClock::new(2, 2).expect("a clock")), packets: true, ..Faces::default() });
    advance_class_by_class(Faces { news: Some(NewsClock::above(2, 2, 2).expect("a clock")), levels: 3, passage: true, packets: true, ..Faces::default() });
}

/// [agent-inferred, October 30] **The heading on the card** (record
/// `2026-10-30_THE_COARSE_LEVEL_HEADS_FOR_THE_TRACE_OF_WHAT_COMES_NEXT…`, acceptance 6, 9, 12 and
/// 15): each clocked level reads its heading from its modes before the arrival for its closure and
/// after it into the face through its descent, closes the trace of its span at its tick, the
/// closure is read and not learned (record §11), and the face's covector returns to the heading's
/// read, the modes after the cell and the descent; 32 sections equal face by face
/// (the closures among them), covector entry by entry, learner for learner and state for state
/// (the open traces among it), on the clock from level 1, on three levels from level 2 with the
/// passage, and at the race's declaration, six levels from level 4 with the passage; on the turned
/// pair contact with an uncompared place; then advanced class by class, a stream's open traces
/// carried from each call into the next.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_heading_is_the_hosts_for_thirty_two_sections() {
    lockstep(11, 3, 9, 32, false, Faces { news: Some(NewsClock::new(2, 2).expect("a clock")), packets: true, heading: true, ..Faces::default() });
    lockstep(11, 3, 9, 32, false, Faces { news: Some(NewsClock::above(2, 2, 2).expect("a clock")), levels: 3, passage: true, packets: true, heading: true, ..Faces::default() });
    lockstep(11, 3, 9, 32, false, Faces { news: Some(NewsClock::above(2, 2, 4).expect("a clock")), levels: 6, passage: true, packets: true, heading: true, ..Faces::default() });
    lockstep(11, 2, 12, 8, true, Faces { news: Some(NewsClock::new(3, 2).expect("a clock")), turned: true, contact: Some(ContactLaw::Pair), packets: true, heading: true, ..Faces::default() });
    advance_class_by_class(Faces { news: Some(NewsClock::new(2, 2).expect("a clock")), packets: true, heading: true, ..Faces::default() });
    advance_class_by_class(Faces { news: Some(NewsClock::above(2, 2, 2).expect("a clock")), levels: 3, passage: true, packets: true, heading: true, ..Faces::default() });
}

/// [agent-inferred, October 30] **A reread on the opening's ticks** (record
/// `2026-10-30_THE_COARSE_LEVEL_HEADS_FOR_THE_TRACE_OF_WHAT_COMES_NEXT…` §16, acceptance 25): the
/// card refuses it before an opening read; after one, on three levels clocked from level 2 and at
/// the race's declaration (six levels clocked from level 4), each with the passage, the packets and
/// the heading, a candidate tower whose descent moved reads on the opening's ticks as the host's,
/// face for face, closure for closure and end for end; and with the declared reading 32 sections
/// are the host's, receipt for receipt (each refused step's read on the opening's ticks among it).
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_reread_on_the_opening_ticks_is_the_hosts() {
    let card = Card::open(0).expect("the card");
    let clocked = [
        Faces { news: Some(NewsClock::above(2, 2, 2).expect("a clock")), levels: 3, passage: true, packets: true, heading: true, ..Faces::default() },
        Faces { news: Some(NewsClock::above(2, 2, 4).expect("a clock")), levels: 6, passage: true, packets: true, heading: true, ..Faces::default() },
    ];
    for faces in clocked {
        let mut realized = TowerCard::open(&card).expect("the tower's image");
        let (host, _) = learners(11, faces);
        let (streams, section) = (3, 9);
        let classes = passage(11, streams * (section + 1));
        let chunk = classes.len() / streams;
        let parts: Vec<&[usize]> = (0..streams).map(|s| &classes[s * chunk..s * chunk + section + 1]).collect();
        let targets: Vec<Vec<Option<usize>>> = parts.iter().map(|p| p[1..].iter().map(|&c| Some(c)).collect()).collect();
        let opening: Vec<TowerState> = (0..streams).map(|_| host.tower.rest()).collect();
        assert!(realized.forward(&host.tower, &opening, &parts, &targets, Slot::OpeningTicks).is_err(), "a reread on the opening's ticks before an opening read");
        let mut reference = HostPass::default();
        reference.forward(&host.tower, &opening, &parts, &targets, Slot::Opened).expect("host opening");
        realized.forward(&host.tower, &opening, &parts, &targets, Slot::Opened).expect("card opening");
        // The candidate: each clocked level's descent opened again off another part of the keys.
        let mut candidate = host.tower.clone();
        let d = candidate.declaration;
        let first = candidate.news().expect("the clock").first();
        let law = candidate.resident_law().expect("the law");
        let k = keys(1 << 16);
        let mut j = 20000;
        for lv in &law.levels[first..] {
            for i in lv.descent..lv.descent + d.width * d.width {
                candidate.theta[i] = (k[j] as i32 - 128) << 15;
                j += 1;
            }
        }
        let host_read = reference.forward(&candidate, &opening, &parts, &targets, Slot::OpeningTicks).expect("host on the opening's ticks");
        let card_read = realized.forward(&candidate, &opening, &parts, &targets, Slot::OpeningTicks).expect("card on the opening's ticks");
        assert_eq!(host_read, card_read, "the read on the opening's ticks");
        let (mut ends_h, mut ends_c) = (opening.clone(), opening.clone());
        reference.carry(&candidate, &mut ends_h, &opening, Slot::OpeningTicks).expect("host carry");
        realized.carry(&candidate, &mut ends_c, &opening, Slot::OpeningTicks).expect("card carry");
        assert_eq!(ends_h, ends_c, "the ends on the opening's ticks");
        lockstep(11, 3, 9, 32, false, Faces { refusal_ticks: true, ..faces });
    }
}

/// The same beside participation on the clock's ticks and the pair contact, an uncompared place
/// held; and advanced class by class under the clock from level 1 and, on three levels, from
/// level 2.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_clocked_participating_passage_on_the_pair_contact_holds_an_uncompared_place_as_the_host_does() {
    lockstep(11, 2, 12, 8, true, Faces { news: Some(NewsClock::new(3, 2).expect("a clock")), participation: Some(12), contact: Some(ContactLaw::Pair), passage: true, ..Faces::default() });
    advance_class_by_class(Faces { news: Some(NewsClock::new(2, 2).expect("a clock")), passage: true, ..Faces::default() });
    advance_class_by_class(Faces { news: Some(NewsClock::above(2, 2, 2).expect("a clock")), levels: 3, passage: true, ..Faces::default() });
}

/// [agent-inferred, October 29] **The continuing body on the card** (acceptance 2 of the record
/// `2026-10-29_THE_CONTINUING_BODY_RESTS_WITH_ITS_CURRENTS_AND_ONE_OPEN_SECTION_…`): a participating
/// body on four hearing currents hears two passages, is asked, hears the answer and is asked again,
/// on the card as on the host, its whole text and its releases to the bit after every operation;
/// and a card body rested after its first hearing and restarted cold from its text, with a new
/// card realization, is the host's body that never stopped.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_body_hears_asks_and_answers_as_the_hosts_and_resumes_cold() {
    let card = Card::open(0).expect("the card");
    let (learner, _) = learners(11, Faces { participation: Some(12), ..Faces::default() });
    let k = keys(1 << 14);
    let (first, second) = (passage(11, 300), passage(11, 511)[300..].to_vec());
    let prompt: Vec<usize> = (0..9).map(|i| (i * 3 + 1) % 10).collect();
    let answer: Vec<usize> = (0..14).map(|i| (i * 7 + 2) % 10).collect();
    let found = || TowerBody::found(learner.clone(), 4, 12).expect("founded");
    // The rest of the life after the first hearing; each operation's text and release.
    let after = |body: &mut TowerBody, realization: &mut dyn PassRealization| -> Vec<(String, Option<Answer>)> {
        let mut seen = Vec::new();
        body.hear(&second, realization).expect("heard");
        seen.push((body.to_text(), None));
        let asked = body.ask(&prompt, &k, 40, 1, realization).expect("asked");
        seen.push((body.to_text(), Some(asked)));
        body.answer(&answer, realization).expect("answered");
        seen.push((body.to_text(), None));
        let again = body.ask(&prompt, &k, 40, 2, realization).expect("asked");
        seen.push((body.to_text(), Some(again)));
        seen
    };
    let mut host = found();
    let mut reference = HostPass::default();
    host.hear(&first, &mut reference).expect("heard");
    let host_seen = after(&mut host, &mut reference);
    let mut on_card = found();
    let mut realized = TowerCard::open(&card).expect("the tower's image");
    on_card.hear(&first, &mut realized).expect("heard");
    let rested = on_card.to_text();
    assert_eq!(TowerBody::from_text(&rested).expect("restored").to_text(), rested, "the body's text re-encodes equal");
    let card_seen = after(&mut on_card, &mut realized);
    assert!(host_seen.iter().all(|(_, a)| a.as_ref().is_none_or(|a| a.participation.is_some() && !a.released.is_empty())));
    for (i, (h, c)) in host_seen.iter().zip(&card_seen).enumerate() {
        assert_eq!(h, c, "operation {i}: the card's body is the host's");
    }
    drop(realized);
    let mut cold = TowerBody::from_text(&rested).expect("restored");
    let mut fresh = TowerCard::open(&card).expect("the tower's image");
    let cold_seen = after(&mut cold, &mut fresh);
    for (i, (h, c)) in host_seen.iter().zip(&cold_seen).enumerate() {
        assert_eq!(h, c, "operation {i}: the card's body restarted cold is the host's that never stopped");
    }
}

/// The growth's acceptance 7 (record `2026-10-29_THE_BODY_GROWS_BY_COPIES_…`): a body that heard,
/// grown at rest, hears, asks and answers on the card as on the host, and a grown card body
/// restarted cold with a new card realization is the host's that never stopped.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_grown_body_continues_as_the_hosts() {
    let card = Card::open(0).expect("the card");
    let (learner, _) = learners(11, Faces { participation: Some(12), ..Faces::default() });
    let k = keys(1 << 14);
    let founding = keys(learner.tower.growth_draws(2) * 4);
    let (first, second) = (passage(11, 300), passage(11, 511)[300..].to_vec());
    let prompt: Vec<usize> = (0..9).map(|i| (i * 3 + 1) % 10).collect();
    let answer: Vec<usize> = (0..14).map(|i| (i * 7 + 2) % 10).collect();
    let grown = |realization: &mut dyn PassRealization| -> TowerBody {
        let mut body = TowerBody::found(learner.clone(), 4, 12).expect("founded");
        body.hear(&first, realization).expect("heard");
        body.grow(2, &founding).expect("grown");
        body
    };
    let after = |body: &mut TowerBody, realization: &mut dyn PassRealization| -> Vec<(String, Option<Answer>)> {
        let mut seen = Vec::new();
        body.hear(&second, realization).expect("heard");
        seen.push((body.to_text(), None));
        let asked = body.ask(&prompt, &k, 40, 1, realization).expect("asked");
        seen.push((body.to_text(), Some(asked)));
        body.answer(&answer, realization).expect("answered");
        seen.push((body.to_text(), None));
        seen
    };
    let mut reference = HostPass::default();
    let mut host = grown(&mut reference);
    let host_seen = after(&mut host, &mut reference);
    let mut realized = TowerCard::open(&card).expect("the tower's image");
    let mut on_card = grown(&mut realized);
    let rested = on_card.to_text();
    let card_seen = after(&mut on_card, &mut realized);
    for (i, (h, c)) in host_seen.iter().zip(&card_seen).enumerate() {
        assert_eq!(h, c, "operation {i}: the card's grown body is the host's");
    }
    drop(realized);
    let mut cold = TowerBody::from_text(&rested).expect("restored");
    let mut fresh = TowerCard::open(&card).expect("the tower's image");
    let cold_seen = after(&mut cold, &mut fresh);
    for (i, (h, c)) in host_seen.iter().zip(&cold_seen).enumerate() {
        assert_eq!(h, c, "operation {i}: the grown card body restarted cold is the host's that never stopped");
    }
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

/// The pair contact's acceptance: 32 sections equal face by face and covector entry by entry, the
/// learners and their states after each, every contact's product read.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_pair_contact_pass_is_the_hosts_for_thirty_two_sections() {
    lockstep(11, 3, 9, 32, false, Faces { contact: Some(ContactLaw::Pair), ..Faces::default() });
}

/// The foil's acceptance, its biases' covectors summed on their own.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_pair_linear_contact_pass_is_the_hosts_for_thirty_two_sections() {
    lockstep(11, 3, 9, 32, false, Faces { contact: Some(ContactLaw::PairLinear), ..Faces::default() });
}

/// The saved unit learners' declaration in small: a rotor stepping pumped modes on pair contacts
/// beside the pair face, an uncompared place held.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_pumped_rotor_on_pair_contacts_holds_an_uncompared_place_as_the_host_does() {
    lockstep(11, 2, 12, 8, true, Faces { forms: 2, pumped: true, rotor: true, contact: Some(ContactLaw::Pair), ..Faces::default() });
}

/// The same declaration's advance is the host's, class by class.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_pumped_rotor_on_pair_contacts_advance_is_the_hosts_class_by_class() {
    advance_class_by_class(Faces { pumped: true, rotor: true, contact: Some(ContactLaw::Pair), ..Faces::default() });
}

/// The strands' acceptance: 32 sections equal face by face and covector entry by entry, the
/// learners and their states (each stream's residues and sheet) after each.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_stranded_pass_is_the_hosts_for_thirty_two_sections() {
    lockstep(11, 3, 9, 32, false, Faces { strands: true, ..Faces::default() });
}

/// Strands beside the saved unit learners' declaration in small: a rotor stepping pumped modes on
/// pair contacts beside the pair face, each drive reading the faces, an uncompared place held.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_stranded_pumped_rotor_on_pair_contacts_holds_an_uncompared_place_as_the_host_does() {
    lockstep(11, 2, 12, 8, true, Faces { forms: 2, pumped: true, rotor: true, strands: true, contact: Some(ContactLaw::Pair), ..Faces::default() });
}

/// Strands on the foil's contacts beside turned modes.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_stranded_turned_pass_on_the_foil_is_the_hosts_for_eight_sections() {
    lockstep(13, 3, 9, 8, false, Faces { turned: true, strands: true, contact: Some(ContactLaw::PairLinear), ..Faces::default() });
}

/// The stranded advance is the host's, class by class, each stream's residues and sheet carried.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_stranded_advance_is_the_hosts_class_by_class() {
    advance_class_by_class(Faces { pumped: true, rotor: true, strands: true, contact: Some(ContactLaw::Pair), ..Faces::default() });
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

/// The same with participation over sections of twelve: each prompt's nine sites carried open
/// into its next advance, the section closing at the third drawn class and the fourth opening the
/// next.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_participating_advance_is_the_hosts_class_by_class() {
    advance_class_by_class(Faces { participation: Some(12), ..Faces::default() });
}

/// The same under a news clock: each prompt's open face and phase carried from one advance to the
/// next on the card as on the host.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_news_clocked_advance_is_the_hosts_class_by_class() {
    advance_class_by_class(Faces { news: Some(NewsClock::new(2, 2).expect("a clock")), ..Faces::default() });
}

/// The same with participation on the clock's ticks: each level's open section and held current
/// carried from one advance to the next on the card as on the host.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_clocked_participating_advance_is_the_hosts_class_by_class() {
    advance_class_by_class(Faces { news: Some(NewsClock::new(2, 2).expect("a clock")), participation: Some(12), ..Faces::default() });
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
    let paired = Tower::found_on(TowerDeclaration { contact: ContactLaw::Pair, ..declaration(11, false, false, false) }, &keys(1 << 16), TurnLadder::Both).expect("founded");
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
    // A strand's residue at its ring's modulus, and strand residues on a tower without strands.
    let (stranded, _) = learners(11, Faces { strands: true, ..Faces::default() });
    let mut beyond = stranded.tower.rest();
    beyond.strands[0] = 9;
    assert!(realized.forward(&stranded.tower, &[beyond.clone()], &parts, &targets, Slot::Opened).is_err());
    let mut unstranded = host.tower.rest();
    unstranded.strands = vec![0; beyond.strands.len()];
    assert!(realized.forward(&host.tower, &[unstranded], &parts, &targets, Slot::Opened).is_err());
}

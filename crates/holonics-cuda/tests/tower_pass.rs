//! The gated tower's training pass on the card returns the host's bits (`holonics_cuda::hnn::tower`):
//! every face at its target, the whole summed covector, and, section after section, the learner
//! and its streams' states; and the card refuses a declaration it does not carry.
use holonics::hnn::tower::realization::{HostPass, PassRealization, Slot};
use holonics::hnn::tower::{ContactLaw, Tower, TowerDeclaration, TowerLearner, TowerState, TurnLadder};
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

fn declaration(alphabet: usize, gated: bool) -> TowerDeclaration {
    TowerDeclaration { alphabet, width: 8, modes: 8, contacts: 16, levels: 2, gated, turned: false, pumped: false, contact: ContactLaw::Rectifying }
}

fn learners(alphabet: usize) -> (TowerLearner, TowerLearner) {
    let tower = Tower::found_on(declaration(alphabet, true), &keys(1 << 16), TurnLadder::Both).expect("founded");
    (TowerLearner::new(tower.clone(), 5), TowerLearner::new(tower, 5))
}

/// Host against card in lockstep: the opening read and its covector on the same material, then
/// both learners take the section; `compared` holds every other place out of the comparison.
fn lockstep(alphabet: usize, streams: usize, section: usize, sections: usize, holding: bool) {
    let card = Card::open(0).expect("the card");
    let mut realized = TowerCard::open(&card).expect("the tower's image");
    let (mut host, mut carded) = learners(alphabet);
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
    lockstep(11, 3, 9, 6, false);
}

#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_pass_holds_an_uncompared_place_as_the_host_does() {
    lockstep(11, 2, 12, 4, true);
}

/// The card's advance is the host's, class by class: three prompts read whole together, then one
/// class at a time on every stream, each stream's whole face and continuing state equal.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_cards_advance_is_the_hosts_class_by_class() {
    let card = Card::open(0).expect("the card");
    let mut realized = TowerCard::open(&card).expect("the tower's image");
    let alphabet = 13;
    let (host, _) = learners(alphabet);
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
    let ungated = Tower::found_on(declaration(11, false), &keys(1 << 16), TurnLadder::Both).expect("founded");
    let classes = passage(11, 10);
    let parts: Vec<&[usize]> = vec![&classes[..]];
    let targets = vec![classes[1..].iter().map(|&c| Some(c)).collect::<Vec<_>>()];
    assert!(realized.forward(&ungated, &[ungated.rest()], &parts, &targets, Slot::Opened).is_err());
    let (host, _) = learners(11);
    assert!(realized.forward(&host.tower, &[host.tower.rest_with_credit()], &parts, &targets, Slot::Opened).is_err());
    let ragged: Vec<&[usize]> = vec![&classes[..], &classes[..9]];
    let ragged_targets = vec![targets[0].clone(), targets[0][..8].to_vec()];
    assert!(realized.forward(&host.tower, &[host.tower.rest(), host.tower.rest()], &ragged, &ragged_targets, Slot::Opened).is_err());
}

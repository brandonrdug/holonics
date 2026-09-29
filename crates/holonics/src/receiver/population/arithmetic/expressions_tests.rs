//! The numeral port, the expression egg and its release, checked exactly on hand-written lines
//! and on the expressions terrain: one key read in every chart, forms outside the glyph set
//! unreached, the egg's face a face that factors into its chart and sheet parts, a holding result's
//! sheet at least its prior share, the pairing located by the results that hold, shared faces with
//! their carried producer, and a request released by certified draws with its square.

use num_bigint::BigUint;
use num_traits::{One, Zero};

use super::*;
use crate::compression::landmark::context::{
    Capacity, LandmarkDeclaration, LetterFamily, StopPrior,
};
use crate::holarchy::terrain::Draw;
use crate::holarchy::terrain::arithmetic::{
    Chart, Drawn, ExpressionFamily, ExpressionStream, Expressions, Slot,
};

fn tree(population: usize) -> TreeFamily {
    TreeFamily::new(
        LandmarkDeclaration {
            alphabet: BYTES,
            depth: 4,
            forced: 0,
            population: population as u64,
            grain: 16,
            family: LetterFamily::cells(),
            prior: StopPrior::half(),
            capacity: Capacity::Unbounded,
        },
        0,
    )
    .unwrap()
}

fn cells(text: &str) -> Vec<usize> {
    text.bytes().map(usize::from).collect()
}

/// The port's events over a text.
fn events(text: &str) -> Vec<PortEvent> {
    let mut port = ExpressionPort::new();
    cells(text)
        .into_iter()
        .map(|cell| port.advance(cell))
        .filter(|event| *event != PortEvent::None)
        .collect()
}

fn operand(base: u64, value: u64) -> Operand {
    Operand {
        base,
        word: encode(base, &BigUint::from(value)).unwrap(),
    }
}

/// **One key in every chart**: the record's three lines read to one key (`347`, a product glyph,
/// `5102`) and close on `1770394`, in bases 10 and 16; the key is read at the relation glyph, `==`
/// included.
#[test]
fn the_port_reads_one_key_in_every_chart() {
    for (text, base, operator) in [
        ("so 347 × 5102 = 1770394.", 10, Operator::Cross),
        ("assert!(0x15B * 0x13EE == 0x1B039A);", 16, Operator::Star),
        (
            "example : 0x15B * 0x13EE = 0x1B039A := by norm_num",
            16,
            Operator::Star,
        ),
        ("so 0b101 · 0b11 = 0b1111.", 2, Operator::Dot),
    ] {
        let mut port = ExpressionPort::new();
        let mut keyed = None;
        let mut closed = None;
        for cell in cells(text) {
            match port.advance(cell) {
                PortEvent::Keyed => keyed = port.key(),
                PortEvent::Closed { result } => closed = result,
                PortEvent::Broken => panic!("{text} broke"),
                PortEvent::None => {}
            }
        }
        let key = keyed.unwrap_or_else(|| panic!("{text} keyed"));
        assert_eq!(key.operator, operator);
        assert_eq!(key.left.base, base);
        let (a, c) = (key.left.value(), key.right.value());
        let result = closed.unwrap();
        assert_eq!(result.base, base);
        assert_eq!(result.value(), a * c);
        assert_eq!(port.phase(), ExpressionPhase::Outside);
    }
    assert_eq!(
        events("so 12 + 7 = 19.")[1],
        PortEvent::Closed {
            result: Some(operand(10, 19))
        }
    );
}

/// **Forms outside the glyph set are unreached**, named by their glyphs: Lean's `(2 : ℕ)`, Rust's
/// `2u64`, the separators `1_000` and `1,000` (whose tail is no numeral of its own), subtraction, a
/// word numeral and a chain; a list `3, 4` still begins a numeral after its space.
#[test]
fn the_port_does_not_reach_forms_outside_the_glyph_set() {
    for text in [
        "example : (2 : ℕ) + 2 = 4 := by norm_num",
        "assert!(2u64 + 2 == 4);",
        "so 1_000 + 1 = 1001.",
        "so 1,000 + 1 = 1,001.",
        "so 5 - 3 = 2.",
        "so two + 2 = 4.",
    ] {
        assert!(
            !events(text).contains(&PortEvent::Keyed),
            "{text} was keyed"
        );
    }
    assert_eq!(
        events("so 2 + 2 + 2 = 6."),
        Vec::<PortEvent>::new(),
        "a chain is unreached"
    );
    assert_eq!(
        events("so 3, 4 + 1 = 5.")[0],
        PortEvent::Keyed,
        "a numeral after a list's comma and space"
    );
    assert_eq!(
        events("so 2 + 2 = four."),
        vec![PortEvent::Keyed, PortEvent::Broken]
    );
}

/// Read a stream through the egg, checking at every cell that the egg's face is a face, that its
/// entry at the cell is the face `receive` returns, and that the face is its chart part times its
/// sheet part; each closed expression's sheet parts over its result cells multiply to the
/// receipt's `Σ_k W_k (A_k + B_k)`, at least the living keys' weighted priors on a holding result.
///
/// The whole face is read only where `faces` asks: it is 256 exact entries a cell.
fn read(egg: &mut ExpressionEgg, stream: &[usize], faces: bool) -> Vec<ExpressionReceipt> {
    let mut receipts = Vec::new();
    let mut product = Rat::one();
    let mut closed = egg.counts().closed;
    for &cell in stream {
        let face = faces.then(|| egg.face().unwrap());
        if let Some(face) = &face {
            assert_eq!(face.iter().cloned().sum::<Rat>(), Rat::one());
        }
        let received = egg.receive(cell).unwrap();
        if let Some(face) = &face {
            assert_eq!(received, face[cell]);
        }
        let last = egg.last().unwrap();
        assert_eq!(&last.chart * &last.sheet, received);
        product = &product * &last.sheet;
        if egg.counts().closed > closed {
            closed = egg.counts().closed;
            let receipt = egg.receipt().unwrap().clone();
            let telescope: Rat = receipt
                .readings
                .iter()
                .map(|reading| &reading.weight * (&reading.holds + &reading.free))
                .sum();
            assert_eq!(product, telescope);
            let prior: Rat = receipt
                .readings
                .iter()
                .filter(|reading| reading.held)
                .map(|reading| &reading.weight * &reading.prior)
                .sum();
            assert!(product >= prior);
            receipts.push(receipt);
        }
        if egg.port().phase() == ExpressionPhase::Outside && egg.counts().closed == closed {
            product = Rat::one();
        }
    }
    receipts
}

fn text(stream: &ExpressionStream) -> Vec<usize> {
    stream.cells.clone()
}

/// **The pairing is located by the results that hold**, and every result is reached and held with
/// its square: on a Rust stream the power dies at the first `^` whose results part, with its
/// receipt; on Lean and prose streams the carry-free sum dies; the holds sheet counts every
/// expression held under the located key.
#[test]
fn the_egg_locates_the_pairing_and_holds_every_result() {
    let mut draw = Draw::new(2_026_092_953);
    for base in [2u64, 10, 16] {
        let family = ExpressionFamily {
            base,
            operands: 1 << 6,
            exponents: 4,
        };
        let expressions = Expressions::draw(family, 8, &mut draw).unwrap();
        for chart in Chart::ALL {
            let stream = expressions.emit(chart).unwrap();
            let mut egg = ExpressionEgg::new(0, tree(stream.cells.len())).unwrap();
            let receipts = read(&mut egg, &text(&stream), false);
            let counts = egg.counts().clone();
            assert_eq!(counts.keyed, 8);
            assert_eq!(counts.closed, 8);
            assert_eq!(counts.held, 8, "{chart:?} base {base}");
            assert_eq!(counts.unreached + counts.broken + counts.failed, 0);
            assert_eq!(counts.square_failures + counts.rebase_failures, 0);
            let carets = expressions
                .drawn()
                .iter()
                .filter(|drawn| drawn.slot == Slot::Caret)
                .count();
            if carets > 0 {
                assert_eq!(egg.located(), Some(chart.caret()), "{chart:?} base {base}");
                let dead = egg
                    .pairing()
                    .iter()
                    .find(|key| key.death.is_some())
                    .unwrap();
                assert_ne!(dead.producer, chart.caret());
                assert!(dead.death.as_ref().unwrap().held == vec![chart.caret()]);
                let survivor = egg
                    .pairing()
                    .iter()
                    .find(|key| key.death.is_none())
                    .unwrap();
                assert_eq!((survivor.held, survivor.free), (8, 0));
            }
            for (receipt, truth) in receipts.iter().zip(&stream.truths) {
                assert_eq!(receipt.result.as_ref().unwrap().value(), truth.value);
                assert!(receipt.fibre.contains(&truth.producer));
            }
        }
    }
}

/// **Shared faces name their carried producer** (`2 + 2`, `2 · 2`, `2 ^ 2`; `10 + 10 = 10 · 10 =
/// 100` in base 2): each receipt's fibre holds the three admitted producers and its readings the
/// carried one, with the holds and free contributions whose sum telescopes the result cells' sheet.
#[test]
fn shared_faces_name_their_carried_producer() {
    let text = "so 2 + 2 = 4.\nso 2 × 2 = 4.\nso 2 ^ 2 = 4.\nso 0b10 + 0b10 = 0b100.\nso 0b10 * 0b10 = 0b100.\n";
    let stream = cells(text);
    let mut egg = ExpressionEgg::new(0, tree(stream.len())).unwrap();
    let receipts = read(&mut egg, &stream, true);
    assert_eq!(receipts.len(), 5);
    let carried = [
        Producer::Sum,
        Producer::Product,
        Producer::Power,
        Producer::Sum,
        Producer::Product,
    ];
    for (receipt, producer) in receipts.iter().zip(carried) {
        assert!(receipt.fibre.contains(&Producer::Sum));
        assert!(receipt.fibre.contains(&Producer::Product));
        assert!(receipt.fibre.contains(&Producer::Power));
        let held: Vec<Producer> = receipt
            .readings
            .iter()
            .filter(|reading| reading.held)
            .map(|reading| reading.producer)
            .collect();
        assert!(held.contains(&producer));
    }
    // `2 ^ 2` parts the pairing: the carry-free sum reads `2 ⊕ 2 = 0`.
    assert_eq!(receipts[2].deaths, vec![Producer::CarryFree]);
    assert_eq!(egg.located(), Some(Producer::Power));
}

/// **A request is released by certified draws** (egg packing): after a Lean stream locates the
/// power, `0x15B ^ 0x3` releases `0x27D8AA3` glyph by glyph under declared keys, each draw's cell
/// `[0, 1)`, then the end, with the square and its rebase, three carry words and `347³`'s
/// factorization; a Rust stream's `^` releases the carry-free sum `0x12B5`; before the pairing is
/// located a `^` request is held; a request that does not reach the awaited result is refused.
#[test]
fn a_request_is_released_by_certified_draws() {
    let keys: Vec<Rat> = (0..16u32)
        .map(|j| Rat::new((2 * j + 1).into(), 32.into()))
        .collect();
    let fresh = ExpressionEgg::new(0, tree(64)).unwrap();
    let request = cells("example : 0x15B ^ 0x3 = ");
    match fresh.release(&request, &keys).unwrap() {
        ExpressionRelease::Hold { producers, .. } => {
            assert_eq!(producers, vec![Producer::Power, Producer::CarryFree]);
        }
        other => panic!("a plural pairing released {other:?}"),
    }
    let product = cells("example : 0x15B * 0x13EE = ");
    let ExpressionRelease::Released(released) = fresh.release(&product, &keys).unwrap() else {
        panic!("a product is held");
    };
    assert_eq!(released.glyphs, b"0x1B039A");
    let family = ExpressionFamily {
        base: 16,
        operands: 1 << 13,
        exponents: 4,
    };
    let caret = Expressions::new(
        family,
        vec![Drawn {
            slot: Slot::Caret,
            left: 347,
            right: 5102,
            exponent: 3,
        }],
    )
    .unwrap();
    for (chart, glyphs, value) in [
        (Chart::Lean, &b"0x27D8AA3"[..], 41_781_923u32),
        (Chart::Rust, &b"0x12B5"[..], 4789),
    ] {
        let stream = caret.emit(chart).unwrap();
        let mut egg = ExpressionEgg::new(0, tree(stream.cells.len() + 64)).unwrap();
        read(&mut egg, &stream.cells, false);
        assert_eq!(egg.located(), Some(chart.caret()));
        let (left, right) = caret.drawn()[0].operands(chart);
        let request: Vec<usize> = chart
            .request(chart.caret(), 16, left, right)
            .unwrap()
            .into_iter()
            .map(usize::from)
            .collect();
        let ExpressionRelease::Released(released) = egg.release(&request, &keys).unwrap() else {
            panic!("a located pairing is held");
        };
        assert_eq!(released.glyphs, glyphs);
        assert_eq!(released.value, BigUint::from(value));
        assert_eq!(released.producer, chart.caret());
        assert!(released.square && released.rebase);
        assert_eq!(released.draws.len(), glyphs.len());
        for draw in &released.draws {
            assert_eq!(
                (draw.prior_upper.clone(), draw.through_lower.clone()),
                (Rat::zero(), Rat::one())
            );
        }
        assert_eq!(released.end.class, 1);
        assert_eq!(released.prefix, b"0x");
        if chart == Chart::Lean {
            assert_eq!(released.consequence.carries.len(), 3);
            assert_eq!(released.factorization, Some(vec![(347, 3)]));
        }
    }
    assert!(fresh.release(&cells("so 2 + "), &keys).is_err());
    assert!(fresh.release(&product, &keys[..3]).is_err());
}

/// The egg's readout is the pairing's one factor, and its declaration names the port, the pairing
/// and the byte tree; a tree over another alphabet is refused.
#[test]
fn the_egg_reads_out_its_pairing() {
    let egg = ExpressionEgg::new(1, tree(8)).unwrap();
    let Readout::Keys(keys) = egg.readout() else {
        panic!("the pairing's keys");
    };
    assert_eq!(keys.spaces, vec![2]);
    assert_eq!(keys.survivors, vec![vec![vec![0], vec![1]]]);
    assert_eq!(
        keys.masses,
        vec![vec![
            Rat::new(1.into(), 2.into()),
            Rat::new(1.into(), 2.into())
        ]]
    );
    assert_eq!(egg.declaration().parts.len(), 3);
    let narrow = TreeFamily::new(
        LandmarkDeclaration {
            alphabet: 16,
            depth: 2,
            forced: 0,
            population: 8,
            grain: 16,
            family: LetterFamily::cells(),
            prior: StopPrior::half(),
            capacity: Capacity::Unbounded,
        },
        0,
    )
    .unwrap();
    assert!(ExpressionEgg::new(0, narrow).is_err());
}

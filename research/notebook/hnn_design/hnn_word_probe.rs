//! F1 exact byte-word work preflight. The choosing probe projects the full work; the separately
//! pinned bounded validation part may be read once with `terminated`. Owner-only inputs stay
//! private; output is counts, exact equality and integer wall time.

use std::time::Instant;

use holonics::ratio::Rat;
use holonics::receiver::population::{Family, Likelihood, WORD_END, WordDictionary, WordFamily};
use num_bigint::BigInt;

fn take<const N: usize>(raw: &[u8], at: &mut usize) -> [u8; N] {
    let end = *at + N;
    let chunk: [u8; N] = raw[*at..end]
        .try_into()
        .expect("a complete private declaration");
    *at = end;
    chunk
}

fn dictionary(path: &str) -> (WordDictionary, u64) {
    let raw = std::fs::read(path).expect("the owner-only dictionary");
    let mut at = 0;
    let count = u32::from_le_bytes(take(&raw, &mut at)) as usize;
    let stop_n = u64::from_le_bytes(take(&raw, &mut at));
    let stop_d = u64::from_le_bytes(take(&raw, &mut at));
    let description = u64::from_le_bytes(take(&raw, &mut at));
    let mut words = Vec::with_capacity(count);
    let mut weights = Vec::with_capacity(count);
    for _ in 0..count {
        let length = u16::from_le_bytes(take(&raw, &mut at)) as usize;
        let weight = u64::from_le_bytes(take(&raw, &mut at));
        words.push(raw[at..at + length].to_vec());
        at += length;
        weights.push(weight);
    }
    assert_eq!(at, raw.len(), "the exact dictionary declaration");
    let total: u64 = weights.iter().sum();
    let face = weights
        .iter()
        .map(|&weight| Rat::new(BigInt::from(weight), BigInt::from(total)))
        .collect();
    let stop = Rat::new(BigInt::from(stop_n), BigInt::from(stop_d));
    (
        WordDictionary::new(words, face, stop).expect("the fitted word law"),
        description,
    )
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let (dictionary_path, cut_path, count, terminated) = match args.as_slice() {
        [dictionary_path, cut_path, count] => (dictionary_path, cut_path, count, false),
        [dictionary_path, cut_path, count, flag] if flag == "terminated" => {
            (dictionary_path, cut_path, count, true)
        }
        _ => panic!(
            "usage: hnn_word_probe <private-dictionary.bin> <private-cut.bin> <byte-count> [terminated]"
        ),
    };
    let count: usize = count.parse().expect("a byte-count aperture");
    let (dictionary, description) = dictionary(dictionary_path);
    let raw = std::fs::read(cut_path).expect("the private choosing cut");
    assert_eq!(raw.len() % 2, 0, "u16 cells");
    let mut family = WordFamily::new("F1 choosing preflight".to_owned(), description, dictionary);
    let start = Instant::now();
    let mut received = 0;
    let mut bytes = Vec::with_capacity(count);
    for pair in raw.chunks_exact(2) {
        let cell = u16::from_le_bytes([pair[0], pair[1]]) as usize;
        if cell >= 256 {
            continue;
        }
        family
            .receive(cell)
            .expect("the singleton fallback admits every byte");
        bytes.push(cell as u8);
        received += 1;
        if received == count {
            break;
        }
    }
    assert_eq!(received, count, "the choosing cut holds the aperture");
    let byte_ms = start.elapsed().as_millis();
    if terminated {
        family
            .receive(WORD_END)
            .expect("the actual part's stop is admitted");
        let Likelihood::Exact(received_mass) = family.likelihood() else {
            panic!("the word family's mass is exact");
        };
        let parsed_mass = family.dictionary().parse_mass(&bytes);
        assert_eq!(
            received_mass, parsed_mass,
            "the prequential word face sums every parse and the stop"
        );
        println!(
            "word-family bounded held-out passage: {received} bytes and END, exact parse/face mass equal; byte receiver {byte_ms} ms, total {} ms; declaration {description} bits",
            start.elapsed().as_millis()
        );
    } else {
        println!(
            "word-family choosing work probe: {received} bytes, {byte_ms} ms; declaration {description} bits"
        );
    }
}

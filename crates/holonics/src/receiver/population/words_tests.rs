use super::words::{
    EncodingSeparator, ParseError, SeparatorCause, WORD_END, WordDictionary, WordFamily,
};
use super::{Family, Likelihood, Population, Readout};
use crate::ratio::{Rat, rat};

fn dictionary() -> WordDictionary {
    WordDictionary::new(
        vec![b"a".to_vec(), b"bc".to_vec(), b"bd".to_vec()],
        vec![rat(1, 3), rat(1, 3), rat(1, 3)],
        rat(1, 2),
    )
    .expect("prefix-free known-truth vocabulary")
}

#[test]
fn the_known_truth_parse_decoder_mass_and_append_square_agree_exactly() {
    let dictionary = dictionary();
    let bytes = b"abc";
    let parse = dictionary.encode(bytes).expect("known-truth parse");
    assert_eq!(parse, [0, 1]);
    assert_eq!(dictionary.decode(&parse).expect("decode"), bytes);
    assert_eq!(dictionary.parse_mass(bytes), rat(1, 72));

    let square = dictionary
        .append_square(b"a", 1)
        .expect("the decoder and append transport square");
    assert_eq!(square.encoding, [0]);
    assert_eq!(square.successor, bytes);
    assert_eq!(square.next_encoding, [0, 1]);
    assert_eq!(square.transported_encoding, [0, 1]);
}

#[test]
fn the_word_family_is_an_exact_population_face_through_termination() {
    let mut family = WordFamily::new("known words".to_string(), 3, dictionary());
    let mut product = Rat::from_integer(1.into());
    for byte in b"abc" {
        let face = family.face().expect("face");
        assert_eq!(face.iter().sum::<Rat>(), Rat::from_integer(1.into()));
        let cell = usize::from(*byte);
        let arrived = family.receive(cell).expect("byte");
        assert_eq!(arrived, face[cell]);
        product *= arrived;
    }
    let face = family.face().expect("terminal face");
    assert_eq!(face[WORD_END], rat(1, 2));
    product *= family.receive(WORD_END).expect("termination");
    assert_eq!(product, rat(1, 72));
    assert_eq!(family.likelihood(), Likelihood::Exact(rat(1, 72)));
    assert!(matches!(family.readout(), Readout::Words(_)));

    let mut population = Population::new(vec![Box::new(WordFamily::new(
        "known words".to_string(),
        3,
        dictionary(),
    ))])
    .expect("population family");
    let cells: Vec<usize> = b"abc".iter().map(|byte| usize::from(*byte)).collect();
    let mut passage = cells;
    passage.push(WORD_END);
    population.receive_passage(&passage).expect("word passage");
}

fn byte_fallback_dictionary() -> WordDictionary {
    let mut words: Vec<Vec<u8>> = (0u8..=u8::MAX).map(|byte| vec![byte]).collect();
    words.push(b"ab".to_vec());
    let token_face = vec![rat(1, 257); 257];
    WordDictionary::new(words, token_face, rat(1, 2)).expect("ambiguous fallback dictionary")
}

#[test]
fn fallback_and_multi_byte_word_sum_both_parses_with_the_stop_mass() {
    let fallback = byte_fallback_dictionary();
    assert!(!fallback.is_uniquely_decodable());

    let expected = rat(1, 1028) + rat(1, 528_392);
    assert_eq!(fallback.parse_mass(b"ab"), expected);
    let Err(ParseError::NotUniquelyDecodable { parses }) = fallback.encode(b"ab") else {
        panic!("the byte fallback and the multi-byte word give two parses")
    };
    assert_eq!(parses.len(), 2);
    assert!(parses.contains(&vec![97, 98]));
    assert!(parses.contains(&vec![256]));

    let mut family = WordFamily::new("fallback with words".to_string(), 9, fallback);
    let mut product = Rat::from_integer(1.into());
    for cell in [usize::from(b'a'), usize::from(b'b'), WORD_END] {
        let face = family.face().expect("face");
        assert_eq!(face.iter().sum::<Rat>(), Rat::from_integer(1.into()));
        let arrived = family.receive(cell).expect("receive");
        assert_eq!(arrived, face[cell]);
        product *= arrived;
    }
    assert_eq!(product, expected);

    let separator = byte_fallback_dictionary()
        .append_square(b"a", 256)
        .unwrap_err();
    assert_eq!(separator.cause, SeparatorCause::SuccessorHasMultipleParses);
    let (first, second) = separator.competing_encodings.expect("two exact parses");
    assert_eq!(byte_fallback_dictionary().decode(&first).unwrap(), b"aab");
    assert_eq!(byte_fallback_dictionary().decode(&second).unwrap(), b"aab");
    assert_ne!(first, second);

    assert!(matches!(
        dictionary().append_square(b"z", 0),
        Err(EncodingSeparator {
            cause: SeparatorCause::SourceHasNoParse,
            ..
        })
    ));
}

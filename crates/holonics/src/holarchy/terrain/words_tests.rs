use super::source::{ContextTree, TreeSource};
use super::words::{WordTerrain, WordVocabulary};
use crate::ratio::Rat;
use crate::receiver::population::WordDictionary;
use num_bigint::BigInt;

#[test]
fn fixed_width_word_chart_recovers_observed_words_without_inventing_any() {
    let vocabulary = WordVocabulary::new(vec![vec![0x61, 0x62], vec![0x63, 0x64]])
        .expect("declared words are distinct and fixed width");
    let tree = ContextTree::new(3, vec![vec![]]).expect("one leaf covers the index alphabet");
    let source = TreeSource::new(tree, 3, vec![vec![1, 1, 1]], vec![])
        .expect("positive exact faces and empty context");
    let terrain = WordTerrain::new(vocabulary, source).expect("source includes terminal index");

    let observed = [0, 1, terrain.terminal()];
    let bytes = terrain
        .encode_terminated(&observed)
        .expect("completed source passage ends at stop");
    assert_eq!(bytes, b"abcd");
    assert_eq!(
        terrain.decode(&bytes).expect("both words are known"),
        [0, 1]
    );
    let source_passage = terrain
        .source()
        .passage(&observed)
        .expect("stop is a source cell");
    assert_eq!(source_passage.counts.iter().flatten().sum::<u64>(), 3);
    // The source gives each of [word 0, word 1, END] exact mass 1/3. The unique byte parse
    // therefore carries its source probability 1/27, including the stop, with no extra path.
    let dictionary = WordDictionary::new(
        terrain.vocabulary().words().to_vec(),
        vec![Rat::new(BigInt::from(1), BigInt::from(2)); 2],
        Rat::new(BigInt::from(1), BigInt::from(3)),
    )
    .expect("the terrain's exact source face");
    assert_eq!(
        dictionary.parse_mass(&bytes),
        Rat::new(BigInt::from(1), BigInt::from(27))
    );

    let bad = b"abef";
    assert!(
        terrain.decode(bad).is_err(),
        "an unknown chunk is never emitted"
    );
    assert!(
        terrain.decode(b"abc").is_err(),
        "partial byte words are refused"
    );
    assert!(
        terrain
            .encode_terminated(&[0, terrain.terminal(), 1])
            .is_err()
    );
}

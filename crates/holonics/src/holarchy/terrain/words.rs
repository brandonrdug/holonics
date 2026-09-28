//! **A known-truth word terrain: a drawn finite vocabulary over a drawn tree navigator.**
//!
//! [definition; agent-inferred] A [`WordTerrain`] couples a finite vocabulary of fixed-width,
//! distinct byte words to a [`TreeSource`] whose alphabet is the word indices plus one terminal
//! index. Fixed width makes the vocabulary uniquely decodable; the terminal index is part of the
//! source word and therefore part of its exact source code. For a byte passage `x`, the consuming
//! segmentation law is `P_G(x) = Σ_(D z=x) P(z)`, with the terminal index in every completed `z`.
//! In this terrain the decoder has at most one parse, but `receiver::population::merge` owns the
//! general segmentation mass and merge price. It does not imply a curated-code acceptance.
//!
//! The computational object is the helical pair interaction of the word navigator and byte
//! receiver at their common section. Of the six winding objects this owner touches **faces and
//! placement** (word-index faces placed on byte words) and the **tower thread** (the indexed word
//! sequence lifts to its byte passage); helix, pair, cell holonomy and tube remain attached through
//! the tree source and population.

use super::{Draw, TerrainError, TreeSource, TreeSourceFamily, TreeSourceTruth, refuse};

/// The finite vocabulary. All entries have one exact byte width, so concatenation has one parse.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordVocabulary {
    words: Vec<Vec<u8>>,
    width: usize,
}

impl WordVocabulary {
    /// A declared vocabulary, refused unless it is nonempty, fixed-width and duplicate-free.
    pub fn new(words: Vec<Vec<u8>>) -> Result<Self, TerrainError> {
        let width = words.first().map_or(0, Vec::len);
        if width == 0 || words.is_empty() || words.iter().any(|word| word.len() != width) {
            return Err(refuse(
                "a word vocabulary",
                "it is nonempty and every word has the same positive byte width",
            ));
        }
        let distinct: std::collections::BTreeSet<&[u8]> = words.iter().map(Vec::as_slice).collect();
        if distinct.len() != words.len() {
            return Err(refuse("a word vocabulary", "its byte words are distinct"));
        }
        Ok(Self { words, width })
    }

    /// Its number of words.
    pub fn len(&self) -> usize {
        self.words.len()
    }

    /// Whether it contains no words (declared vocabularies are never empty).
    pub fn is_empty(&self) -> bool {
        self.words.is_empty()
    }

    /// The exact width shared by every word.
    pub fn word_width(&self) -> usize {
        self.width
    }

    /// The vocabulary in word-index order.
    pub fn words(&self) -> &[Vec<u8>] {
        &self.words
    }

    /// The word at an index.
    pub fn get(&self, index: usize) -> Option<&[u8]> {
        self.words.get(index).map(Vec::as_slice)
    }
}

/// The declared draw family. `word_count` is the number of byte words; one more tree-source
/// symbol is reserved for termination.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WordTerrainFamily {
    pub word_count: usize,
    pub depth: usize,
    pub grid: u64,
}

/// Exact truth attached to a word passage, including the stop symbol's source code.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordTerrainTruth {
    /// Vocabulary indexed by the source's word alphabet.
    pub vocabulary: WordVocabulary,
    /// The source on word indices and its terminal index.
    pub source: TreeSource,
    /// Exact leaf-chain law and entropy-rate receipt for that source.
    pub source_truth: TreeSourceTruth,
    /// The terminal source index, equal to `vocabulary.len()`.
    pub terminal: usize,
}

/// A realized word passage. `indices` contains the terminal index iff `terminated`; `bytes` is
/// the lossless byte chart of the nonterminal indices. The exact source code includes the stop.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordPassage {
    pub indices: Vec<usize>,
    pub bytes: Vec<u8>,
    pub terminated: bool,
}

/// A drawn vocabulary and tree source over its word indices.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordTerrain {
    vocabulary: WordVocabulary,
    source: TreeSource,
    terminal: usize,
}

impl WordTerrain {
    /// Couple a declared vocabulary to a drawn tree source. The source alphabet must contain one
    /// terminal symbol after the vocabulary.
    pub fn new(vocabulary: WordVocabulary, source: TreeSource) -> Result<Self, TerrainError> {
        let terminal = vocabulary.len();
        if source.tree().alphabet() != terminal.checked_add(1).unwrap_or(0) {
            return Err(refuse(
                "a word terrain",
                "its tree-source alphabet is vocabulary indices plus one terminal index",
            ));
        }
        Ok(Self {
            vocabulary,
            source,
            terminal,
        })
    }

    /// Draw a uniformly shuffled fixed-width vocabulary and a tree source over its indices plus
    /// termination. The byte words are the fixed-width encodings of a draw-permuted index set.
    pub fn draw(family: WordTerrainFamily, draw: &mut Draw) -> Result<Self, TerrainError> {
        if family.word_count == 0 || family.depth == 0 {
            return Err(refuse(
                "a word-terrain family",
                "it has at least one word and positive source depth",
            ));
        }
        let alphabet = family.word_count.checked_add(1).ok_or_else(|| {
            refuse(
                "a word-terrain family",
                "its word alphabet fits a machine index",
            )
        })?;
        let width = byte_width(family.word_count);
        let mut labels: Vec<usize> = (0..family.word_count).collect();
        for i in (1..labels.len()).rev() {
            labels.swap(i, draw.below(i + 1));
        }
        let words = labels
            .into_iter()
            .map(|label| fixed_width_bytes(label, width))
            .collect();
        let vocabulary = WordVocabulary::new(words)?;
        let source = TreeSource::draw(
            &TreeSourceFamily {
                alphabet,
                depth: family.depth,
                grid: family.grid,
            },
            draw,
        )?;
        Self::new(vocabulary, source)
    }

    /// Draw from a seed through the terrain's exact seeded navigator.
    pub fn draw_seeded(family: WordTerrainFamily, seed: u64) -> Result<Self, TerrainError> {
        Self::draw(family, &mut Draw::new(seed))
    }

    /// The known-truth receipt.
    pub fn truth(&self) -> Result<WordTerrainTruth, TerrainError> {
        Ok(WordTerrainTruth {
            vocabulary: self.vocabulary.clone(),
            source: self.source.clone(),
            source_truth: self.source.truth()?,
            terminal: self.terminal,
        })
    }

    /// The byte vocabulary.
    pub fn vocabulary(&self) -> &WordVocabulary {
        &self.vocabulary
    }

    /// The exact tree source over word indices and termination.
    pub fn source(&self) -> &TreeSource {
        &self.source
    }

    /// The terminal source index.
    pub fn terminal(&self) -> usize {
        self.terminal
    }

    /// Encode a sequence of word indices; terminal indices are not ordinary words.
    pub fn encode_indices(&self, indices: &[usize]) -> Result<Vec<u8>, TerrainError> {
        let mut bytes = Vec::with_capacity(indices.len().saturating_mul(self.vocabulary.width));
        for &index in indices {
            let word = self.vocabulary.get(index).ok_or_else(|| {
                refuse(
                    "a word passage",
                    "every emitted index names a vocabulary word",
                )
            })?;
            bytes.extend_from_slice(word);
        }
        Ok(bytes)
    }

    /// Encode a completed index passage, including its source terminal symbol. The stop has no
    /// byte word: it closes the decoded sequence and is charged by the source law.
    pub fn encode_terminated(&self, indices: &[usize]) -> Result<Vec<u8>, TerrainError> {
        if indices.last() != Some(&self.terminal)
            || indices[..indices.len().saturating_sub(1)].contains(&self.terminal)
        {
            return Err(refuse(
                "a completed word passage",
                "it ends in exactly one terminal source index",
            ));
        }
        self.encode_indices(&indices[..indices.len() - 1])
    }

    /// Decode a byte passage. Fixed-width boundaries and membership in the drawn vocabulary are
    /// checked exactly; malformed or spurious byte words are refused.
    pub fn decode(&self, bytes: &[u8]) -> Result<Vec<usize>, TerrainError> {
        if bytes.len() % self.vocabulary.width != 0 {
            return Err(refuse(
                "a word decode",
                "the byte passage is a whole number of vocabulary word widths",
            ));
        }
        let mut indices = Vec::with_capacity(bytes.len() / self.vocabulary.width);
        for chunk in bytes.chunks_exact(self.vocabulary.width) {
            let index = self
                .vocabulary
                .words
                .iter()
                .position(|word| word.as_slice() == chunk)
                .ok_or_else(|| refuse("a word decode", "every byte chunk is in the vocabulary"))?;
            indices.push(index);
        }
        Ok(indices)
    }

    /// Emit at most `maximum_indices` source symbols. If termination is met, it is included in
    /// `indices`, charged in `source_code`, and excluded from byte output. A passage that reaches
    /// the bound without stop remains explicitly unterminated.
    pub fn emit(
        &self,
        maximum_indices: usize,
        draw: &mut Draw,
    ) -> Result<(WordPassage, super::source::Passage), TerrainError> {
        let sampled = self.source.emit(maximum_indices, draw);
        let stop_at = sampled.iter().position(|&index| index == self.terminal);
        let (indices, terminated) = match stop_at {
            Some(position) => (sampled[..=position].to_vec(), true),
            None => (sampled, false),
        };
        let byte_indices = if terminated {
            &indices[..indices.len() - 1]
        } else {
            &indices[..]
        };
        let bytes = self.encode_indices(byte_indices)?;
        let source_code = self.source.passage(&indices)?;
        Ok((
            WordPassage {
                indices,
                bytes,
                terminated,
            },
            source_code,
        ))
    }
}

fn byte_width(count: usize) -> usize {
    let mut width = 1;
    let mut capacity = 256u128;
    while capacity < count as u128 {
        width += 1;
        capacity *= 256;
    }
    width
}

fn fixed_width_bytes(index: usize, width: usize) -> Vec<u8> {
    let mut value = index;
    let mut bytes = vec![0; width];
    for slot in bytes.iter_mut().rev() {
        *slot = (value & 0xff) as u8;
        value >>= 8;
    }
    bytes
}

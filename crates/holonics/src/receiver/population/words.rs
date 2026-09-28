//! Exact segmentation of byte passages by a finite uniquely decodable dictionary.
//!
//! For dictionary words `w` with exact token face `p(w)` and continuation mass `c=1-s`, each
//! parse `z` has terminated mass `P(z)=s·∏ᵢ(c p(zᵢ))`. `SegmentationLattice::parse_mass` sums this
//! over every dictionary path decoding to the supplied bytes. The family reads the same law
//! prequentially over byte classes plus one explicit end class. The dictionary and its declared
//! prior cost are part of the family's declaration; termination is always scored.

use std::collections::BTreeSet;

use crate::ratio::Rat;
use crate::receiver::population::{
    Declaration, Family, Likelihood, PopulationError, Readout, Work, refuse,
};
use num_traits::Zero;

/// The end-of-passage class, after the 256 byte values.
pub const WORD_END: usize = 256;

/// A byte segmentation is absent or nonunique, or a declared word index is outside the dictionary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParseError {
    /// No dictionary path decodes to the requested byte passage.
    NoParse,
    /// The token index is outside the declared dictionary.
    WordOutsideDictionary { word: usize, words: usize },
    /// Two distinct parses decode to the same bytes.
    NotUniquelyDecodable { parses: Vec<Vec<usize>> },
}

/// A finite segmentation lattice: one vertex per byte boundary and an edge for each dictionary
/// word that begins there.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SegmentationLattice {
    bytes: Vec<u8>,
    edges: Vec<Vec<(usize, usize)>>,
}

impl SegmentationLattice {
    /// Byte passage represented by this lattice.
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Outgoing `(word index, next byte boundary)` edges at each current byte boundary.
    pub fn edges(&self, boundary: usize) -> Option<&[(usize, usize)]> {
        self.edges.get(boundary).map(Vec::as_slice)
    }
}

/// Exact result of checking the append transport square for one byte continuation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EncodingSquare {
    /// `ρ(x)`, the original bytes.
    pub source: Vec<u8>,
    /// `E(x)`, its unique parse.
    pub encoding: Vec<usize>,
    /// `T(x)`, source followed by the declared word.
    pub successor: Vec<u8>,
    /// `E_next(T(x))`, the unique parse after continuation.
    pub next_encoding: Vec<usize>,
    /// `U(E(x))`, parse followed by the declared word index.
    pub transported_encoding: Vec<usize>,
}

/// A concrete separator for the append square: the two proposed successor encodings differ.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EncodingSeparator {
    /// Why the proposed square has no unique encoding.
    pub cause: SeparatorCause,
    /// The source bytes.
    pub source: Vec<u8>,
    /// `E(x)`.
    pub encoding: Vec<usize>,
    /// `T(x)`.
    pub successor: Vec<u8>,
    /// The actual next parse `E_next(T(x))`.
    pub next_encoding: Vec<usize>,
    /// The transported old parse `U(E(x))`.
    pub transported_encoding: Vec<usize>,
    /// Two exact competing parses when ambiguity is the separating defect.
    pub competing_encodings: Option<(Vec<usize>, Vec<usize>)>,
}

/// The exact obstruction returned by [`WordDictionary::append_square`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SeparatorCause {
    /// The source has no parse in the dictionary image.
    SourceHasNoParse,
    /// The source has multiple parses, so `E` is not a function there.
    SourceHasMultipleParses,
    /// The declared continuation word index is outside the dictionary.
    WordOutsideDictionary,
    /// The continued source has no parse in the dictionary image.
    SuccessorHasNoParse,
    /// The continued source has multiple parses.
    SuccessorHasMultipleParses,
    /// The two exact successor encodings differ.
    TransportMismatch,
}

/// A finite byte-word dictionary with an exact token face and stopping face.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordDictionary {
    words: Vec<Vec<u8>>,
    token_face: Vec<Rat>,
    stop: Rat,
    continuation: Rat,
    uniquely_decodable: bool,
}

impl WordDictionary {
    /// Declare a finite vocabulary, including ambiguous dictionaries whose source mass sums all
    /// segmentation paths. Token masses must form an exact face;
    /// `0 < stop < 1` leaves positive mass for both termination and continuation.
    pub fn new(
        words: Vec<Vec<u8>>,
        token_face: Vec<Rat>,
        stop: Rat,
    ) -> Result<Self, PopulationError> {
        if words.is_empty()
            || words.len() != token_face.len()
            || words.iter().any(Vec::is_empty)
            || token_face
                .iter()
                .any(|mass| mass <= &Rat::from_integer(0.into()))
            || token_face.iter().sum::<Rat>() != Rat::from_integer(1.into())
            || stop <= Rat::from_integer(0.into())
            || stop >= Rat::from_integer(1.into())
        {
            return Err(refuse(
                "a word dictionary",
                "it has nonempty words, a positive exact token face, and a stop face strictly between zero and one",
            ));
        }
        let uniquely_decodable = uniquely_decodable(&words);
        let continuation = Rat::from_integer(1.into()) - &stop;
        Ok(Self {
            words,
            token_face,
            stop,
            continuation,
            uniquely_decodable,
        })
    }

    /// Declared byte words in dictionary order.
    pub fn words(&self) -> &[Vec<u8>] {
        &self.words
    }

    /// Whether every finite dictionary concatenation has a unique tokenization.
    pub fn is_uniquely_decodable(&self) -> bool {
        self.uniquely_decodable
    }

    /// Decode a token word by concatenating its declared byte words.
    pub fn decode(&self, parse: &[usize]) -> Result<Vec<u8>, ParseError> {
        let mut bytes = Vec::new();
        for &word in parse {
            let Some(piece) = self.words.get(word) else {
                return Err(ParseError::WordOutsideDictionary {
                    word,
                    words: self.words.len(),
                });
            };
            bytes.extend_from_slice(piece);
        }
        Ok(bytes)
    }

    /// Build the offset lattice for a byte passage.
    pub fn lattice(&self, bytes: &[u8]) -> SegmentationLattice {
        let mut edges = vec![Vec::new(); bytes.len() + 1];
        for at in 0..bytes.len() {
            for (word, piece) in self.words.iter().enumerate() {
                if bytes[at..].starts_with(piece) {
                    edges[at].push((word, at + piece.len()));
                }
            }
        }
        SegmentationLattice {
            bytes: bytes.to_vec(),
            edges,
        }
    }

    /// Recover a unique token sequence, or return no-parse / exact competing-parse evidence.
    pub fn encode(&self, bytes: &[u8]) -> Result<Vec<usize>, ParseError> {
        let lattice = self.lattice(bytes);
        let mut paths: Vec<Vec<Vec<usize>>> = vec![Vec::new(); bytes.len() + 1];
        paths[0].push(Vec::new());
        for at in 0..bytes.len() {
            for path in paths[at].clone() {
                for &(word, next) in &lattice.edges[at] {
                    let mut candidate = path.clone();
                    candidate.push(word);
                    if paths[next].len() < 2 && !paths[next].contains(&candidate) {
                        paths[next].push(candidate);
                    }
                }
            }
        }
        match paths
            .pop()
            .expect("one path slot per byte boundary")
            .as_slice()
        {
            [] => Err(ParseError::NoParse),
            [parse] => Ok(parse.clone()),
            [first, second, ..] => Err(ParseError::NotUniquelyDecodable {
                parses: vec![first.clone(), second.clone()],
            }),
        }
    }

    /// Exact terminated source mass `P_G(x)=Σ_(D z=x) P(z)`, including the stop factor.
    pub fn parse_mass(&self, bytes: &[u8]) -> Rat {
        let lattice = self.lattice(bytes);
        let mut mass = vec![Rat::from_integer(0.into()); bytes.len() + 1];
        mass[0] = Rat::from_integer(1.into());
        for at in 0..bytes.len() {
            let incoming = mass[at].clone();
            if incoming.is_zero() {
                continue;
            }
            for &(word, next) in &lattice.edges[at] {
                mass[next] += &incoming * &self.continuation * &self.token_face[word];
            }
        }
        &mass[bytes.len()] * &self.stop
    }

    /// Check `D E = ρ` and the append continuation square `E_next T = U E`. A mismatch returns
    /// the exact pair of competing successor encodings as a separator.
    pub fn append_square(
        &self,
        bytes: &[u8],
        appended_word: usize,
    ) -> Result<EncodingSquare, EncodingSeparator> {
        let encoding = match self.encode(bytes) {
            Ok(encoding) => encoding,
            Err(ParseError::NotUniquelyDecodable { parses }) => {
                return Err(EncodingSeparator {
                    cause: SeparatorCause::SourceHasMultipleParses,
                    source: bytes.to_vec(),
                    encoding: parses[0].clone(),
                    successor: bytes.to_vec(),
                    next_encoding: Vec::new(),
                    transported_encoding: Vec::new(),
                    competing_encodings: Some((parses[0].clone(), parses[1].clone())),
                });
            }
            Err(_) => {
                return Err(EncodingSeparator {
                    cause: SeparatorCause::SourceHasNoParse,
                    source: bytes.to_vec(),
                    encoding: Vec::new(),
                    successor: bytes.to_vec(),
                    next_encoding: Vec::new(),
                    transported_encoding: Vec::new(),
                    competing_encodings: None,
                });
            }
        };
        let Some(word) = self.words.get(appended_word) else {
            return Err(EncodingSeparator {
                cause: SeparatorCause::WordOutsideDictionary,
                source: bytes.to_vec(),
                encoding,
                successor: bytes.to_vec(),
                next_encoding: Vec::new(),
                transported_encoding: Vec::new(),
                competing_encodings: None,
            });
        };
        let mut successor = bytes.to_vec();
        successor.extend_from_slice(word);
        let next_encoding = match self.encode(&successor) {
            Ok(next_encoding) => next_encoding,
            Err(ParseError::NotUniquelyDecodable { parses }) => {
                return Err(EncodingSeparator {
                    cause: SeparatorCause::SuccessorHasMultipleParses,
                    source: bytes.to_vec(),
                    encoding: encoding.clone(),
                    successor,
                    next_encoding: parses[0].clone(),
                    transported_encoding: encoding,
                    competing_encodings: Some((parses[0].clone(), parses[1].clone())),
                });
            }
            Err(_) => {
                return Err(EncodingSeparator {
                    cause: SeparatorCause::SuccessorHasNoParse,
                    source: bytes.to_vec(),
                    encoding: encoding.clone(),
                    successor,
                    next_encoding: Vec::new(),
                    transported_encoding: encoding,
                    competing_encodings: None,
                });
            }
        };
        let mut transported_encoding = encoding.clone();
        transported_encoding.push(appended_word);
        if next_encoding != transported_encoding {
            return Err(EncodingSeparator {
                cause: SeparatorCause::TransportMismatch,
                source: bytes.to_vec(),
                encoding,
                successor,
                next_encoding,
                transported_encoding,
                competing_encodings: None,
            });
        }
        let Ok(decoded) = self.decode(&encoding) else {
            unreachable!("encode returns dictionary word indices")
        };
        debug_assert_eq!(decoded, bytes);
        Ok(EncodingSquare {
            source: bytes.to_vec(),
            encoding,
            successor,
            next_encoding,
            transported_encoding,
        })
    }
}

/// The exact receiver readout of a word family, including its live segmentation states.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordReadout {
    /// Dictionary size.
    pub words: usize,
    /// Number of received byte or end classes.
    pub received: u64,
    /// Exact mass at a token boundary.
    pub boundary_mass: Rat,
    /// Number of nonzero partial-token states carried.
    pub partial_states: usize,
    /// Whether the explicit end class has been received.
    pub terminated: bool,
}

/// A population family whose receiver alphabet is 256 byte classes and one explicit end class.
pub struct WordFamily {
    label: String,
    dictionary: WordDictionary,
    description: u64,
    boundary: Rat,
    active: Vec<Vec<Rat>>,
    likelihood: Rat,
    received: u64,
    terminated: bool,
    extinct: bool,
}

impl WordFamily {
    /// Declare a word family. `description` is the charged dictionary and family declaration;
    /// the likelihood separately charges every token and the terminal class.
    pub fn new(label: String, description: u64, dictionary: WordDictionary) -> Self {
        let active = dictionary
            .words
            .iter()
            .map(|word| vec![Rat::from_integer(0.into()); word.len() + 1])
            .collect();
        Self {
            label,
            dictionary,
            description,
            boundary: Rat::from_integer(1.into()),
            active,
            likelihood: Rat::from_integer(1.into()),
            received: 0,
            terminated: false,
            extinct: false,
        }
    }

    /// The dictionary and its exact source mass.
    pub fn dictionary(&self) -> &WordDictionary {
        &self.dictionary
    }

    fn active_mass(&self) -> Rat {
        self.active
            .iter()
            .flat_map(|states| states.iter())
            .cloned()
            .sum()
    }
}

impl Family for WordFamily {
    fn label(&self) -> String {
        self.label.clone()
    }

    fn alphabet(&self) -> usize {
        WORD_END + 1
    }

    fn description(&self) -> u64 {
        self.description
    }

    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        if self.terminated {
            return Err(refuse(
                "a terminated word family",
                "no cell follows its explicit end class",
            ));
        }
        let denominator = &self.boundary + self.active_mass();
        if self.extinct || denominator.is_zero() {
            return Ok(vec![Rat::from_integer(0.into()); self.alphabet()]);
        }
        let mut numerator = vec![Rat::from_integer(0.into()); self.alphabet()];
        for (word, probability) in self
            .dictionary
            .words
            .iter()
            .zip(&self.dictionary.token_face)
        {
            numerator[usize::from(word[0])] +=
                &self.boundary * &self.dictionary.continuation * probability;
        }
        numerator[WORD_END] += &self.boundary * &self.dictionary.stop;
        for (word_index, word) in self.dictionary.words.iter().enumerate() {
            for offset in 1..word.len() {
                let mass = &self.active[word_index][offset];
                if !mass.is_zero() {
                    numerator[usize::from(word[offset])] += mass;
                }
            }
        }
        Ok(numerator
            .into_iter()
            .map(|mass| mass / &denominator)
            .collect())
    }

    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        if cell >= self.alphabet() {
            return Err(PopulationError::CellOutside {
                cell,
                alphabet: self.alphabet(),
            });
        }
        let face = self.face()?;
        let arrived = face[cell].clone();
        self.likelihood *= &arrived;
        self.received += 1;
        if arrived.is_zero() {
            self.boundary = Rat::from_integer(0.into());
            self.active.iter_mut().for_each(|states| {
                states.fill(Rat::from_integer(0.into()));
            });
            self.extinct = true;
            return Ok(arrived);
        }
        if cell == WORD_END {
            self.terminated = true;
            self.boundary = Rat::from_integer(0.into());
            self.active.iter_mut().for_each(|states| {
                states.fill(Rat::from_integer(0.into()));
            });
            return Ok(arrived);
        }

        let byte = cell as u8;
        let old_boundary = self.boundary.clone();
        let mut next_boundary = Rat::from_integer(0.into());
        let mut next_active: Vec<Vec<Rat>> = self
            .dictionary
            .words
            .iter()
            .map(|word| vec![Rat::from_integer(0.into()); word.len() + 1])
            .collect();

        for (word_index, word) in self.dictionary.words.iter().enumerate() {
            if word[0] == byte {
                let mass = &old_boundary
                    * &self.dictionary.continuation
                    * &self.dictionary.token_face[word_index];
                if word.len() == 1 {
                    next_boundary += mass;
                } else {
                    next_active[word_index][1] += mass;
                }
            }
            for offset in 1..word.len() {
                if word[offset] != byte {
                    continue;
                }
                let mass = self.active[word_index][offset].clone();
                if offset + 1 == word.len() {
                    next_boundary += mass;
                } else {
                    next_active[word_index][offset + 1] += mass;
                }
            }
        }
        self.boundary = next_boundary;
        self.active = next_active;
        Ok(arrived)
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Exact(self.likelihood.clone())
    }

    fn readout(&self) -> Readout<'_> {
        Readout::Words(WordReadout {
            words: self.dictionary.words.len(),
            received: self.received,
            boundary_mass: self.boundary.clone(),
            partial_states: self
                .active
                .iter()
                .flat_map(|states| states.iter())
                .filter(|mass| !mass.is_zero())
                .count(),
            terminated: self.terminated,
        })
    }

    fn admits(&self, cells: &[usize]) -> Result<(), PopulationError> {
        let alphabet = self.alphabet();
        if let Some(&cell) = cells.iter().find(|&&cell| cell >= alphabet) {
            return Err(PopulationError::CellOutside { cell, alphabet });
        }
        if self.terminated && !cells.is_empty() {
            return Err(refuse(
                "a word family passage",
                "no source cells follow the terminal class",
            ));
        }
        if let Some(end) = cells.iter().position(|&cell| cell == WORD_END)
            && end + 1 < cells.len()
        {
            return Err(refuse(
                "a word family passage",
                "its terminal class is the final source cell",
            ));
        }
        Ok(())
    }

    fn declaration(&self) -> Declaration {
        Declaration::new(
            "word segmentation",
            vec![self.dictionary.words.len() as u64, WORD_END as u64 + 1],
        )
    }

    fn work(&self) -> Work {
        Work::default()
    }
}

fn uniquely_decodable(words: &[Vec<u8>]) -> bool {
    let mut residuals = BTreeSet::<Vec<u8>>::new();
    for (i, left) in words.iter().enumerate() {
        for (j, right) in words.iter().enumerate() {
            if i == j {
                continue;
            }
            if left.starts_with(right) {
                residuals.insert(left[right.len()..].to_vec());
            } else if right.starts_with(left) {
                residuals.insert(right[left.len()..].to_vec());
            }
        }
    }
    if residuals.contains(&Vec::new()) {
        return false;
    }
    let mut seen = BTreeSet::<Vec<Vec<u8>>>::new();
    while !residuals.is_empty() {
        let layer: Vec<_> = residuals.iter().cloned().collect();
        if !seen.insert(layer.clone()) {
            return true;
        }
        let mut next = BTreeSet::<Vec<u8>>::new();
        for residual in layer {
            for word in words {
                if residual == *word {
                    return false;
                }
                if residual.starts_with(word) {
                    next.insert(residual[word.len()..].to_vec());
                } else if word.starts_with(&residual) {
                    next.insert(word[residual.len()..].to_vec());
                }
            }
        }
        if next.contains(&Vec::new()) {
            return false;
        }
        residuals = next;
    }
    true
}

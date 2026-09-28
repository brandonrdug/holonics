//! Word segmentation conditioned by the existing section-letter receiver.
//!
//! A sectioned word family has the same byte/section alphabet as its `BoundaryEgg`. Within an
//! open part, the `WordFamily` face supplies all byte masses and its `WORD_END` mass is distributed
//! over section classes in the boundary egg's exact conditional proportions. At the opening
//! section there is no preceding word to terminate, so the boundary egg's opening letter face is
//! used directly. A section consumes the current word's end class and resets that word receiver.

use crate::ratio::Rat;
use crate::receiver::population::{
    BoundaryEgg, Declaration, Family, Likelihood, PopulationError, Readout, WORD_END,
    WordDictionary, WordFamily, Work, refuse,
};
use num_traits::Zero;

/// The word navigator joined to a part-clock section receiver over one shared cell alphabet.
pub struct SectionedWordFamily {
    label: String,
    description: u64,
    dictionary: WordDictionary,
    pub(super) word: WordFamily,
    pub(super) boundary: BoundaryEgg,
    likelihood: Rat,
    open: bool,
}

impl SectionedWordFamily {
    /// Join the word receiver to a fresh section receiver. The vocabulary must contain every
    /// singleton byte so every exterior byte remains admitted even when longer words are also
    /// present; ambiguous longer parses are handled by `WordFamily`'s exact path sum.
    pub fn new(
        label: String,
        description: u64,
        dictionary: WordDictionary,
        boundary: BoundaryEgg,
    ) -> Result<Self, PopulationError> {
        let chart = *boundary.clock().chart();
        if chart.bytes() != 256 || chart.alphabet() != chart.bytes() + chart.letters() {
            return Err(refuse(
                "a sectioned word family",
                "its section chart has 256 byte cells followed by its section letters",
            ));
        }
        if boundary.clock().port().section.is_some() {
            return Err(refuse(
                "a sectioned word family",
                "its boundary egg is at the opening section",
            ));
        }
        if (0..chart.bytes())
            .any(|byte| !dictionary.words().iter().any(|word| word == &[byte as u8]))
        {
            return Err(refuse(
                "a sectioned word dictionary",
                "it contains a singleton fallback for every exterior byte",
            ));
        }
        let word = WordFamily::new(
            "within-part words".to_string(),
            description,
            dictionary.clone(),
        );
        Ok(Self {
            label,
            description,
            dictionary,
            word,
            boundary,
            likelihood: Rat::from_integer(1.into()),
            open: false,
        })
    }

    /// The shared exterior chart.
    pub fn chart(&self) -> &crate::compression::landmark::context::SectionChart {
        self.boundary.clock().chart()
    }

    /// The section reader's exact conditional face over section classes.
    fn conditional_letters(&self) -> Result<Vec<Rat>, PopulationError> {
        let boundary_face = self.boundary.face()?;
        let chart = self.chart();
        let letters = boundary_face[chart.bytes()..].to_vec();
        let total: Rat = letters.iter().cloned().sum();
        if total.is_zero() {
            return Err(refuse(
                "a sectioned word face",
                "the boundary egg's section-letter mass is positive",
            ));
        }
        Ok(letters.into_iter().map(|mass| mass / &total).collect())
    }

    /// `P(c | current state)` on the shared byte/section chart, exact and normalized.
    fn composed_face(&self) -> Result<Vec<Rat>, PopulationError> {
        let chart = self.chart();
        let mut face = vec![Rat::zero(); chart.alphabet()];
        if !self.open {
            // Before the first section the boundary egg pins the opening letter; there is no word
            // passage whose stop can be charged yet.
            face[chart.bytes()..].clone_from_slice(&self.conditional_letters()?);
        } else {
            let word_face = self.word.face()?;
            let end = word_face[WORD_END].clone();
            face[..chart.bytes()].clone_from_slice(&word_face[..chart.bytes()]);
            for (offset, conditional) in self.conditional_letters()?.into_iter().enumerate() {
                face[chart.bytes() + offset] = &end * conditional;
            }
        }
        if face.iter().cloned().sum::<Rat>() != Rat::from_integer(1.into()) {
            return Err(refuse(
                "a sectioned word face",
                "byte masses and routed word-end mass sum exactly to one",
            ));
        }
        Ok(face)
    }

    fn reset_word(&mut self) {
        self.word = WordFamily::new(
            "within-part words".to_string(),
            self.description,
            self.dictionary.clone(),
        );
    }
}

impl Family for SectionedWordFamily {
    fn label(&self) -> String {
        self.label.clone()
    }

    fn alphabet(&self) -> usize {
        self.chart().alphabet()
    }

    fn description(&self) -> u64 {
        self.description
    }

    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        self.composed_face()
    }

    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let alphabet = self.alphabet();
        if cell >= alphabet {
            return Err(crate::receiver::population::PopulationError::CellOutside {
                cell,
                alphabet,
            });
        }
        let face = self.composed_face()?;
        let arrived = face[cell].clone();
        if arrived.is_zero() {
            return Ok(arrived);
        }

        let chart = *self.chart();
        if chart.section(cell).is_some() {
            if self.open {
                let word_face = self.word.face()?;
                let stopped = self.word.receive(WORD_END)?;
                if stopped != word_face[WORD_END] {
                    return Err(refuse(
                        "a sectioned word end",
                        "the consumed terminal mass equals the word receiver's own face",
                    ));
                }
            }
            self.boundary.receive(cell)?;
            self.open = true;
            self.reset_word();
        } else {
            if !self.open {
                return Err(refuse(
                    "a sectioned word byte",
                    "a section opens before any byte is received",
                ));
            }
            let word_probability = self.word.receive(cell)?;
            if word_probability != arrived {
                return Err(refuse(
                    "a sectioned word byte",
                    "the composed byte face equals the word receiver's own face",
                ));
            }
            self.boundary.receive(cell)?;
        }
        self.likelihood *= &arrived;
        Ok(arrived)
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Exact(self.likelihood.clone())
    }

    fn readout(&self) -> Readout<'_> {
        self.word.readout()
    }

    fn admits(&self, cells: &[usize]) -> Result<(), PopulationError> {
        if let Some(&cell) = cells.iter().find(|&&cell| cell >= self.alphabet()) {
            return Err(crate::receiver::population::PopulationError::CellOutside {
                cell,
                alphabet: self.alphabet(),
            });
        }
        self.boundary.admits(cells)
    }

    fn declaration(&self) -> Declaration {
        Declaration::new(
            "sectioned word family",
            vec![
                self.chart().bytes() as u64,
                self.chart().channels() as u64,
                self.chart().kinds() as u64,
                self.dictionary.words().len() as u64,
            ],
        )
        .with(vec![self.word.declaration(), self.boundary.declaration()])
    }

    fn work(&self) -> Work {
        let mut work = self.word.work();
        for (act, count) in &self.boundary.work().acts {
            work.add(*act, *count);
        }
        // The current component owners expose no counts for dictionary-edge evaluations. This
        // receipt carries only work reported by those owners; it cannot certify the F1 budget.
        work
    }
}

//! **Aeon switching: two sources alternating by drawn aeons; a grating silent for an aeon returns.**
//!
//! [definition; agent-inferred] **The Holarchy.** Two sources run together over one passage, both
//! moving at every tick; the emission reads the first in the even aeons and the second in the odd
//! ones. The aeons' lengths are drawn from a declared family ([`AeonFamily`], uniform on
//! `[shortest, longest]`). In the **dormant** case ([`Switching::dormant`]) both sources are one
//! moiré: every grating in the even aeons, and in the odd ones every grating but the dormant one,
//! whose layer is transparent (its sheet reads 0) while its ring keeps turning, so when it returns
//! it returns at its continued phase, never restarted: a dormant mode waiting for a fitting
//! antecedent.
//!
//! [proved-derived; implemented-exact] **The truth** ([`SwitchTruth`]): the aeons' lengths, the
//! switch cells (each aeon's first cell after the first), and the **switch epochs** as the aeon
//! owner's epochs (`aeon::epochs`, Lean `Aeon/Clock/Epoch.epochOf`): the cell clock is a one-circle
//! lift (`aeon::ClockLift`, one micro-step a cell), the passage is its forward aeon of `n` steps,
//! and the section is the passages arriving on a switch cell. So a cell's aeon is the epoch of the
//! micro-state it leaves, `epochOf(t) = #{switch cells ≤ t}`, the sources alternate on its parity,
//! and the flux is the number of switches. The owner fits: nothing of the switching is read outside
//! it. The dormant grating is named with the aeons it is silent in (the odd ones). The switch clock
//! alone ([`SwitchTruth::clock`], [`SwitchTruth::drawn`]) is also the chase's faulty sensor's: its
//! turned frame is the second source, read in the odd aeons (`holarchy::terrain::sensing`).

use std::collections::BTreeSet;

use num_bigint::{BigInt, BigUint};

use super::{Draw, Moire, TerrainError, refuse};
use crate::aeon::{ClockLift, Epochs, LiftPassage, epochs};

/// [definition] **The declared aeon family**: each aeon's length uniform on `[shortest, longest]`,
/// `1 ≤ shortest ≤ longest`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AeonFamily {
    pub shortest: u64,
    pub longest: u64,
}

/// [definition] **The switching's exact truth receipt** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SwitchTruth {
    pub lengths: Vec<u64>,
    pub switches: Vec<usize>,
    pub epochs: Epochs,
    pub dormant: Option<usize>,
}

impl SwitchTruth {
    /// **The switch clock of a passage of `n ≥ 1` cells under declared aeon lengths** (module
    /// header): the lengths the passage uses, the switch cells and the switch epochs of the cell
    /// clock's forward aeon; refused at a passage of no cells, an aeon of no cells, or lengths that
    /// do not cover the passage. Every switching reads its sources through it, and so does the
    /// chase's faulty sensor (`holarchy::terrain::sensing`).
    pub fn clock(n: usize, lengths: &[u64]) -> Result<Self, TerrainError> {
        if n == 0 || lengths.contains(&0) {
            return Err(refuse(
                "an aeon switching",
                "it needs cells and aeons of at least one cell",
            ));
        }
        let mut switches = Vec::new();
        let mut at = 0u64;
        for length in &lengths[..lengths.len().saturating_sub(1)] {
            at += length;
            if at >= n as u64 {
                break;
            }
            switches.push(at as usize);
        }
        if lengths.iter().sum::<u64>() < n as u64 {
            return Err(refuse(
                "an aeon switching",
                "the aeons' lengths do not cover the passage",
            ));
        }
        let lift = ClockLift::new(vec![BigUint::from(n)])?;
        let aeon = lift.forward(vec![BigInt::from(0)], &[BigInt::from(n)])?;
        let section: BTreeSet<BigInt> = switches.iter().map(|&s| BigInt::from(s)).collect();
        let epochs = epochs(&aeon, |passage: &LiftPassage| {
            section.contains(&(&passage.from[0] + 1))
        });
        let used = switches.len() + 1;
        Ok(Self {
            lengths: lengths[..used].to_vec(),
            switches,
            epochs,
            dormant: None,
        })
    }

    /// **The switch clock under drawn aeon lengths** (module header): lengths drawn from the
    /// declared family until they cover the passage of `n` cells.
    pub fn drawn(n: usize, family: &AeonFamily, draw: &mut Draw) -> Result<Self, TerrainError> {
        if family.shortest == 0 || family.shortest > family.longest {
            return Err(refuse(
                "an aeon family",
                "its lengths need 1 ≤ shortest ≤ longest",
            ));
        }
        let span = usize::try_from(family.longest - family.shortest + 1)
            .map_err(|_| refuse("an aeon family", "its span exceeds the address space"))?;
        let mut lengths = Vec::new();
        let mut covered = 0u64;
        while covered < n as u64 {
            let length = family.shortest + draw.below(span) as u64;
            covered += length;
            lengths.push(length);
        }
        Self::clock(n, &lengths)
    }

    /// **The source a cell reads**: its aeon's parity, the epoch of the micro-state it leaves.
    pub fn source(&self, cell: usize) -> Option<usize> {
        self.epochs.epoch_of(cell).map(|epoch| epoch % 2)
    }
}

/// [definition] **An aeon-switching terrain with its truth** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Switching {
    pub cells: Vec<usize>,
    pub truth: SwitchTruth,
}

impl Switching {
    /// **The switching of two sources by declared aeon lengths** (module header): the passage runs
    /// over the shorter source; the lengths must cover it, and each is positive.
    pub fn new(sources: [&[usize]; 2], lengths: Vec<u64>) -> Result<Self, TerrainError> {
        let n = sources[0].len().min(sources[1].len());
        let truth = SwitchTruth::clock(n, &lengths)?;
        let cells = (0..n)
            .map(|t| {
                let source = truth
                    .source(t)
                    .expect("a cell's micro-state lies in the aeon");
                sources[source][t]
            })
            .collect();
        Ok(Self { cells, truth })
    }

    /// **The switching under drawn aeon lengths** (module header): lengths drawn until they cover
    /// the passage.
    pub fn draw(
        sources: [&[usize]; 2],
        family: &AeonFamily,
        draw: &mut Draw,
    ) -> Result<Self, TerrainError> {
        let n = sources[0].len().min(sources[1].len());
        let truth = SwitchTruth::drawn(n, family, draw)?;
        Self::new(sources, truth.lengths)
    }

    /// **The dormant grating** (module header): one moiré, every grating in the even aeons and every
    /// grating but `dormant` in the odd ones, over `cells` cells and drawn aeons.
    pub fn dormant(
        moire: &Moire,
        dormant: usize,
        cells: usize,
        family: &AeonFamily,
        draw: &mut Draw,
    ) -> Result<Self, TerrainError> {
        let rings = moire.gratings().len();
        if dormant >= rings {
            return Err(refuse(
                "a dormant grating",
                "it names a grating of the moiré",
            ));
        }
        let every = moire.emit(cells);
        let mut active = vec![true; rings];
        active[dormant] = false;
        let silent = moire.emit_active(cells, &active);
        let mut switching = Self::draw([&every, &silent], family, draw)?;
        switching.truth.dormant = Some(dormant);
        Ok(switching)
    }
}

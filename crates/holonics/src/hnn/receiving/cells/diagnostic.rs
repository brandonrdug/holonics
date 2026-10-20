//! Immutable receiving-face controls. Every arm reads the same retained population and tree;
//! none receives a target, changes a constitution or supplies a generation law.

use super::*;
use num_traits::Zero;
use crate::hnn::receiving::ReceivingRead;
use crate::ratio::linear::ExactRatMatrix;
use crate::receiver::release::ClassCommit;

/// Three distinct executed operands at one pre-reception cut. The combined face includes the
/// wave and the tree's grain logits; the executed tree is its original rational face.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScoredFaceDiagnostic {
    pub reading_bits: u32,
    pub native_masses: Vec<ExactInterval>,
    pub combined_masses: Vec<ExactInterval>,
    pub tree_masses: Vec<ExactInterval>,
    pub native_minus_tree: Vec<ExactInterval>,
    pub combined_minus_tree: Vec<ExactInterval>,
    pub native_commit: ClassCommit,
    pub combined_commit: ClassCommit,
    pub tree_commit: ClassCommit,
}

fn differences(a: &[ExactInterval], b: &[ExactInterval]) -> Vec<ExactInterval> {
    a.iter().zip(b).map(|(a, b)| ExactInterval {
        lower: &a.lower - &b.upper,
        upper: &a.upper - &b.lower,
    }).collect()
}

impl ScoredFaceReading {
    /// Re-read the actual frozen operands at one depth of the existing demand ladder. This is a
    /// same-prior control, not a second population adapted to different outcomes.
    pub fn diagnostic_at(&self, bits: u32) -> Result<ScoredFaceDiagnostic, HnnError> {
        if !demand_ladder().contains(&bits) {
            return Err(HnnError::Unadmitted {
                reason: "a face diagnostic reads one depth of the native demand ladder",
            });
        }
        let alphabet = self.tree_probabilities.len();
        if alphabet == 0 || self.combined.cells().len() != alphabet {
            return Err(HnnError::Shape {
                what: "a diagnostic's tree and combined classes",
                expected: alphabet,
                found: self.combined.cells().len(),
            });
        }
        if self.tree_probabilities.iter().any(|x| x < &Rat::zero())
            || self.tree_probabilities.iter().cloned().sum::<Rat>() != Rat::one()
        {
            return Err(HnnError::Unadmitted {
                reason: "a diagnostic's executed tree is a probability partition",
            });
        }
        let native_masses = self.masses_at(bits)?;
        let combined_masses = (0..alphabet)
            .map(|c| face_enclosure_at(&self.combined, c, bits))
            .collect::<Result<Vec<_>, _>>()?;
        let tree_masses: Vec<_> = self.tree_probabilities.iter().cloned()
            .map(ExactInterval::point).collect();
        Ok(ScoredFaceDiagnostic {
            reading_bits: bits,
            native_minus_tree: differences(&native_masses, &tree_masses),
            combined_minus_tree: differences(&combined_masses, &tree_masses),
            native_commit: commit(&native_masses).map_err(draw_refusal)?,
            combined_commit: commit(&combined_masses).map_err(draw_refusal)?,
            tree_commit: commit(&tree_masses).map_err(draw_refusal)?,
            native_masses,
            combined_masses,
            tree_masses,
        })
    }
}

/// An operative receiving-map control on one already executed feature. The caller owns the
/// producing cut; exact equality below prevents a different native feature/read from silently
/// becoming its control. No alternate constitution or encoded source is manufactured.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReadoutMapDiagnostic {
    pub feature: Vec<Rat>,
    pub native_wave_logits: Vec<Rat>,
    pub control_wave_logits: Vec<Rat>,
    pub native: ScoredFaceDiagnostic,
    pub control: ScoredFaceDiagnostic,
    pub native_minus_control_masses: Vec<ExactInterval>,
}

pub fn compare_readout_maps_at(
    reading: &ScoredFaceReading,
    tree: &LandmarkFace,
    feature: &[Rat],
    native_map: &ExactRatMatrix,
    native_wave_logits: &[Rat],
    control_map: &ExactRatMatrix,
    bits: u32,
) -> Result<ReadoutMapDiagnostic, HnnError> {
    let rows = 2 * reading.tree_probabilities.len();
    if native_map.rows() != rows || control_map.rows() != rows
        || native_map.columns() != feature.len() || control_map.columns() != feature.len()
        || native_wave_logits.len() != rows
        || tree.probabilities != reading.tree_probabilities
        || tree.grain != reading.combined.grain()
    {
        return Err(HnnError::Unadmitted {
            reason: "a readout control preserves the complete producing classes, feature and tree",
        });
    }
    let native_logits = native_map.apply(feature)?;
    let native_read = ReceivingRead::combined(native_logits.clone(), tree, tree.grain)?;
    if native_logits != native_wave_logits
        || Face::of_read(&native_read, tree.grain)? != reading.combined
    {
        return Err(HnnError::Unadmitted {
            reason: "a readout control reconstructs the exact executed native logits and face",
        });
    }
    let control_wave_logits = control_map.apply(feature)?;
    let control_read = ReceivingRead::combined(control_wave_logits.clone(), tree, tree.grain)?;
    let control_reading = ScoredFaceReading {
        population: reading.population.clone(),
        tree_probabilities: reading.tree_probabilities.clone(),
        combined: Face::of_read(&control_read, tree.grain)?,
    };
    let native = reading.diagnostic_at(bits)?;
    let control = control_reading.diagnostic_at(bits)?;
    Ok(ReadoutMapDiagnostic {
        feature: feature.to_vec(),
        native_wave_logits: native_logits,
        control_wave_logits,
        native_minus_control_masses: differences(&native.native_masses, &control.native_masses),
        native,
        control,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::receiving::receiving_population;
    use crate::ratio::{integer, rat};

    fn material() -> (ScoredFaceReading, LandmarkFace, ExactRatMatrix) {
        let tree = LandmarkFace {
            grain: 4,
            probabilities: vec![rat(1, 2), rat(1, 2)],
            exponents: vec![(-4).into(), (-4).into()],
        };
        let map = ExactRatMatrix::new(vec![vec![integer(1)], vec![integer(0)],
            vec![integer(0)], vec![integer(0)]]).unwrap();
        let read = ReceivingRead::combined(map.apply(&[integer(1)]).unwrap(), &tree, 4).unwrap();
        (ScoredFaceReading::new(&receiving_population(), &tree, &Face::of_read(&read, 4).unwrap()), tree, map)
    }

    #[test]
    fn frozen_face_control_keeps_population_and_exposes_wave_commit() {
        let (reading, _, _) = material();
        let before = reading.clone();
        let diagnostic = reading.diagnostic_at(READING_BITS).unwrap();
        assert_eq!(diagnostic.native_commit.class(), Some(0));
        assert_eq!(diagnostic.combined_commit.class(), Some(0));
        assert_eq!(diagnostic.tree_commit.class(), None);
        assert!(diagnostic.native_minus_tree[0].lower > Rat::zero());
        assert_eq!(reading, before);
    }

    #[test]
    fn frozen_readout_control_changes_only_the_receiving_map() {
        let (reading, tree, map) = material();
        let before = reading.clone();
        let feature = vec![integer(1)];
        let wave = map.apply(&feature).unwrap();
        let zero = ExactRatMatrix::new(vec![vec![integer(0)]; 4]).unwrap();
        let diagnostic = compare_readout_maps_at(&reading, &tree, &feature, &map, &wave,
            &zero, READING_BITS).unwrap();
        assert_eq!(diagnostic.native.native_commit.class(), Some(0));
        assert_eq!(diagnostic.control.native_commit.class(), None);
        assert_eq!(diagnostic.native.tree_masses, diagnostic.control.tree_masses);
        assert_eq!(reading, before);
        let same = compare_readout_maps_at(&reading, &tree, &feature, &map, &wave,
            &map, READING_BITS).unwrap();
        assert_eq!(same.native, same.control);
        let mut wrong = wave; wrong[0] += integer(1);
        assert!(compare_readout_maps_at(&reading, &tree, &feature, &map, &wrong,
            &zero, READING_BITS).is_err());
    }
}

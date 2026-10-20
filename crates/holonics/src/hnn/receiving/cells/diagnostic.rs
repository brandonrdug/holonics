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

/// A factual target's code on identical feature/tree/population operands under two R maps.
/// All code fields are exact intervals in bits. `native_minus_control` uses the existing
/// correlated population comparison: common tree and population normalization remain shared.
/// The other two differences compare against the executed tree's own code. No population,
/// tree, map, class chart or receiving history is changed to form these observations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReadoutClassCodeDiagnostic {
    pub target: usize,
    pub reading_bits: u32,
    pub native_code: ExactInterval,
    pub control_code: ExactInterval,
    pub tree_code: ExactInterval,
    pub native_minus_control: ExactInterval,
    pub native_minus_tree: ExactInterval,
    pub control_minus_tree: ExactInterval,
    pub native_mass: ExactInterval,
    pub control_mass: ExactInterval,
    pub tree_mass: Rat,
}

/// Read a genuine observed target only after the blind producing feature and face are fixed.
/// `code_of_at` and `code_change_at` are the existing native scorer owners; this adds no
/// logarithm, normalization, mixture or learning law. The maps share this one factual prefix's
/// tree and population. These are R-only interventions, not independently adapted populations.
#[allow(clippy::too_many_arguments)]
pub fn compare_readout_class_codes_at(
    reading: &ScoredFaceReading,
    tree: &LandmarkFace,
    feature: &[Rat],
    native_map: &ExactRatMatrix,
    native_wave_logits: &[Rat],
    control_map: &ExactRatMatrix,
    target: usize,
    bits: u32,
) -> Result<ReadoutClassCodeDiagnostic, HnnError> {
    use crate::receiver::population::port::ComparedFace;
    // Reuse the full consuming square: native R*feature equals its actual logits and grain
    // face; the counterfactual changes only R on that same feature, tree and population.
    let maps = compare_readout_maps_at(
        reading,
        tree,
        feature,
        native_map,
        native_wave_logits,
        control_map,
        bits,
    )?;
    let control_read = ReceivingRead::combined(maps.control_wave_logits, tree, tree.grain)?;
    let control_face = Face::of_read(&control_read, tree.grain)?;
    let tree_mass = reading
        .tree_probabilities
        .get(target)
        .ok_or(HnnError::CellOutside {
            code: target,
            alphabet: reading.tree_probabilities.len(),
        })?
        .clone();
    let tree_point = ExactInterval::point(tree_mass.clone());
    let native_combined = face_enclosure_at(&reading.combined, target, bits)?;
    let control_combined = face_enclosure_at(&control_face, target, bits)?;
    let native_faces = [tree_point.clone(), native_combined.clone()];
    let control_faces = [tree_point.clone(), control_combined.clone()];
    let native_code = reading
        .population
        .code_of_at(&native_faces, bits)
        .map_err(population_refusal)?;
    let control_code = reading
        .population
        .code_of_at(&control_faces, bits)
        .map_err(population_refusal)?;
    let log_tree = crate::ratio::algebraic::log2_enclosure_at(&tree_mass, bits)?;
    let tree_code = ExactInterval::new(-log_tree.upper, -log_tree.lower)?;
    let combined_change = if reading.combined == control_face {
        ComparedFace::Shared(native_combined)
    } else {
        ComparedFace::Changed {
            before: control_combined,
            after: native_combined,
        }
    };
    // code_change_at returns code(after)-code(before), hence native minus control here.
    let native_minus_control = reading
        .population
        .code_change_at(
            &[vec![ComparedFace::Shared(tree_point), combined_change]],
            bits,
        )
        .map_err(population_refusal)?;
    let difference = |a: &ExactInterval, b: &ExactInterval| {
        ExactInterval::new(&a.lower - &b.upper, &a.upper - &b.lower)
    };
    Ok(ReadoutClassCodeDiagnostic {
        target,
        reading_bits: bits,
        native_mass: reading
            .population
            .face_of_at(&native_faces, bits)
            .map_err(population_refusal)?,
        control_mass: reading
            .population
            .face_of_at(&control_faces, bits)
            .map_err(population_refusal)?,
        native_minus_tree: difference(&native_code, &tree_code)?,
        control_minus_tree: difference(&control_code, &tree_code)?,
        native_code,
        control_code,
        tree_code,
        native_minus_control,
        tree_mass,
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
    #[test]
    fn readout_class_codes_match_the_actual_native_scorer_and_keep_operands_frozen() {
        let (reading, tree, map) = material();
        let before = reading.clone();
        let feature = vec![integer(1)];
        let wave = map.apply(&feature).unwrap();
        let zero = ExactRatMatrix::new(vec![vec![integer(0)]; 4]).unwrap();
        let codes = compare_readout_class_codes_at(
            &reading,
            &tree,
            &feature,
            &map,
            &wave,
            &zero,
            0,
            READING_BITS,
        )
        .unwrap();
        let scored = crate::hnn::receiving::score_at(
            &reading.population,
            0,
            &crate::hnn::ratio::Faces {
                faces: vec![reading.combined.clone()],
                logits: vec![wave.clone()],
            },
            &[tree.clone()],
            &[0],
            READING_BITS,
        )
        .unwrap();
        assert_eq!(codes.native_code, scored.model[0]);
        assert_eq!(codes.tree_code, scored.tree[0]);
        assert!(codes.native_minus_control.upper < Rat::zero());
        assert!(codes.native_mass.lower > codes.control_mass.upper);
        assert_eq!(reading, before);
        let other = compare_readout_class_codes_at(
            &reading,
            &tree,
            &feature,
            &map,
            &wave,
            &zero,
            1,
            READING_BITS,
        )
        .unwrap();
        assert!(other.native_minus_control.lower > Rat::zero());
    }

    #[test]
    fn readout_class_codes_share_identical_readout_uncertainty_and_refuse_invalid_targets() {
        let (reading, tree, map) = material();
        let feature = vec![integer(1)];
        let wave = map.apply(&feature).unwrap();
        let codes = compare_readout_class_codes_at(
            &reading,
            &tree,
            &feature,
            &map,
            &wave,
            &map,
            0,
            READING_BITS,
        )
        .unwrap();
        assert_eq!(codes.native_code, codes.control_code);
        assert_eq!(codes.native_minus_control, ExactInterval::point(integer(0)));
        assert!(matches!(
            compare_readout_class_codes_at(
                &reading,
                &tree,
                &feature,
                &map,
                &wave,
                &map,
                2,
                READING_BITS
            ),
            Err(HnnError::CellOutside {
                code: 2,
                alphabet: 2
            })
        ));
    }
}

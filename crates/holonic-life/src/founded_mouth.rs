//! THE FOUNDED MOUTH — the segmentation a material's own octets decide, against the authored one.
//!
//! # Why this exists
//!
//! Every language ecology in this tree conditions on [`crate::causal_language::lexical_tokens`], and
//! that function is **authored end to end**: a word rule of `is_alphanumeric() || '_' || '\''`, a
//! six-glyph punctuation-run set `- = : / * #`, and a two-species Word/Punctuation partition. None of
//! it was read off any material. Brandon, 2026-08-16, on the segmentation it produces:
//!
//! > *"this segmenting is genuinely useless and we've had far better segmenting results in the past…
//! > either way the segmentation is broken so it is not tokenizing."*
//!
//! Meanwhile [`crate::exposure_codec`] recovers a codec from **octets alone** — the alphabet by
//! exhausting all 256 probes, the minimal refusals that establish there is a rule at all, the finest
//! quotient the declared family admits with the shortest separating context per pair, unit roles by a
//! downward fixed point **checked from two seeding frames and refused if they disagree**, and the
//! gauge freedoms the material never realised. Measured 2026-08-16 on this repository's records: it
//! recovers UTF-8 structure with **0 disagreements against an independent decoder on eight held-out
//! exposures**, and refuses octets the founding never showed rather than guessing.
//!
//! **The organ was built and was not on the language path.** This module is that join.
//!
//! # What this returns, and what it deliberately does not do
//!
//! It returns the founded segmentation **and the authored one beside it**, with the positions where
//! they differ. It does not silently replace anything: `CLAUDE.md` §8's rule is that an excision is
//! graded by its **orbit**, so the two readings are carried together and the difference is the
//! evidence. A caller that wants the founded reading takes it by name.
//!
//! # The refusals are returns
//!
//! A recovery can be obstructed, and an obstruction is a reading rather than an error:
//! `NothingIsRefused` is what uniform noise returns and is the negative control of the whole
//! operation; `NothingRecurs` means nothing happened twice; `FramesDisagree` means the reading
//! depended on which end it was seeded from, which is a coordinate rather than an invariant.
//! [`FoundedMouth::found`] carries every one of them out rather than collapsing them to `None`.

use crate::exposure_codec::{
    carried, octets_of, recover, ExposedMaterial, ExposureApertures, ExposureObstruction,
    ExposureRefusal, Unit, UnitRole,
};

/// Why a mouth could not be founded. Distinct from an obstruction, which is a return.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FoundedMouthRefusal {
    /// The exposure itself refused — no material, a radius below adjacency, a family past the
    /// declared aperture. Carried verbatim rather than restated.
    Exposure(ExposureRefusal),
    /// The recovery returned obstructions instead of a codec. Every one is carried, because
    /// *which* obstruction is the reading: uniform noise refuses nothing, and a material that
    /// recurs nowhere established nothing.
    Obstructed(Vec<ExposureObstruction>),
    /// The recovered codec refused to segment the read material, carrying its own reason.
    ///
    /// **This is a lawful return, and the commonest reason is the honest one**: the material read
    /// carries an octet the FOUNDING never showed, so the codec has no rule for it and declines
    /// rather than guessing. The first form of this enum folded this case into
    /// `PartLeftTheOctetCarrier` below, which made a routine and correct refusal look like a carrier
    /// defect and hid which of the two had happened.
    SegmentationRefused(String),
    /// The recovered codec segmented a part back into symbols that are not octets. Structural, and
    /// it has never been observed; it is refused rather than rendered lossily.
    PartLeftTheOctetCarrier,
}

/// One position where the two readings disagree, carried as the two parts rather than a count.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MouthDisagreement {
    /// The ordinal of the disagreement in the founded reading.
    pub at: usize,
    pub founded: String,
    pub authored: Option<String>,
}

/// The segmentation a material's own octets decided, with the authored reading retained beside it.
#[derive(Clone, Debug)]
pub struct FoundedMouth {
    /// The alphabet the material actually carries, recovered by exhausting every declared
    /// candidate. At the octet scale this mouth founds on, a unit is an octet.
    pub alphabet: Vec<Unit>,
    /// Every unit's role, present only because the two seeding frames agreed.
    pub roles: Vec<(Unit, UnitRole)>,
    /// The class adjacencies the material never realised. Flipping one changes no segmentation of
    /// this material, so they are freedoms and are reported rather than filled.
    pub gauge_freedom: Vec<(UnitRole, UnitRole)>,
    /// How many minimal refusals establish that there is a rule at all.
    pub refusals: usize,
    /// The founded parts.
    pub founded: Vec<String>,
    /// The authored parts, as the declared control.
    pub authored: Vec<String>,
}

impl FoundedMouth {
    /// Found a mouth from a population of octet streams, then read one of them through it.
    ///
    /// **Exposures are separate streams**, because two files are not one file and a codec recovered
    /// across the seam would have been recovered from an artifact of the concatenation order. The
    /// radius and family extent are caller-declared apertures; neither is authored here.
    pub fn found(
        exposures: Vec<Vec<u8>>,
        read: &[u8],
        apertures: ExposureApertures,
    ) -> Result<Self, FoundedMouthRefusal> {
        let material = ExposedMaterial::expose(exposures, apertures.radius)
            .map_err(FoundedMouthRefusal::Exposure)?;
        let recovery = recover(&material, apertures).map_err(FoundedMouthRefusal::Exposure)?;
        let Some(codec) = recovery.codec.as_ref() else {
            return Err(FoundedMouthRefusal::Obstructed(recovery.obstructions));
        };

        let symbols = carried(read);
        let parts = codec
            .segment(&symbols)
            .map_err(|refusal| FoundedMouthRefusal::SegmentationRefused(format!("{refusal:?}")))?;
        let mut founded = Vec::with_capacity(parts.len());
        for part in &parts {
            let octets = octets_of(part).ok_or(FoundedMouthRefusal::PartLeftTheOctetCarrier)?;
            founded.push(String::from_utf8_lossy(&octets).into_owned());
        }

        let authored = crate::causal_language::lexical_tokens(&String::from_utf8_lossy(read));

        Ok(Self {
            alphabet: recovery.alphabet,
            roles: recovery.roles.into_iter().collect(),
            gauge_freedom: recovery.gauge_freedom,
            refusals: recovery.refusals.len(),
            founded,
            authored,
        })
    }

    /// Where the two readings disagree, as parts rather than as a rate.
    ///
    /// A rate would be a magnitude face of a population whose members are the whole point: which
    /// parts the authored rule invented or missed is what a reader needs, and a percentage cannot
    /// carry it.
    pub fn disagreements(&self) -> Vec<MouthDisagreement> {
        let mut found = Vec::new();
        for (at, part) in self.founded.iter().enumerate() {
            let authored = self.authored.get(at);
            if authored != Some(part) {
                found.push(MouthDisagreement {
                    at,
                    founded: part.clone(),
                    authored: authored.cloned(),
                });
            }
        }
        found
    }

    /// The units carrying one recovered role, in canonical order.
    pub fn units_with(&self, role: UnitRole) -> Vec<Unit> {
        self.roles
            .iter()
            .filter(|(_, carried)| *carried == role)
            .map(|(unit, _)| *unit)
            .collect()
    }

    /// The same reading at octet scale, where a unit **is** an octet. `None` if any unit is wider,
    /// which this mouth's own founding cannot produce but a caller's alphabet could.
    pub fn octets_with(&self, role: UnitRole) -> Option<Vec<u8>> {
        self.units_with(role)
            .into_iter()
            .map(|unit| u8::try_from(unit).ok())
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn apertures() -> ExposureApertures {
        ExposureApertures::declared(2, 1 << 20)
    }

    /// The mouth founds on ordinary material and returns both readings.
    #[test]
    fn a_mouth_founds_from_octets_and_carries_the_authored_reading_beside_it() {
        let material: Vec<Vec<u8>> = vec![
            b"the arrival lands where it did not choose".to_vec(),
            b"a passage deposits and a later current rides it".to_vec(),
            b"the reflection series closes on a crystal".to_vec(),
        ];
        let read = b"a later current rides the deposit".to_vec();
        let mouth = FoundedMouth::found(material, &read, apertures()).expect("the mouth founds");
        assert!(!mouth.alphabet.is_empty(), "an alphabet was recovered");
        assert!(!mouth.founded.is_empty(), "the founded reading segmented");
        assert!(
            !mouth.authored.is_empty(),
            "the authored reading is retained"
        );
        assert!(
            mouth.refusals > 0,
            "with no minimal refusal there is no rule to have recovered"
        );
    }

    /// **The negative control of the whole operation.** Material whose own recurring factors license
    /// everything it does refuses nothing, so there is no rule to recover — and the organ must return
    /// that as an obstruction rather than manufacture a codec.
    #[test]
    fn material_that_refuses_nothing_is_obstructed_rather_than_segmented() {
        // Every word of the declared family realised, so nothing is refused. Over the alphabet
        // {a,b} at radius 2 the family is {a, b, aa, ab, ba, bb} and this material carries all six.
        //
        // The first fixture here was `abababab`, which was WRONG and the organ said so: it never
        // carries `aa` or `bb`, so it refuses two words, a rule exists, and a codec was correctly
        // recovered. The control was mis-declared, not the law.
        let material: Vec<Vec<u8>> = vec![b"aabbaab".to_vec(), b"bbaabba".to_vec()];
        match FoundedMouth::found(material, b"abab", apertures()) {
            Err(FoundedMouthRefusal::Obstructed(obstructions)) => {
                assert!(!obstructions.is_empty(), "an obstruction names itself");
            }
            other => panic!("material refusing nothing must be obstructed, got {other:?}"),
        }
    }

    /// An exposure refusal is carried verbatim rather than restated as a local error.
    #[test]
    fn a_radius_below_adjacency_is_refused_by_the_exposure_and_carried_out() {
        let material: Vec<Vec<u8>> = vec![b"anything".to_vec()];
        assert!(matches!(
            FoundedMouth::found(
                material,
                b"anything",
                ExposureApertures::declared(1, 1 << 12)
            ),
            Err(FoundedMouthRefusal::Exposure(
                ExposureRefusal::RadiusBelowAdjacency { radius: 1 }
            ))
        ));
    }

    /// Disagreements are returned as PARTS, not as a rate — the members are the reading.
    #[test]
    fn disagreements_carry_the_parts_and_never_a_rate() {
        let material: Vec<Vec<u8>> = vec![
            b"the arrival lands where it did not choose".to_vec(),
            b"a passage deposits and a later current rides it".to_vec(),
        ];
        let mouth = FoundedMouth::found(material, b"a later current", apertures())
            .expect("the mouth founds");
        for disagreement in mouth.disagreements() {
            assert!(
                !disagreement.founded.is_empty(),
                "a disagreement names the founded part"
            );
        }
    }
}

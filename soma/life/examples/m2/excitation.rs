//! M1 presentation occurrences crossing the authenticated W1 exterior codec.

use holonic_engine::foreign_codec_rest::ExteriorCodecArtifact;
use holonic_engine::native_rest::MountedNativeRest;
use life::mathematical_particle::{ExcitationPassage, TypedPassage};

use crate::particle::ExcitationGenerator;

pub fn passage(
    generator: &ExcitationGenerator,
    particle_occurrence: &str,
    typed: &TypedPassage,
    rest: &MountedNativeRest,
    codec: &ExteriorCodecArtifact,
) -> Result<ExcitationPassage, String> {
    let mut generator_octets = Vec::new();
    for (at, word) in generator.words.iter().enumerate() {
        if at > 0 {
            generator_octets.push(b' ');
        }
        generator_octets.extend_from_slice(word);
    }
    let text = std::str::from_utf8(&generator_octets)
        .map_err(|error| format!("{} is not UTF-8: {error}", generator.occurrence))?;
    let codewords = rest
        .codebook()
        .encode_text(codec, text, false)
        .map_err(|error| error.to_string())?
        .into_iter()
        .map(|word| usize::try_from(word).map_err(|_| "native codeword exceeds usize".to_owned()))
        .collect::<Result<Vec<_>, _>>()?;
    if codewords.is_empty() {
        return Err(format!(
            "{} returned no exterior codewords",
            generator.occurrence
        ));
    }
    let staging = typed
        .staging()
        .get(&generator.branch)
        .ok_or_else(|| format!("{} has no staging occurrence", generator.occurrence))?;
    let word = typed
        .branch(generator.branch)
        .ok_or_else(|| format!("{} has no operation word", generator.occurrence))?;
    let mut particle_word = vec![staging.event];
    particle_word.extend(word.steps.iter().map(|step| step.event));
    Ok(ExcitationPassage {
        occurrence: generator.occurrence.clone(),
        particle_occurrence: particle_occurrence.to_owned(),
        particle_word,
        source_occurrences: generator.source_occurrences.clone(),
        generator_octets,
        exterior_codec_occurrence: format!(
            "W1 exterior codec {} with authenticated detached companion bytes",
            rest.codebook().digest()
        ),
        codewords,
    })
}

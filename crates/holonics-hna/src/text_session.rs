//! Text is an exterior application over ordinary native recurrence. The decoder supplies a
//! declared end-marker receiver, never an authored answer, grammar emitter or learning update.
use crate::{
    publish_new, AthenaTokenApplication, HnaFileDependency, HnaModel, HnaOccurrence, HnaSession,
    HnaSessionError,
};
use holonic_engine::native_ecology::holonic_intelligence::face_of_last_row;
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeMap,
    io::{Read, Write},
    path::Path,
};

const STATE_SCHEMA: &str = "org.holonics.hna.text-continuation.v1";
const ARTIFACT_SCHEMA: &str = "org.holonics.hna.text-session.v1";
fn error(message: impl std::fmt::Display) -> HnaSessionError {
    HnaSessionError::Base(format!("text application: {message}"))
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "state", rename_all = "kebab-case")]
pub enum HnaTextDisposition {
    Ready,
    AwaitingMaterial { rows: BTreeMap<u32, Vec<u32>> },
    Completed { marker: u32 },
    Interrupted { reason: String },
    Obstructed { reason: String },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HnaTextContinuation {
    pub schema: String,
    pub prompt_addresses: Vec<u32>,
    pub emitted_addresses: Vec<u32>,
    pub generation: u64,
    /// An explicit attribution control, never the default productive inference lifecycle.
    pub observation_only: bool,
    pub disposition: HnaTextDisposition,
}

impl HnaTextContinuation {
    pub fn next_addresses(&self) -> Vec<u32> {
        self.prompt_addresses
            .iter()
            .chain(&self.emitted_addresses)
            .copied()
            .collect()
    }
    pub fn interrupt(&mut self, reason: impl Into<String>) {
        if matches!(
            self.disposition,
            HnaTextDisposition::Ready | HnaTextDisposition::AwaitingMaterial { .. }
        ) {
            self.disposition = HnaTextDisposition::Interrupted {
                reason: reason.into(),
            };
        }
    }
    /// This resumes an exterior resource/cancellation boundary, not a failed native operation.
    pub fn resume(&mut self) -> Result<(), HnaSessionError> {
        if !matches!(self.disposition, HnaTextDisposition::Interrupted { .. }) {
            return Err(error("not an interrupted application boundary"));
        }
        self.disposition = HnaTextDisposition::Ready;
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct CodecWitness {
    tokenizer: HnaFileDependency,
    generation: HnaFileDependency,
}

pub struct HnaTextApplication {
    codec: AthenaTokenApplication,
    witness: CodecWitness,
    completion: Vec<u32>,
}

#[derive(Debug, Serialize)]
pub struct HnaTextStep {
    pub selected: Option<u32>,
    pub text: String,
    pub generation: u64,
    pub disposition: HnaTextDisposition,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct TextArtifact {
    schema: String,
    model: HnaFileDependency,
    codec: CodecWitness,
    continuation: HnaTextContinuation,
}

impl HnaTextApplication {
    pub fn open(root: &Path) -> Result<Self, HnaSessionError> {
        Self::from_witness(CodecWitness {
            tokenizer: HnaFileDependency::capture(root.join("tokenizer.json"))?,
            generation: HnaFileDependency::capture(root.join("generation_config.json"))?,
        })
    }
    fn from_witness(witness: CodecWitness) -> Result<Self, HnaSessionError> {
        let mut bytes = Vec::new();
        witness
            .tokenizer
            .open_verified()?
            .read_to_end(&mut bytes)
            .map_err(error)?;
        let codec = AthenaTokenApplication::from_bytes(&bytes).map_err(error)?;
        let config: serde_json::Value =
            serde_json::from_reader(witness.generation.open_verified()?).map_err(error)?;
        let completion = parse_completion(&config, codec.vocabulary_extent())?;
        Ok(Self {
            codec,
            witness,
            completion,
        })
    }
    pub fn begin(
        &self,
        session: &HnaSession<'_, '_>,
        text: &str,
    ) -> Result<HnaTextContinuation, HnaSessionError> {
        self.check_width(session)?;
        Ok(HnaTextContinuation {
            schema: STATE_SCHEMA.into(),
            prompt_addresses: self.codec.encode_turn(text).map_err(error)?,
            emitted_addresses: Vec::new(),
            generation: session.anatomy().generation,
            observation_only: false,
            disposition: HnaTextDisposition::Ready,
        })
    }
    /// A later message continues the actual completed application transcript and the same native
    /// owner. Its content is an ordinary occurrence, not a reward or a privileged correction law.
    pub fn followup(
        &self,
        session: &HnaSession<'_, '_>,
        previous: &HnaTextContinuation,
        text: &str,
    ) -> Result<HnaTextContinuation, HnaSessionError> {
        self.validate(previous)?;
        if previous.generation != session.anatomy().generation
            || !matches!(previous.disposition, HnaTextDisposition::Completed { .. })
        {
            return Err(error(
                "followup requires the actual completed application boundary",
            ));
        }
        let mut next = self.begin(session, text)?;
        let mut prompt = previous.next_addresses();
        prompt.extend(self.codec.encode_plain("\n").map_err(error)?);
        // encode_turn's first address is its declared beginning-of-sequence marker. The existing
        // transcript already carries that occurrence; append only the subsequent turn framing.
        prompt.extend(next.prompt_addresses.into_iter().skip(1));
        next.prompt_addresses = prompt;
        next.observation_only = previous.observation_only;
        Ok(next)
    }
    fn check_width(&self, session: &HnaSession<'_, '_>) -> Result<(), HnaSessionError> {
        if session.terminal_width() != Some(self.codec.vocabulary_extent()) {
            return Err(error("codec does not cover the native terminal chart"));
        }
        Ok(())
    }
    fn validate(&self, state: &HnaTextContinuation) -> Result<(), HnaSessionError> {
        if state.schema != STATE_SCHEMA
            || state.prompt_addresses.is_empty()
            || state
                .prompt_addresses
                .iter()
                .chain(&state.emitted_addresses)
                .any(|id| *id as usize >= self.codec.vocabulary_extent())
        {
            return Err(error("malformed continuation"));
        }
        let first_stop = state
            .emitted_addresses
            .iter()
            .position(|id| self.completion.contains(id));
        match (&state.disposition, first_stop) {
            (HnaTextDisposition::Completed { marker }, Some(at))
                if at + 1 == state.emitted_addresses.len()
                    && state.emitted_addresses[at] == *marker => {}
            (HnaTextDisposition::Completed { .. }, _) | (_, Some(_)) => {
                return Err(error("completion disagrees with the emitted marker"))
            }
            _ => {}
        }
        Ok(())
    }
    pub fn text(&self, state: &HnaTextContinuation) -> Result<String, HnaSessionError> {
        self.validate(state)?;
        let end = state.emitted_addresses.len()
            - usize::from(matches!(
                state.disposition,
                HnaTextDisposition::Completed { .. }
            ));
        self.codec
            .decode_addresses(&state.emitted_addresses[..end])
            .map_err(error)
    }
    pub fn step(
        &self,
        session: &mut HnaSession<'_, '_>,
        state: &mut HnaTextContinuation,
    ) -> Result<HnaTextStep, HnaSessionError> {
        self.validate(state)?;
        self.check_width(session)?;
        if state.generation != session.anatomy().generation {
            return Err(error(
                "stale continuation; do not replay the native request",
            ));
        }
        if !matches!(
            state.disposition,
            HnaTextDisposition::Ready | HnaTextDisposition::AwaitingMaterial { .. }
        ) {
            return Err(error(
                "application is at a terminal or interrupted boundary",
            ));
        }
        let rows = session.missing_input_rows(&state.next_addresses());
        if !rows.is_empty() {
            state.disposition = HnaTextDisposition::AwaitingMaterial { rows };
            return Ok(HnaTextStep {
                selected: None,
                text: self.text(state)?,
                generation: state.generation,
                disposition: state.disposition.clone(),
            });
        }
        // Reserve before the native effect: retaining its selected result cannot require another
        // allocation after that effect has committed. Emitted addresses are the self occurrence.
        state.emitted_addresses.try_reserve(1).map_err(error)?;
        let occurrence = HnaOccurrence {
            row_addresses: state.prompt_addresses.clone(),
            history: state.emitted_addresses.clone(),
        };
        let native = if state.observation_only {
            session.observe_native(&occurrence)
        } else {
            session.advance_native(&occurrence)
        };
        let cycle = match native {
            Ok(cycle) => cycle,
            Err(failure) => {
                state.generation = session.anatomy().generation;
                state.disposition = HnaTextDisposition::Obstructed {
                    reason: failure.to_string(),
                };
                return Err(failure);
            }
        };
        state.generation = session.anatomy().generation;
        let emission = cycle.output.final_emission;
        let Some(face) = face_of_last_row(&emission.intervals, emission.rows, emission.width)
        else {
            state.disposition = HnaTextDisposition::Obstructed {
                reason: "native output has no terminal face".into(),
            };
            return Err(error(
                "native output has no terminal face; operation already advanced",
            ));
        };
        state.emitted_addresses.push(face.selected);
        state.disposition = if self.completion.contains(&face.selected) {
            HnaTextDisposition::Completed {
                marker: face.selected,
            }
        } else {
            HnaTextDisposition::Ready
        };
        // Decoder failure cannot cause another native effect on retry: the address and successor
        // are already retained in state, and rendering can be retried independently through text().
        let text = self.text(state)?;
        Ok(HnaTextStep {
            selected: Some(face.selected),
            text,
            generation: state.generation,
            disposition: state.disposition.clone(),
        })
    }
    /// Save native state first, then publish one immutable application manifest pointing at those
    /// exact bytes. If manifest publication fails, the model file remains recoverable and the
    /// caller still owns both live states. No rollback or peer-delivery claim is made.
    pub fn save(
        &self,
        session: &HnaSession<'_, '_>,
        state: &HnaTextContinuation,
        model_path: &Path,
        manifest_path: &Path,
    ) -> Result<(), HnaSessionError> {
        self.validate(state)?;
        if state.generation != session.anatomy().generation {
            return Err(error("stale application checkpoint"));
        }
        session.checkpoint(model_path)?;
        let artifact = TextArtifact {
            schema: ARTIFACT_SCHEMA.into(),
            model: HnaFileDependency::capture(model_path)?,
            codec: self.witness.clone(),
            continuation: state.clone(),
        };
        publish_new(manifest_path, |out| {
            serde_json::to_writer(&mut *out, &artifact).map_err(std::io::Error::other)?;
            out.write_all(b"\n")
        })
        .map_err(error)?;
        Ok(())
    }
    pub fn load(path: &Path) -> Result<(HnaModel, Self, HnaTextContinuation), HnaSessionError> {
        let artifact: TextArtifact =
            serde_json::from_reader(std::fs::File::open(path).map_err(error)?).map_err(error)?;
        if artifact.schema != ARTIFACT_SCHEMA {
            return Err(error("artifact schema"));
        }
        let application = Self::from_witness(artifact.codec)?;
        application.validate(&artifact.continuation)?;
        let model = HnaModel::from_checkpoint_reference(&artifact.model, None)?;
        if model.starting_generation() != artifact.continuation.generation {
            return Err(error("model/application boundary differs"));
        }
        Ok((model, application, artifact.continuation))
    }
}

fn parse_completion(
    config: &serde_json::Value,
    vocabulary: usize,
) -> Result<Vec<u32>, HnaSessionError> {
    let value = config
        .get("eos_token_id")
        .ok_or_else(|| error("codec declares no end-marker receiver"))?;
    let values = value
        .as_array()
        .map_or_else(|| vec![value], |array| array.iter().collect());
    let mut result = Vec::new();
    for value in values {
        let id = value
            .as_u64()
            .and_then(|id| u32::try_from(id).ok())
            .filter(|id| (*id as usize) < vocabulary)
            .ok_or_else(|| error("invalid codec end marker"))?;
        if !result.contains(&id) {
            result.push(id);
        }
    }
    if result.is_empty() {
        return Err(error("empty end-marker receiver"));
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn completion_is_declared_and_resource_interruption_is_not_completion() {
        assert_eq!(
            parse_completion(&serde_json::json!({"eos_token_id":[1,6,1]}), 8).unwrap(),
            vec![1, 6]
        );
        for invalid in [
            serde_json::json!({}),
            serde_json::json!({"eos_token_id":[]}),
            serde_json::json!({"eos_token_id":8}),
            serde_json::json!({"eos_token_id":-1}),
        ] {
            assert!(parse_completion(&invalid, 8).is_err());
        }
        let mut state = HnaTextContinuation {
            schema: STATE_SCHEMA.into(),
            prompt_addresses: vec![2],
            emitted_addresses: vec![3],
            generation: 9,
            observation_only: false,
            disposition: HnaTextDisposition::Ready,
        };
        state.interrupt("cycle budget");
        assert!(matches!(
            state.disposition,
            HnaTextDisposition::Interrupted { .. }
        ));
        state.resume().unwrap();
        assert_eq!(state.disposition, HnaTextDisposition::Ready);
        assert_eq!(state.next_addresses(), vec![2, 3]);
        assert_eq!(state.generation, 9);
        state.disposition = HnaTextDisposition::Completed { marker: 1 };
        state.interrupt("cancel");
        assert_eq!(
            state.disposition,
            HnaTextDisposition::Completed { marker: 1 }
        );
    }
}

//! Receiver-exact fusion of heterogeneous source-port realizations.
//!
//! A common world passage does not identify the occurrences which present it.  Text and vision
//! keep distinct boundary ports, incidence, source consequences, and reconstruction fibres.  The
//! only shared native object is the generator acting on the declared world-state face.  This is
//! the computational form of conservation of faces: condensation preserves the complete inverse
//! image of every native consequence instead of declaring fibre members equal.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use thiserror::Error;

pub const HETEROGENEOUS_STANDING_SCHEMA: &str = "holonics.i4.heterogeneous-standing.v1";
pub const HETEROGENEOUS_DECODER_SCHEMA: &str = "holonics.i4.heterogeneous-decoder.v1";
pub const HETEROGENEOUS_FIBRES_SCHEMA: &str = "holonics.i4.heterogeneous-fibres.v1";

/// One exterior tokenizer crossing. Offsets remain apparatus/codec incidence; they never become
/// native semantic taxa or a fusion key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExteriorTokenization {
    pub ids: Vec<u32>,
    pub byte_offsets: Vec<(usize, usize)>,
}

pub fn tokenize_exterior_occurrence(
    tokenizer_json: &[u8],
    text: &str,
    add_special_tokens: bool,
) -> Result<ExteriorTokenization, HeterogeneousFusionRefusal> {
    let tokenizer = tokenizers::Tokenizer::from_bytes(tokenizer_json)
        .map_err(|error| HeterogeneousFusionRefusal::Codec(error.to_string()))?;
    let encoding = tokenizer
        .encode(text, add_special_tokens)
        .map_err(|error| HeterogeneousFusionRefusal::Codec(error.to_string()))?;
    if encoding.get_ids().is_empty() || encoding.get_ids().len() != encoding.get_offsets().len() {
        return Err(HeterogeneousFusionRefusal::Codec(
            "the tokenizer did not return one offset face per codeword".to_owned(),
        ));
    }
    Ok(ExteriorTokenization {
        ids: encoding.get_ids().to_vec(),
        byte_offsets: encoding.get_offsets().to_vec(),
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ModalityPort {
    TextCodeword,
    VisionPatch,
    /// One exact time-ordered acoustic section crossing the inherited audio boundary. Sample and
    /// frame chronology remain in the source incidence fibre; this tag only types the port.
    AudioFrame,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PortDeclaration {
    pub port: ModalityPort,
    pub boundary: String,
    pub source_population: String,
    pub width: u32,
    pub incidence: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourcePortResponse {
    pub family: u32,
    pub state: u32,
    pub port: ModalityPort,
    pub occurrence: String,
    pub occurrence_sha256: String,
    pub consequence_sha256: String,
    pub incidence_sha256: String,
    pub semantic_units: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SharedWorldGenerator {
    pub name: String,
    pub predecessor: u32,
    pub successor: u32,
    pub lineage: String,
    pub common_world_receiver: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HeterogeneousStanding {
    pub schema: String,
    pub source_model_sha256: String,
    pub state_count: u32,
    pub family_count: u32,
    pub ports: Vec<PortDeclaration>,
    pub successor_action: Vec<u32>,
    pub shared_generator: SharedWorldGenerator,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativePortConsequence {
    pub address: u32,
    pub family: u32,
    pub state: u32,
    pub port: ModalityPort,
    pub source_consequence_sha256: String,
    pub source_incidence_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HeterogeneousDecoder {
    pub schema: String,
    /// Family-major, port-major, state-minor. The wire order is validated, never inferred.
    pub consequences: Vec<NativePortConsequence>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FibreMember {
    pub occurrence: String,
    pub occurrence_sha256: String,
    pub consequence_sha256: String,
    pub incidence_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ModalityReconstructionFibre {
    pub native_address: u32,
    pub family: u32,
    pub state: u32,
    pub port: ModalityPort,
    pub members: Vec<FibreMember>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NaturalitySquare {
    pub family: u32,
    pub port: ModalityPort,
    pub source_predecessor: String,
    pub source_successor: String,
    pub native_predecessor: u32,
    pub native_successor: u32,
    pub generator: String,
    pub commutes: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HeterogeneousFibres {
    pub schema: String,
    pub fibres: Vec<ModalityReconstructionFibre>,
    pub naturality_squares: Vec<NaturalitySquare>,
    pub unavailable_ports: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeterogeneousFusionRest {
    pub standing: HeterogeneousStanding,
    pub decoder: HeterogeneousDecoder,
    pub fibres: HeterogeneousFibres,
}

impl HeterogeneousFusionRest {
    /// Found one shared generator from complete source-port responses.
    ///
    /// `family == 0` is developmental. Later families must already carry both states at every
    /// port, but they do not participate in founding the generator; they are successor-history
    /// naturality receivers. No response digest, transcript, label, or coordinate similarity is
    /// used as an equivalence key.
    pub fn found(
        source_model_sha256: String,
        ports: Vec<PortDeclaration>,
        responses: Vec<SourcePortResponse>,
        generator: SharedWorldGenerator,
        unavailable_ports: Vec<String>,
        open_exterior: Vec<String>,
    ) -> Result<Self, HeterogeneousFusionRefusal> {
        if source_model_sha256.len() != 64
            || !source_model_sha256
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit())
        {
            return Err(HeterogeneousFusionRefusal::SourceIdentity);
        }
        if ports.len() < 2 || responses.is_empty() {
            return Err(HeterogeneousFusionRefusal::Boundary);
        }
        let port_set = ports.iter().map(|port| port.port).collect::<BTreeSet<_>>();
        if port_set.len() != ports.len()
            || ports
                .iter()
                .any(|port| port.width == 0 || port.boundary.is_empty())
        {
            return Err(HeterogeneousFusionRefusal::Boundary);
        }
        if generator.predecessor == generator.successor
            || generator.common_world_receiver.is_empty()
            || generator.lineage.is_empty()
        {
            return Err(HeterogeneousFusionRefusal::Generator);
        }
        let state_count = generator
            .predecessor
            .max(generator.successor)
            .checked_add(1)
            .ok_or(HeterogeneousFusionRefusal::Extent)?;
        if state_count != 2 || generator.predecessor != 0 || generator.successor != 1 {
            return Err(HeterogeneousFusionRefusal::Generator);
        }
        let family_count = responses
            .iter()
            .map(|response| response.family)
            .max()
            .ok_or(HeterogeneousFusionRefusal::Boundary)?
            .checked_add(1)
            .ok_or(HeterogeneousFusionRefusal::Extent)?;
        if family_count < 2 {
            return Err(HeterogeneousFusionRefusal::HeldOutFamily);
        }

        let mut by_face = BTreeMap::new();
        for response in responses {
            if !port_set.contains(&response.port)
                || response.state >= state_count
                || response.family >= family_count
                || response.semantic_units == 0
                || response.occurrence.is_empty()
                || !valid_sha(&response.occurrence_sha256)
                || !valid_sha(&response.consequence_sha256)
                || !valid_sha(&response.incidence_sha256)
            {
                return Err(HeterogeneousFusionRefusal::Response);
            }
            let key = (response.family, response.port, response.state);
            if by_face.insert(key, response).is_some() {
                return Err(HeterogeneousFusionRefusal::DuplicateFace);
            }
        }
        for family in 0..family_count {
            for port in &ports {
                for state in 0..state_count {
                    if !by_face.contains_key(&(family, port.port, state)) {
                        return Err(HeterogeneousFusionRefusal::IncompleteFibre);
                    }
                }
                let before = &by_face[&(family, port.port, generator.predecessor)];
                let after = &by_face[&(family, port.port, generator.successor)];
                if before.consequence_sha256 == after.consequence_sha256
                    || before.occurrence_sha256 == after.occurrence_sha256
                {
                    return Err(HeterogeneousFusionRefusal::UnwitnessedPassage);
                }
            }
        }

        let mut consequences = Vec::with_capacity(by_face.len());
        let mut fibres = Vec::with_capacity(by_face.len());
        let mut squares = Vec::with_capacity((family_count as usize) * ports.len());
        for family in 0..family_count {
            for port in &ports {
                let predecessor_address = consequences.len() as u32;
                for state in 0..state_count {
                    let response = &by_face[&(family, port.port, state)];
                    let address = consequences.len() as u32;
                    consequences.push(NativePortConsequence {
                        address,
                        family,
                        state,
                        port: port.port,
                        source_consequence_sha256: response.consequence_sha256.clone(),
                        source_incidence_sha256: response.incidence_sha256.clone(),
                    });
                    fibres.push(ModalityReconstructionFibre {
                        native_address: address,
                        family,
                        state,
                        port: port.port,
                        members: vec![FibreMember {
                            occurrence: response.occurrence.clone(),
                            occurrence_sha256: response.occurrence_sha256.clone(),
                            consequence_sha256: response.consequence_sha256.clone(),
                            incidence_sha256: response.incidence_sha256.clone(),
                        }],
                    });
                }
                squares.push(NaturalitySquare {
                    family,
                    port: port.port,
                    source_predecessor: by_face[&(family, port.port, generator.predecessor)]
                        .occurrence
                        .clone(),
                    source_successor: by_face[&(family, port.port, generator.successor)]
                        .occurrence
                        .clone(),
                    native_predecessor: predecessor_address,
                    native_successor: predecessor_address + 1,
                    generator: generator.name.clone(),
                    commutes: true,
                });
            }
        }
        let rest = Self {
            standing: HeterogeneousStanding {
                schema: HETEROGENEOUS_STANDING_SCHEMA.to_owned(),
                source_model_sha256,
                state_count,
                family_count,
                ports,
                successor_action: vec![generator.successor, generator.successor],
                shared_generator: generator,
                open_exterior,
            },
            decoder: HeterogeneousDecoder {
                schema: HETEROGENEOUS_DECODER_SCHEMA.to_owned(),
                consequences,
            },
            fibres: HeterogeneousFibres {
                schema: HETEROGENEOUS_FIBRES_SCHEMA.to_owned(),
                fibres,
                naturality_squares: squares,
                unavailable_ports,
            },
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(
        standing: &[u8],
        decoder: &[u8],
        fibres: &[u8],
    ) -> Result<Self, HeterogeneousFusionRefusal> {
        let rest = Self {
            standing: serde_json::from_slice(standing)
                .map_err(|error| HeterogeneousFusionRefusal::Wire(error.to_string()))?,
            decoder: serde_json::from_slice(decoder)
                .map_err(|error| HeterogeneousFusionRefusal::Wire(error.to_string()))?,
            fibres: serde_json::from_slice(fibres)
                .map_err(|error| HeterogeneousFusionRefusal::Wire(error.to_string()))?,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn standing_bytes(&self) -> Result<Vec<u8>, HeterogeneousFusionRefusal> {
        self.validate()?;
        serde_json::to_vec(&self.standing)
            .map_err(|error| HeterogeneousFusionRefusal::Wire(error.to_string()))
    }

    pub fn decoder_bytes(&self) -> Result<Vec<u8>, HeterogeneousFusionRefusal> {
        self.validate()?;
        serde_json::to_vec(&self.decoder)
            .map_err(|error| HeterogeneousFusionRefusal::Wire(error.to_string()))
    }

    pub fn fibre_bytes(&self) -> Result<Vec<u8>, HeterogeneousFusionRefusal> {
        self.validate()?;
        serde_json::to_vec(&self.fibres)
            .map_err(|error| HeterogeneousFusionRefusal::Wire(error.to_string()))
    }

    /// Family-major, port-major, state-minor decoder wire for the resident fusion deed.
    pub fn decoder_addresses(&self) -> Vec<u32> {
        self.decoder
            .consequences
            .iter()
            .map(|consequence| consequence.address)
            .collect()
    }

    pub fn starts(&self) -> Vec<u32> {
        vec![
            self.standing.shared_generator.predecessor;
            self.standing.family_count as usize * self.standing.ports.len()
        ]
    }

    pub fn validate(&self) -> Result<(), HeterogeneousFusionRefusal> {
        if self.standing.schema != HETEROGENEOUS_STANDING_SCHEMA
            || self.decoder.schema != HETEROGENEOUS_DECODER_SCHEMA
            || self.fibres.schema != HETEROGENEOUS_FIBRES_SCHEMA
            || !valid_sha(&self.standing.source_model_sha256)
            || self.standing.state_count != 2
            || self.standing.family_count < 2
            || self.standing.ports.len() < 2
            || self.standing.successor_action.len() != self.standing.state_count as usize
            || self.standing.shared_generator.predecessor != 0
            || self.standing.shared_generator.successor != 1
            || self.standing.shared_generator.lineage.is_empty()
            || self
                .standing
                .shared_generator
                .common_world_receiver
                .is_empty()
        {
            return Err(HeterogeneousFusionRefusal::Schema);
        }
        let port_set = self
            .standing
            .ports
            .iter()
            .map(|port| port.port)
            .collect::<BTreeSet<_>>();
        if port_set.len() != self.standing.ports.len()
            || self.standing.ports.iter().any(|port| {
                port.width == 0
                    || port.boundary.is_empty()
                    || port.source_population.is_empty()
                    || port.incidence.is_empty()
            })
            || self.standing.successor_action[0] != 1
            || self.standing.successor_action[1] != 1
        {
            return Err(HeterogeneousFusionRefusal::Boundary);
        }
        let cells = self
            .standing
            .family_count
            .checked_mul(self.standing.ports.len() as u32)
            .ok_or(HeterogeneousFusionRefusal::Extent)?;
        let consequences = cells
            .checked_mul(self.standing.state_count)
            .ok_or(HeterogeneousFusionRefusal::Extent)?;
        if self.decoder.consequences.len() != consequences as usize
            || self.fibres.fibres.len() != consequences as usize
            || self.fibres.naturality_squares.len() != cells as usize
        {
            return Err(HeterogeneousFusionRefusal::IncompleteFibre);
        }
        for (at, consequence) in self.decoder.consequences.iter().enumerate() {
            let state = at as u32 % self.standing.state_count;
            let cell = at as u32 / self.standing.state_count;
            let family = cell / self.standing.ports.len() as u32;
            let port = self.standing.ports[cell as usize % self.standing.ports.len()].port;
            if consequence.address != at as u32
                || consequence.family != family
                || consequence.state != state
                || consequence.port != port
                || self.fibres.fibres[at].native_address != at as u32
                || self.fibres.fibres[at].family != family
                || self.fibres.fibres[at].state != state
                || self.fibres.fibres[at].port != port
                || self.fibres.fibres[at].members.len() != 1
                || !valid_sha(&consequence.source_consequence_sha256)
                || !valid_sha(&consequence.source_incidence_sha256)
                || self.fibres.fibres[at].members.iter().any(|member| {
                    member.consequence_sha256 != consequence.source_consequence_sha256
                        || member.incidence_sha256 != consequence.source_incidence_sha256
                        || member.occurrence.is_empty()
                        || !valid_sha(&member.occurrence_sha256)
                })
            {
                return Err(HeterogeneousFusionRefusal::Decoder);
            }
        }
        for family in 0..self.standing.family_count {
            for (port_at, port) in self.standing.ports.iter().enumerate() {
                let cell = family as usize * self.standing.ports.len() + port_at;
                let before_at = cell * self.standing.state_count as usize;
                let after_at = before_at + 1;
                let before = &self.decoder.consequences[before_at];
                let after = &self.decoder.consequences[after_at];
                let before_member = &self.fibres.fibres[before_at].members[0];
                let after_member = &self.fibres.fibres[after_at].members[0];
                let square = &self.fibres.naturality_squares[cell];
                if before.source_consequence_sha256 == after.source_consequence_sha256
                    || before_member.occurrence_sha256 == after_member.occurrence_sha256
                {
                    return Err(HeterogeneousFusionRefusal::UnwitnessedPassage);
                }
                if !square.commutes
                    || square.family != family
                    || square.port != port.port
                    || square.generator != self.standing.shared_generator.name
                    || square.native_predecessor != before.address
                    || square.native_successor != after.address
                    || square.source_predecessor != before_member.occurrence
                    || square.source_successor != after_member.occurrence
                {
                    return Err(HeterogeneousFusionRefusal::Naturality);
                }
            }
        }
        Ok(())
    }
}

fn valid_sha(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

#[derive(Debug, Error, PartialEq, Eq)]
pub enum HeterogeneousFusionRefusal {
    #[error("the source model identity is not a SHA-256 occurrence frame")]
    SourceIdentity,
    #[error("the heterogeneous boundary has fewer than two distinct typed ports")]
    Boundary,
    #[error("the shared world generator is not the declared two-state passage")]
    Generator,
    #[error("the heterogeneous family extent overflowed")]
    Extent,
    #[error("no held-out receiver family was supplied")]
    HeldOutFamily,
    #[error("a source-port response is malformed or outside the boundary")]
    Response,
    #[error("two source responses claim the same family/port/state face")]
    DuplicateFace,
    #[error("a modality reconstruction fibre is incomplete")]
    IncompleteFibre,
    #[error("a proposed shared passage did not move one source-port consequence")]
    UnwitnessedPassage,
    #[error("the heterogeneous rest schema moved")]
    Schema,
    #[error("the heterogeneous decoder order or address moved")]
    Decoder,
    #[error("a proposed shared-generator square does not commute")]
    Naturality,
    #[error("heterogeneous rest wire: {0}")]
    Wire(String),
    #[error("heterogeneous exterior codec: {0}")]
    Codec(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sha(value: u32) -> String {
        format!("{value:064x}")
    }

    fn response(family: u32, state: u32, port: ModalityPort) -> SourcePortResponse {
        let mark = match (family, state, port) {
            (0, 0, ModalityPort::TextCodeword) => 1,
            (0, 1, ModalityPort::TextCodeword) => 2,
            (0, 0, ModalityPort::VisionPatch) => 3,
            (0, 1, ModalityPort::VisionPatch) => 4,
            (1, 0, ModalityPort::TextCodeword) => 5,
            (1, 1, ModalityPort::TextCodeword) => 6,
            (1, 0, ModalityPort::VisionPatch) => 7,
            _ => 8,
        };
        SourcePortResponse {
            family,
            state,
            port,
            occurrence: format!("family-{family}/state-{state}/{port:?}"),
            occurrence_sha256: sha(mark),
            consequence_sha256: sha(mark + 8),
            incidence_sha256: sha(mark + 16),
            semantic_units: 1,
        }
    }

    fn fixture() -> Result<HeterogeneousFusionRest, HeterogeneousFusionRefusal> {
        let ports = vec![
            PortDeclaration {
                port: ModalityPort::TextCodeword,
                boundary: "ordered codewords".to_owned(),
                source_population: "text".to_owned(),
                width: 8,
                incidence: "serial".to_owned(),
            },
            PortDeclaration {
                port: ModalityPort::VisionPatch,
                boundary: "patches".to_owned(),
                source_population: "vision".to_owned(),
                width: 3,
                incidence: "planar".to_owned(),
            },
        ];
        let responses = (0..2)
            .flat_map(|family| {
                [ModalityPort::TextCodeword, ModalityPort::VisionPatch]
                    .into_iter()
                    .flat_map(move |port| (0..2).map(move |state| response(family, state, port)))
            })
            .collect();
        HeterogeneousFusionRest::found(
            sha(42),
            ports,
            responses,
            SharedWorldGenerator {
                name: "g".to_owned(),
                predecessor: 0,
                successor: 1,
                lineage: "one caused passage".to_owned(),
                common_world_receiver: "declared before conduct".to_owned(),
            },
            vec!["audio".to_owned()],
            vec!["broader histories".to_owned()],
        )
    }

    #[test]
    fn one_generator_conserves_every_distinct_face_in_its_fibre() {
        let rest = fixture().expect("the fixture is complete");
        assert_eq!(rest.standing.ports.len(), 2);
        assert_eq!(rest.standing.family_count, 2);
        assert_eq!(rest.decoder.consequences.len(), 8);
        assert_eq!(rest.fibres.fibres.len(), 8);
        assert_eq!(rest.fibres.naturality_squares.len(), 4);
        assert!(
            rest.fibres
                .naturality_squares
                .iter()
                .all(|square| square.commutes)
        );
        let read = HeterogeneousFusionRest::read(
            &rest.standing_bytes().unwrap(),
            &rest.decoder_bytes().unwrap(),
            &rest.fibre_bytes().unwrap(),
        )
        .unwrap();
        assert_eq!(read, rest);
    }

    #[test]
    fn equal_source_consequence_does_not_witness_a_shared_passage() {
        let mut rest = fixture().expect("the fixture is complete");
        let held = rest.decoder.consequences[0]
            .source_consequence_sha256
            .clone();
        rest.decoder.consequences[1].source_consequence_sha256 = held;
        rest.fibres.fibres[1].members[0].consequence_sha256 = rest.decoder.consequences[0]
            .source_consequence_sha256
            .clone();
        assert_eq!(
            rest.validate(),
            Err(HeterogeneousFusionRefusal::UnwitnessedPassage)
        );
    }

    #[test]
    fn a_stored_naturality_claim_cannot_move_one_conserved_face() {
        let mut rest = fixture().expect("the fixture is complete");
        rest.fibres.naturality_squares[2].source_predecessor = "another occurrence".to_owned();
        assert_eq!(rest.validate(), Err(HeterogeneousFusionRefusal::Naturality));
    }
}

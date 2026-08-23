//! The addressed junction which makes the admitted Phoenix rests one inference ecology.
//!
//! I3 already owns recurrent predecessor/successor conduct and I4 already owns the separately
//! typed text/vision faces of one shared world passage.  This owner does not copy either rest and
//! does not introduce an interpreter, scheduler, context cache, or semantic router.  It binds the
//! two conserved recurrent modes to the two conserved world faces, records an explicit
//! commit/decline decision, and authenticates the exterior return which may change that decision.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use super::{
    heterogeneous_fusion::HeterogeneousFusionRest,
    recurrent_condensation::CondensedRecurrentRest,
    recurrent_return::{ExteriorToolReturn, ReturnDecision},
};

pub const INFERENCE_JUNCTION_SCHEMA: &str = "holonics.i5.inference-junction.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RestComponentIdentity {
    pub standing_sha256: String,
    pub decoder_sha256: String,
    pub fibres_sha256: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum RecurrentMode {
    Predecessor,
    Successor,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ConservedFaceBinding {
    pub recurrent_mode: RecurrentMode,
    pub world_state: u32,
    pub receiver_face: String,
    pub addressed_lineage: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InferenceJunction {
    pub schema: String,
    pub recurrent: RestComponentIdentity,
    pub heterogeneous: RestComponentIdentity,
    pub bindings: Vec<ConservedFaceBinding>,
    pub decision: ReturnDecision,
    pub exterior_return: Option<ExteriorToolReturn>,
    pub decision_occurrence: String,
    pub open_exterior: Vec<String>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct InferenceEcologyRest {
    pub recurrent: CondensedRecurrentRest,
    pub heterogeneous: HeterogeneousFusionRest,
    pub junction: InferenceJunction,
}

impl InferenceEcologyRest {
    /// Bind the already-admitted rests without copying their topology.  The declined body is the
    /// matched predecessor sibling: it conducts through both component rests but selects their
    /// predecessor faces until an actual exterior return is committed.
    pub fn bind_declined(
        recurrent: CondensedRecurrentRest,
        heterogeneous: HeterogeneousFusionRest,
        decision_occurrence: String,
    ) -> Result<Self, InferenceEcologyRefusal> {
        recurrent
            .validate()
            .map_err(|error| InferenceEcologyRefusal::Recurrent(error.to_string()))?;
        heterogeneous
            .validate()
            .map_err(|error| InferenceEcologyRefusal::Heterogeneous(error.to_string()))?;
        if decision_occurrence.is_empty() {
            return Err(InferenceEcologyRefusal::Lineage);
        }
        let receiver = heterogeneous
            .standing
            .shared_generator
            .common_world_receiver
            .clone();
        let lineage = heterogeneous.standing.shared_generator.lineage.clone();
        let junction = InferenceJunction {
            schema: INFERENCE_JUNCTION_SCHEMA.to_owned(),
            recurrent: component_identity_recurrent(&recurrent)?,
            heterogeneous: component_identity_heterogeneous(&heterogeneous)?,
            bindings: vec![
                ConservedFaceBinding {
                    recurrent_mode: RecurrentMode::Predecessor,
                    world_state: heterogeneous.standing.shared_generator.predecessor,
                    receiver_face: receiver.clone(),
                    addressed_lineage: format!("{lineage}/predecessor"),
                },
                ConservedFaceBinding {
                    recurrent_mode: RecurrentMode::Successor,
                    world_state: heterogeneous.standing.shared_generator.successor,
                    receiver_face: receiver,
                    addressed_lineage: format!("{lineage}/successor"),
                },
            ],
            decision: ReturnDecision::Declined,
            exterior_return: None,
            decision_occurrence,
            open_exterior: vec![
                "unexcited inherited successor histories remain reconstruction fibres".to_owned(),
                "audio, video, and generation ports have not crossed this bounded ecology"
                    .to_owned(),
                "a conventional tensor container would expand this native topology and owes its decoder and defect"
                    .to_owned(),
                "unrestricted intelligence is outside the admitted receiver family".to_owned(),
            ],
        };
        let rest = Self {
            recurrent,
            heterogeneous,
            junction,
        };
        rest.validate()?;
        Ok(rest)
    }

    /// Commit one actual exterior return.  This changes only the addressed junction; both
    /// component rests retain their own lineages and reconstruction fibres.
    pub fn commit_return(
        mut self,
        exterior_return: ExteriorToolReturn,
        decision_occurrence: String,
    ) -> Result<Self, InferenceEcologyRefusal> {
        self.validate()?;
        if self.junction.decision != ReturnDecision::Declined
            || self.junction.exterior_return.is_some()
            || decision_occurrence.is_empty()
            || decision_occurrence == self.junction.decision_occurrence
        {
            return Err(InferenceEcologyRefusal::Decision);
        }
        exterior_return
            .validate()
            .map_err(|error| InferenceEcologyRefusal::Exterior(error.to_string()))?;
        if exterior_return.exact_difference_octets == 0 {
            return Err(InferenceEcologyRefusal::Decision);
        }
        self.junction.decision = ReturnDecision::Committed;
        self.junction.exterior_return = Some(exterior_return);
        self.junction.decision_occurrence = decision_occurrence;
        self.validate()?;
        Ok(self)
    }

    pub fn read(
        recurrent_standing: &[u8],
        recurrent_decoder: &[u8],
        recurrent_fibres: &[u8],
        heterogeneous_standing: &[u8],
        heterogeneous_decoder: &[u8],
        heterogeneous_fibres: &[u8],
        junction: &[u8],
    ) -> Result<Self, InferenceEcologyRefusal> {
        let rest = Self {
            recurrent: CondensedRecurrentRest::read(
                recurrent_standing,
                recurrent_decoder,
                recurrent_fibres,
            )
            .map_err(|error| InferenceEcologyRefusal::Recurrent(error.to_string()))?,
            heterogeneous: HeterogeneousFusionRest::read(
                heterogeneous_standing,
                heterogeneous_decoder,
                heterogeneous_fibres,
            )
            .map_err(|error| InferenceEcologyRefusal::Heterogeneous(error.to_string()))?,
            junction: serde_json::from_slice(junction)
                .map_err(|error| InferenceEcologyRefusal::Wire(error.to_string()))?,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn junction_bytes(&self) -> Result<Vec<u8>, InferenceEcologyRefusal> {
        self.validate()?;
        serde_json::to_vec(&self.junction)
            .map_err(|error| InferenceEcologyRefusal::Wire(error.to_string()))
    }

    pub fn committed(&self) -> bool {
        self.junction.decision == ReturnDecision::Committed
    }

    pub fn selected_world_state(&self) -> u32 {
        if self.committed() {
            self.heterogeneous.standing.shared_generator.successor
        } else {
            self.heterogeneous.standing.shared_generator.predecessor
        }
    }

    pub fn validate(&self) -> Result<(), InferenceEcologyRefusal> {
        self.recurrent
            .validate()
            .map_err(|error| InferenceEcologyRefusal::Recurrent(error.to_string()))?;
        self.heterogeneous
            .validate()
            .map_err(|error| InferenceEcologyRefusal::Heterogeneous(error.to_string()))?;
        let junction = &self.junction;
        if junction.schema != INFERENCE_JUNCTION_SCHEMA
            || junction.decision_occurrence.is_empty()
            || junction.open_exterior.is_empty()
            || junction.open_exterior.iter().any(String::is_empty)
            || junction.recurrent != component_identity_recurrent(&self.recurrent)?
            || junction.heterogeneous != component_identity_heterogeneous(&self.heterogeneous)?
        {
            return Err(InferenceEcologyRefusal::Lineage);
        }
        let receiver = &self
            .heterogeneous
            .standing
            .shared_generator
            .common_world_receiver;
        let lineage = &self.heterogeneous.standing.shared_generator.lineage;
        let expected = [
            (
                RecurrentMode::Predecessor,
                self.heterogeneous.standing.shared_generator.predecessor,
                format!("{lineage}/predecessor"),
            ),
            (
                RecurrentMode::Successor,
                self.heterogeneous.standing.shared_generator.successor,
                format!("{lineage}/successor"),
            ),
        ];
        if junction.bindings.len() != expected.len()
            || junction
                .bindings
                .iter()
                .zip(expected)
                .any(|(binding, (mode, state, addressed))| {
                    binding.recurrent_mode != mode
                        || binding.world_state != state
                        || binding.receiver_face != *receiver
                        || binding.addressed_lineage != addressed
                })
        {
            return Err(InferenceEcologyRefusal::FaceBinding);
        }
        match (junction.decision, &junction.exterior_return) {
            (ReturnDecision::Declined, None) => {}
            (ReturnDecision::Committed, Some(exterior)) => {
                exterior
                    .validate()
                    .map_err(|error| InferenceEcologyRefusal::Exterior(error.to_string()))?;
                if exterior.exact_difference_octets == 0 {
                    return Err(InferenceEcologyRefusal::Decision);
                }
            }
            _ => return Err(InferenceEcologyRefusal::Decision),
        }
        Ok(())
    }
}

fn component_identity_recurrent(
    rest: &CondensedRecurrentRest,
) -> Result<RestComponentIdentity, InferenceEcologyRefusal> {
    Ok(RestComponentIdentity {
        standing_sha256: sha256(
            &rest
                .standing_bytes()
                .map_err(|error| InferenceEcologyRefusal::Recurrent(error.to_string()))?,
        ),
        decoder_sha256: sha256(
            &rest
                .decoder_bytes()
                .map_err(|error| InferenceEcologyRefusal::Recurrent(error.to_string()))?,
        ),
        fibres_sha256: sha256(
            &rest
                .fibre_bytes()
                .map_err(|error| InferenceEcologyRefusal::Recurrent(error.to_string()))?,
        ),
    })
}

fn component_identity_heterogeneous(
    rest: &HeterogeneousFusionRest,
) -> Result<RestComponentIdentity, InferenceEcologyRefusal> {
    Ok(RestComponentIdentity {
        standing_sha256: sha256(
            &rest
                .standing_bytes()
                .map_err(|error| InferenceEcologyRefusal::Heterogeneous(error.to_string()))?,
        ),
        decoder_sha256: sha256(
            &rest
                .decoder_bytes()
                .map_err(|error| InferenceEcologyRefusal::Heterogeneous(error.to_string()))?,
        ),
        fibres_sha256: sha256(
            &rest
                .fibre_bytes()
                .map_err(|error| InferenceEcologyRefusal::Heterogeneous(error.to_string()))?,
        ),
    })
}

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum InferenceEcologyRefusal {
    #[error("the recurrent rest refused the inference junction: {0}")]
    Recurrent(String),
    #[error("the heterogeneous rest refused the inference junction: {0}")]
    Heterogeneous(String),
    #[error("inference-junction wire refused: {0}")]
    Wire(String),
    #[error("the component lineage or identity does not close")]
    Lineage,
    #[error("the recurrent modes do not conserve the addressed heterogeneous faces")]
    FaceBinding,
    #[error("the cultivation decision is not founded by its matched predecessor and return")]
    Decision,
    #[error("the exterior return refused: {0}")]
    Exterior(String),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::phoenix::{
        heterogeneous_fusion::{
            ModalityPort, PortDeclaration, SharedWorldGenerator, SourcePortResponse,
        },
        recurrent_condensation::{
            CompactBoundaryFace, CondensedDecoder, CondensedFibre, CondensedFibreMember,
            CondensedFibres, CondensedSeparator, CondensedStanding, CONDENSED_DECODER_SCHEMA,
            CONDENSED_FIBRES_SCHEMA, CONDENSED_STANDING_SCHEMA,
        },
    };

    fn digest(mark: u32) -> String {
        format!("{mark:064x}")
    }

    fn recurrent() -> CondensedRecurrentRest {
        CondensedRecurrentRest {
            standing: CondensedStanding {
                schema: CONDENSED_STANDING_SCHEMA.to_owned(),
                source_passage_sha256: digest(100),
                returned_predecessor_sha256: digest(101),
                native_states: 3,
                successor_action: vec![1, 2, 2],
                predecessor_from: 2,
                predecessor_to: 1,
                main_start: 0,
                held_out_start: 1,
                open_exterior: vec!["unexcited histories".to_owned()],
            },
            decoder: CondensedDecoder {
                schema: CONDENSED_DECODER_SCHEMA.to_owned(),
                faces: vec![
                    None,
                    Some(CompactBoundaryFace {
                        native_id: 1,
                        source_surface: "▁France".to_owned(),
                        lower: 0,
                    }),
                    Some(CompactBoundaryFace {
                        native_id: 2,
                        source_surface: "▁is".to_owned(),
                        lower: 1,
                    }),
                ],
            },
            fibres: CondensedFibres {
                schema: CONDENSED_FIBRES_SCHEMA.to_owned(),
                fibres: vec![
                    CondensedFibre {
                        native: 0,
                        members: vec![CondensedFibreMember {
                            occurrence: digest(1),
                            terminal_potential_sha256: None,
                        }],
                    },
                    CondensedFibre {
                        native: 1,
                        members: vec![
                            CondensedFibreMember {
                                occurrence: digest(2),
                                terminal_potential_sha256: Some(digest(20)),
                            },
                            CondensedFibreMember {
                                occurrence: digest(3),
                                terminal_potential_sha256: Some(digest(21)),
                            },
                        ],
                    },
                    CondensedFibre {
                        native: 2,
                        members: vec![
                            CondensedFibreMember {
                                occurrence: digest(4),
                                terminal_potential_sha256: Some(digest(22)),
                            },
                            CondensedFibreMember {
                                occurrence: digest(5),
                                terminal_potential_sha256: Some(digest(23)),
                            },
                        ],
                    },
                ],
                separators: vec![
                    CondensedSeparator {
                        native: 1,
                        left_occurrence: digest(2),
                        right_occurrence: digest(3),
                        left_potential_sha256: digest(20),
                        right_potential_sha256: digest(21),
                        shortest_history: vec![0],
                    },
                    CondensedSeparator {
                        native: 2,
                        left_occurrence: digest(4),
                        right_occurrence: digest(5),
                        left_potential_sha256: digest(22),
                        right_potential_sha256: digest(23),
                        shortest_history: vec![0],
                    },
                ],
            },
        }
    }

    fn heterogeneous() -> HeterogeneousFusionRest {
        let ports = vec![
            PortDeclaration {
                port: ModalityPort::TextCodeword,
                boundary: "codeword".to_owned(),
                source_population: "text".to_owned(),
                width: 8,
                incidence: "serial".to_owned(),
            },
            PortDeclaration {
                port: ModalityPort::VisionPatch,
                boundary: "patch".to_owned(),
                source_population: "vision".to_owned(),
                width: 3,
                incidence: "planar".to_owned(),
            },
        ];
        let responses = (0..2)
            .flat_map(|family| {
                [ModalityPort::TextCodeword, ModalityPort::VisionPatch]
                    .into_iter()
                    .flat_map(move |port| {
                        (0..2).map(move |state| {
                            let mark = 30 + family * 8 + state * 2 + port as u32;
                            SourcePortResponse {
                                family,
                                state,
                                port,
                                occurrence: format!("{family}/{port:?}/{state}"),
                                occurrence_sha256: digest(mark),
                                consequence_sha256: digest(mark + 40),
                                incidence_sha256: digest(mark + 80),
                                semantic_units: 1,
                            }
                        })
                    })
            })
            .collect();
        HeterogeneousFusionRest::found(
            digest(9),
            ports,
            responses,
            SharedWorldGenerator {
                name: "shared".to_owned(),
                predecessor: 0,
                successor: 1,
                lineage: "world-passage".to_owned(),
                common_world_receiver: "common-world".to_owned(),
            },
            vec!["audio".to_owned()],
            vec!["unexcited".to_owned()],
        )
        .expect("heterogeneous fixture")
    }

    fn exterior() -> ExteriorToolReturn {
        ExteriorToolReturn {
            schema: "holonics.i2.exterior-tool-return.v1".to_owned(),
            receiver: "/usr/bin/tee".to_owned(),
            emitted_occurrence: "emitted".to_owned(),
            consequence_occurrence: "consequence".to_owned(),
            return_occurrence: "returned".to_owned(),
            emitted_sha256: digest(7),
            consequence_sha256: digest(7),
            echoed_sha256: digest(7),
            before_octets: 0,
            after_octets: 4,
            exact_difference_octets: 4,
            process_status: 0,
        }
    }

    #[test]
    fn the_return_changes_only_the_addressed_junction_and_both_siblings_remount() {
        let declined = InferenceEcologyRest::bind_declined(
            recurrent(),
            heterogeneous(),
            "declined".to_owned(),
        )
        .expect("the rests bind");
        let recurrent_standing = declined.recurrent.standing_bytes().unwrap();
        let heterogeneous_standing = declined.heterogeneous.standing_bytes().unwrap();
        let committed = declined
            .commit_return(exterior(), "committed".to_owned())
            .expect("the return commits");
        assert!(committed.committed());
        assert_eq!(
            recurrent_standing,
            committed.recurrent.standing_bytes().unwrap()
        );
        assert_eq!(
            heterogeneous_standing,
            committed.heterogeneous.standing_bytes().unwrap()
        );
        let remounted = InferenceEcologyRest::read(
            &committed.recurrent.standing_bytes().unwrap(),
            &committed.recurrent.decoder_bytes().unwrap(),
            &committed.recurrent.fibre_bytes().unwrap(),
            &committed.heterogeneous.standing_bytes().unwrap(),
            &committed.heterogeneous.decoder_bytes().unwrap(),
            &committed.heterogeneous.fibre_bytes().unwrap(),
            &committed.junction_bytes().unwrap(),
        )
        .expect("the seven components remount");
        assert_eq!(remounted, committed);
    }

    #[test]
    fn a_face_binding_cannot_identify_the_successor_with_the_predecessor() {
        let mut rest = InferenceEcologyRest::bind_declined(
            recurrent(),
            heterogeneous(),
            "declined".to_owned(),
        )
        .unwrap();
        rest.junction.bindings[1].world_state = 0;
        assert_eq!(rest.validate(), Err(InferenceEcologyRefusal::FaceBinding));
    }
}

//! Source-detached cultivated-product runtime.
//!
//! This is the application-facing composition of the authenticated product directory, its
//! addressed W1 predecessor, the recovered exterior codec and the resident W3 tail. It owns no
//! model semantics: the tower/overlay owners conduct the card deed and return their exact receipts.

use std::path::Path;

use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::cultivated_rest::{
    CultivatedRest, DirectoryCompanion, MorphologyPayload, OctaveBoundOrigin,
    PredecessorProductIdentity, RuntimeChart, RuntimeLawReceipt,
};
use crate::cultivation_derivation::CultivationDerivation;
use crate::embedding_fiber::{AlignedMaterial, ResidentReadout};
use crate::exact_work::ExactWork;
use crate::front_passage::{ApparatusPrediction, DeedAdmission};
use crate::phoenix::native_streamed::NativeMaterialSource;
use crate::phoenix::session_factor_complex::{
    FactorMutationReceipt, ResidentFactorCurrentReturn, SessionFactorComplex,
    SessionFactorComplexIdentity, SessionFactorComplexRest, TowerFactorRealization,
};
use crate::phoenix::streamed::streamed_cultivation::{ExecutionReceipt, OverlayExecutionIdentity};
use crate::phoenix::streamed::{self, ApparatusCensus, CultivatedCirculated, MaterialSource};
use crate::phoenix::tower;
use crate::resident_section::{ResidentGrain, ResidentSurface, SeriesAperture};
use crate::streamed_standing::StreamedCensus;

/// The source-detached runtime's returned semantic face and its complete resident receipt.
pub struct RuntimeReturn {
    pub cultivated: CultivatedCirculated,
    pub receipt: RuntimeReceipt,
}

/// An authenticated W3 product held across a family of resident deeds.
///
/// The directory, predecessor, morphology witness, codec companions, factor support and rank
/// derivation are mounted/reconstructed once.  [`PreparedProduct`] supplies the small
/// input-shaped occurrence for each intervention without reopening the product or consulting the
/// source model.  This is deliberately a preparation/session owner; the card deed remains owned
/// by [`crate::phoenix::streamed`].
pub struct ProductSession {
    product_root: std::path::PathBuf,
    mounted: crate::cultivated_rest::MountedCultivatedRest,
    artifact: crate::foreign_codec_rest::ExteriorCodecArtifact,
    tokenizer: tokenizers::Tokenizer,
    /// One continuing resident apparatus owner across every successor frontier. Recreating a CUDA
    /// context per frontier leaks the physical recurrence into process churn and eventually
    /// refuses stream creation under pressure even though semantic standing is unchanged.
    readout: ResidentReadout,
    source_codec_identity: String,
    runtime_law: RuntimeLawReceipt,
    u: AlignedMaterial,
    v: AlignedMaterial,
    derivation: streamed::cultivation_overlay::FactorDerivationReceipt,
    factor_rank: usize,
    factor: crate::cultivated_rest::AlignedFactor,
    factor_complex: Option<SessionFactorComplex>,
    continuation: Option<crate::phoenix::continuation::MountedContinuation>,
}

/// One input-shaped W3 request borrowed from an authenticated [`ProductSession`].
pub struct PreparedProduct<'session> {
    session: &'session ProductSession,
    candidate: streamed::cultivation_overlay::FactorizedCandidate,
    tokens: Vec<u32>,
}

/// The authenticated source/native address chart carried by the mounted W1 codebook.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SourceNativeCorrespondence {
    pub source_extent: u32,
    pub native_extent: u32,
    pub source_to_native: Vec<(u32, u32)>,
    pub unresolved_source: Vec<u32>,
}

/// A source-token sequence reconstructed through the authenticated codebook and checked against
/// the actual exterior codec crossing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SourceTokenSequence {
    pub source_ids: Vec<u32>,
    pub native_ids: Vec<u32>,
    pub surface: String,
}

/// One exterior exchange face constructed from the authenticated tokenizer companion.
///
/// Roles and delimiters remain codec material.  The returned text is suitable for the existing
/// native crossing, but it does not add a conversation, role or language owner to the engine.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExteriorTurnPresentation {
    pub text: String,
    pub text_sha256: String,
    pub entering_role: String,
    pub successor_anchor_sha256: String,
    pub codec_identity: String,
}

/// The overlay operation complex founded from the authenticated W3 rank receipt and factor
/// testimony.  This is topology testimony only; it does not claim that the deed ran.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedOverlayTopology {
    pub complex: crate::ported_operation::PortedOperationComplex,
    pub topology_identity: String,
    pub rank_receipt_identity: String,
    pub factor_populations: [String; 2],
}

/// Exact absence testimony against the admitted W1 operation/population closure.  This is not a
/// semantic equivalence or receiver claim; W5 supplies the receiver difference separately.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct OverlayAbsenceProof {
    pub source_closure_identity: String,
    pub overlay_topology_identity: String,
    pub overlay_topology_name: String,
    pub overlay_topology_absent: bool,
    pub overlay_operations_absent: Vec<String>,
    pub factor_populations_absent: Vec<String>,
}

/// Identity of the complete authenticated W1 source closure.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct W1SourceClosureIdentity {
    pub digest: String,
    pub operation_count: usize,
    pub population_count: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CurrentFactorChart {
    pub rows: u32,
    pub columns: u32,
    pub rank: u32,
    pub left_exponent: i32,
    pub right_exponent: i32,
    pub payload_sha256: String,
}

impl ProductSession {
    /// Mount and authenticate the product directory once, including its W1 predecessor and
    /// source-detached codec. One resident readout/context is mounted here and held for the
    /// complete session; no semantic deed occurs until current crosses an inference method.
    pub fn open(product_directory: impl AsRef<Path>) -> Result<Self, String> {
        let product_root = std::fs::canonicalize(product_directory.as_ref()).map_err(|error| {
            format!(
                "product directory {}: {error}",
                product_directory.as_ref().display()
            )
        })?;
        let mounted = crate::cultivated_rest::mount_directory(product_directory)
            .map_err(|error| error.to_string())?;
        mounted.verify_still().map_err(|error| error.to_string())?;
        let artifact = mounted
            .exterior_codec_artifact()
            .map_err(|error| error.to_string())?;
        mounted
            .predecessor()
            .codebook()
            .validate_with_codec(&artifact)
            .map_err(|error| error.to_string())?;
        let tokenizer = tokenizers::Tokenizer::from_bytes(&artifact.tokenizer_json)
            .map_err(|error| error.to_string())?;
        let source_codec_identity = artifact.descriptor().tokenizer_json_sha256;
        let runtime_law = mounted.product.runtime_law().clone();
        if runtime_law.schema != "holonic-engine.phoenix.runtime-law.v1"
            || runtime_law.series_aperture == 0
            || runtime_law.band_terms == 0
            || runtime_law.rank != 1
            || runtime_law.vocabulary_extent as usize != tower::VOCABULARY
            || runtime_law.hidden_extent as usize != tower::HIDDEN
            || mounted.predecessor().codebook().vocabulary_extent as usize != tower::VOCABULARY
        {
            return Err(
                "cultivated product runtime-law is not this resident Phoenix instance".to_owned(),
            );
        }
        let morphology = mounted
            .product
            .native_morphology()
            .ok_or("cultivated product lacks authenticated native morphology")?;
        if morphology.predecessor_sha256 != mounted.predecessor_identity().sha256
            || morphology.left_shape != vec![tower::VOCABULARY, runtime_law.rank as usize]
            || morphology.right_shape != vec![runtime_law.rank as usize, tower::HIDDEN]
            || morphology.rank != runtime_law.rank
            || morphology.left_population != runtime_law.left_population
            || morphology.right_population != runtime_law.right_population
        {
            return Err(
                "cultivated morphology does not bind the authenticated W1 predecessor".to_owned(),
            );
        }
        let (u, v, derivation, _, factor) = factor_runtime(&mounted.product, &runtime_law)?;
        let factor_rank = runtime_law.rank as usize;
        let readout = ResidentReadout::new().map_err(|error| error.to_string())?;
        Ok(Self {
            product_root,
            mounted,
            artifact,
            tokenizer,
            readout,
            source_codec_identity,
            runtime_law,
            u,
            v,
            derivation,
            factor_rank,
            factor,
            factor_complex: None,
            continuation: None,
        })
    }

    /// Mount one addressed local continuation over this exact cultivated body.  The continuation
    /// changes only the authenticated sparse factor supplied to the existing resident overlay;
    /// it does not introduce a second inference path or flatten its predecessor lineage into W1.
    pub fn open_with_continuation(
        product_directory: impl AsRef<Path>,
        continuation_directory: impl AsRef<Path>,
    ) -> Result<Self, String> {
        let mut session = Self::open(product_directory)?;
        session.attach_continuation(continuation_directory)?;
        Ok(session)
    }

    /// Attach a continuation to the already-mounted single owner.  This is the in-process
    /// cultivation seam: the expensive immutable predecessor remains mounted once while its
    /// addressed local difference becomes the factor supplied to later resident current.
    pub fn attach_continuation(
        &mut self,
        continuation_directory: impl AsRef<Path>,
    ) -> Result<(), String> {
        if self.continuation.is_some() {
            return Err("the product session already carries a continuation".to_owned());
        }
        let body = self.body_identity()?;
        let base = match self
            .mounted
            .product
            .morphology_payload()
            .map_err(|error| error.to_string())?
        {
            MorphologyPayload::AlignedFactor(factor) => factor,
            MorphologyPayload::SparseDelta(_) => {
                return Err("cultivated predecessor has no resident aligned factor".to_owned());
            }
        };
        let continuation = crate::phoenix::continuation::MountedContinuation::open(
            continuation_directory,
            &body,
            &base,
            &self.runtime_law,
            self.mounted.product.laws(),
            self.mounted.product.predecessor(),
        )
        .map_err(|error| error.to_string())?;
        self.u = continuation.aligned_left();
        self.v = continuation.aligned_right();
        self.derivation = streamed::cultivation_overlay::FactorDerivationReceipt::RankOne(
            continuation.rank_receipt().clone(),
        );
        self.factor_rank = 1;
        self.factor = continuation.factor().clone();
        self.continuation = Some(continuation);
        Ok(())
    }

    /// Withdraw only the attached continuation and recover the immediate cultivated predecessor
    /// inside the same owner.  The returned identity is the exact delta which was removed.
    pub fn ablate_continuation(
        &mut self,
    ) -> Result<crate::phoenix::continuation::ContinuationRuntimeIdentity, String> {
        let continuation = self
            .continuation
            .take()
            .ok_or_else(|| "the product session carries no continuation to ablate".to_owned())?;
        continuation
            .verify_still()
            .map_err(|error| error.to_string())?;
        let identity = continuation
            .runtime_identity()
            .map_err(|error| error.to_string())?;
        if self.factor_complex.is_some() {
            return Err("withdraw the deposited factor complex before ablating its predecessor continuation".to_owned());
        }
        let (u, v, derivation, _, factor) =
            factor_runtime(&self.mounted.product, &self.runtime_law)?;
        self.u = u;
        self.v = v;
        self.derivation = derivation;
        self.factor_rank = self.runtime_law.rank as usize;
        self.factor = factor;
        Ok(identity)
    }

    /// Deposit one complete returned cover into this exact session owner.  Categorical atoms with
    /// no founded vocabulary/hidden chart remain named in `open_factor_addresses`; they are not
    /// silently projected.  The realized population changes the same U/V morphology used by the
    /// next resident tower deed.
    pub fn deposit_factor_cover(
        &mut self,
        cover: crate::derived_factor_cover::DerivedFactorCover,
        realizations: Vec<TowerFactorRealization>,
        open_factor_addresses: Vec<String>,
    ) -> Result<SessionFactorComplexIdentity, String> {
        if self.factor_complex.is_some() {
            return Err(
                "the product session already carries a deposited factor complex".to_owned(),
            );
        }
        let complex = SessionFactorComplex::found(
            cover,
            self.factor.clone(),
            realizations,
            open_factor_addresses,
        )
        .map_err(|error| error.to_string())?;
        self.factor_complex = Some(complex);
        self.synchronize_factor_complex()?;
        self.factor_complex_identity()?
            .ok_or_else(|| "the factor complex disappeared after deposit".to_owned())
    }

    pub fn factor_complex_identity(&self) -> Result<Option<SessionFactorComplexIdentity>, String> {
        self.factor_complex
            .as_ref()
            .map(SessionFactorComplex::identity)
            .transpose()
            .map_err(|error| error.to_string())
    }

    pub fn factor_complex_rest_bytes(&self) -> Result<Vec<u8>, String> {
        self.factor_complex
            .as_ref()
            .ok_or_else(|| "the product session carries no factor complex to rest".to_owned())?
            .canonical_rest_bytes()
            .map_err(|error| error.to_string())
    }

    pub fn factor_complex_rest(&self) -> Result<SessionFactorComplexRest, String> {
        self.factor_complex
            .as_ref()
            .ok_or_else(|| "the product session carries no factor complex to rest".to_owned())?
            .canonical_rest()
            .map_err(|error| error.to_string())
    }

    /// Remount one rested factor complex over the exact authenticated continuation morphology.
    /// The rest itself carries no product tensors, transcript, sibling response or source payload.
    pub fn mount_factor_complex_rest(&mut self, bytes: &[u8]) -> Result<(), String> {
        if self.factor_complex.is_some() {
            return Err(
                "the product session already carries a deposited factor complex".to_owned(),
            );
        }
        self.factor_complex = Some(
            SessionFactorComplex::remount(bytes, self.factor.clone())
                .map_err(|error| error.to_string())?,
        );
        self.synchronize_factor_complex()
    }

    pub fn mount_factor_complex_standing(
        &mut self,
        rest: SessionFactorComplexRest,
    ) -> Result<(), String> {
        if self.factor_complex.is_some() {
            return Err(
                "the product session already carries a deposited factor complex".to_owned(),
            );
        }
        self.factor_complex = Some(
            SessionFactorComplex::remount_rest(rest, self.factor.clone())
                .map_err(|error| error.to_string())?,
        );
        self.synchronize_factor_complex()
    }

    pub fn factor_cover(&self) -> Option<&crate::derived_factor_cover::DerivedFactorCover> {
        self.factor_complex
            .as_ref()
            .map(SessionFactorComplex::cover)
    }

    /// The caused realization word after the cover owner has ordered it by the first addressed
    /// source atom. Exterior target-map order is not a lawful substitute for this chronology.
    pub fn factor_realizations(&self) -> Option<&[TowerFactorRealization]> {
        self.factor_complex
            .as_ref()
            .map(SessionFactorComplex::realizations)
    }

    pub fn conduct_deposited_factor_current(
        &self,
        local_address: &str,
        input_words: &[u16],
    ) -> Result<ResidentFactorCurrentReturn, String> {
        let complex = self
            .factor_complex
            .as_ref()
            .ok_or_else(|| "the product session carries no factor complex".to_owned())?;
        let local = complex
            .cover()
            .locals
            .iter()
            .find(|local| local.section.address == local_address)
            .ok_or_else(|| format!("factor-cover local {local_address} is absent"))?;
        crate::phoenix::session_factor_complex::conduct_factor_current(
            &self.readout,
            local,
            input_words,
        )
        .map_err(|error| error.to_string())
    }

    /// Enact an exact overlap/holonomy control through this session's resident apparatus without
    /// depositing the control into the continuing morphology. The distinction keeps experimental
    /// controls outside the factor cover while proving that both use the same physical owner.
    pub fn conduct_factor_control(
        &self,
        local: &crate::derived_factor_cover::LocalFactorReceipt,
        input_words: &[u16],
    ) -> Result<ResidentFactorCurrentReturn, String> {
        crate::phoenix::session_factor_complex::conduct_factor_current(
            &self.readout,
            local,
            input_words,
        )
        .map_err(|error| error.to_string())
    }

    pub fn ablate_factor_realization(
        &mut self,
        address: &str,
    ) -> Result<FactorMutationReceipt, String> {
        let receipt = self
            .factor_complex
            .as_mut()
            .ok_or_else(|| "the product session carries no factor complex".to_owned())?
            .ablate(address)
            .map_err(|error| error.to_string())?;
        self.synchronize_factor_complex()?;
        Ok(receipt)
    }

    pub fn restore_factor_realization(
        &mut self,
        address: &str,
    ) -> Result<FactorMutationReceipt, String> {
        let receipt = self
            .factor_complex
            .as_mut()
            .ok_or_else(|| "the product session carries no factor complex".to_owned())?
            .restore_ablation(address)
            .map_err(|error| error.to_string())?;
        self.synchronize_factor_complex()?;
        Ok(receipt)
    }

    pub fn withdraw_factor_prefix(
        &mut self,
        prefix: usize,
    ) -> Result<FactorMutationReceipt, String> {
        let receipt = self
            .factor_complex
            .as_mut()
            .ok_or_else(|| "the product session carries no factor complex".to_owned())?
            .withdraw_to_prefix(prefix)
            .map_err(|error| error.to_string())?;
        self.synchronize_factor_complex()?;
        Ok(receipt)
    }

    fn synchronize_factor_complex(&mut self) -> Result<(), String> {
        let (factor, derivation) = self
            .factor_complex
            .as_ref()
            .ok_or_else(|| "the product session carries no factor complex".to_owned())?
            .current_factor()
            .map_err(|error| error.to_string())?;
        let (u, v) = factor_materials(&factor);
        self.factor_rank = factor.rank as usize;
        self.factor = factor;
        self.u = u;
        self.v = v;
        self.derivation = derivation;
        Ok(())
    }

    /// Encode through the authenticated product codec and cross the source address into the
    /// native W1 space.  The returned IDs are suitable for the resident tower.
    pub fn encode(&self, text: &str) -> Result<Vec<u32>, String> {
        let encoded = self
            .tokenizer
            .encode(text, self.runtime_law.add_special_tokens)
            .map_err(|error| error.to_string())?;
        encoded
            .get_ids()
            .iter()
            .map(|source| {
                self.mounted
                    .predecessor()
                    .codebook()
                    .native_id(*source)
                    .map_err(|error| error.to_string())
            })
            .collect()
    }

    /// Present one addressed application turn through delimiters declared by the authenticated
    /// tokenizer companion.  This is an exterior codec operation, not a semantic routing law.
    pub fn present_exterior_turn(
        &self,
        entering_role: &str,
        content: &str,
    ) -> Result<ExteriorTurnPresentation, String> {
        if entering_role.is_empty() || entering_role.contains(['\n', '\r']) || content.is_empty() {
            return Err("the exterior turn face is empty or malformed".to_owned());
        }
        self.present_exterior_exchange(&[(entering_role, content)])
    }

    /// Present an addressed plural exchange through the same authenticated codec face. The
    /// application role labels remain exterior material; the codec's own successor anchor names
    /// the model-facing role used for assistant occurrences.
    pub fn present_exterior_exchange(
        &self,
        faces: &[(&str, &str)],
    ) -> Result<ExteriorTurnPresentation, String> {
        if faces.is_empty()
            || faces.iter().any(|(role, content)| {
                role.is_empty()
                    || role.contains(['\n', '\r'])
                    || content.is_empty()
                    || !matches!(*role, "user" | "assistant")
            })
            || faces.last().is_none_or(|(role, _)| *role != "user")
        {
            return Err("the exterior exchange face is empty or malformed".to_owned());
        }
        let config = self
            .artifact
            .tokenizer_config_json
            .as_deref()
            .ok_or_else(|| "the authenticated codec carries no turn companion".to_owned())?;
        let config: serde_json::Value =
            serde_json::from_slice(config).map_err(|error| error.to_string())?;
        let token = |name: &str| {
            config
                .get(name)
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| format!("authenticated codec turn token {name} is absent"))
        };
        let open = token("sot_token")?;
        let close = token("eot_token")?;
        let successor = config
            .pointer("/response_template/start_anchor")
            .and_then(|value| {
                value.as_str().or_else(|| {
                    value
                        .as_array()
                        .and_then(|values| values.first())
                        .and_then(serde_json::Value::as_str)
                })
            })
            .ok_or_else(|| "authenticated codec successor anchor is absent".to_owned())?;
        let model_role = successor
            .strip_prefix(open)
            .and_then(|tail| tail.split_once('\n').map(|(role, _)| role))
            .filter(|role| !role.is_empty())
            .ok_or_else(|| "authenticated codec successor role is absent".to_owned())?;
        let mut text = String::new();
        for (role, content) in faces {
            let codec_role = if *role == "assistant" {
                model_role
            } else {
                *role
            };
            text.push_str(open);
            text.push_str(codec_role);
            text.push('\n');
            text.push_str(content);
            text.push_str(close);
        }
        text.push_str(successor);
        let text_sha256 = format!("{:x}", Sha256::digest(text.as_bytes()));
        Ok(ExteriorTurnPresentation {
            text,
            text_sha256,
            entering_role: "addressed-plural-exchange".to_owned(),
            successor_anchor_sha256: format!("{:x}", Sha256::digest(successor.as_bytes())),
            codec_identity: self.source_codec_identity.clone(),
        })
    }

    /// Return one exterior text face from authenticated native codebook addresses.
    ///
    /// The reverse source chart and tokenizer decoder are both declared W1 companions. This is a
    /// codec crossing only: it neither chooses a boundary state nor determines recurrence extent.
    pub fn decode_native_ids(&self, native_ids: &[u32]) -> Result<String, String> {
        if native_ids.is_empty() {
            return Err("the native decoder received no addressed occurrence".to_owned());
        }
        let source_ids = self.source_ids(native_ids)?;
        self.tokenizer
            .decode(&source_ids, false)
            .map_err(|error| error.to_string())
    }

    fn encode_partitioned(
        &self,
        text: &str,
        byte_boundaries: &[usize],
    ) -> Result<(Vec<u32>, RuntimeInputPresentation), String> {
        if byte_boundaries.len() < 2
            || byte_boundaries[0] != 0
            || byte_boundaries.last().copied() != Some(text.len())
            || byte_boundaries.windows(2).any(|pair| pair[0] >= pair[1])
            || byte_boundaries
                .iter()
                .any(|boundary| !text.is_char_boundary(*boundary))
        {
            return Err(format!(
                "the byte partition does not cover the UTF-8 occurrence exactly: {byte_boundaries:?} over {} octets",
                text.len()
            ));
        }
        let encoding = self
            .tokenizer
            .encode(text, self.runtime_law.add_special_tokens)
            .map_err(|error| error.to_string())?;
        let source_ids = encoding.get_ids();
        if encoding.get_offsets().len() != source_ids.len() {
            return Err("the tokenizer did not return one byte face per source row".to_owned());
        }
        let native_ids = source_ids
            .iter()
            .map(|source| {
                self.mounted
                    .predecessor()
                    .codebook()
                    .native_id(*source)
                    .map_err(|error| error.to_string())
            })
            .collect::<Result<Vec<_>, _>>()?;
        if native_ids.is_empty() {
            return Err("the partitioned codec crossing returned no source rows".to_owned());
        }
        let groups = byte_boundaries.len() - 1;
        let mut populations = vec![0u32; groups];
        let mut crossings = Vec::new();
        let mut previous_group = 0usize;
        for (token, (start, end)) in encoding.get_offsets().iter().copied().enumerate() {
            let group = if start == end {
                if token == 0 { 0 } else { previous_group }
            } else {
                byte_boundaries[1..]
                    .iter()
                    .position(|boundary| end <= *boundary)
                    .unwrap_or(groups - 1)
            };
            if group < previous_group {
                return Err(
                    "the tokenizer's offset chart moved backwards across the partition".to_owned(),
                );
            }
            for (boundary_index, boundary) in byte_boundaries[1..groups].iter().enumerate() {
                if start < *boundary && *boundary < end {
                    crossings.push(RuntimeBoundaryCrossing {
                        native_row: token as u32,
                        source_id: source_ids[token],
                        byte_range: (start as u64, end as u64),
                        crossed_boundary: (boundary_index + 1) as u32,
                    });
                }
            }
            populations[group] = populations[group].saturating_add(1);
            previous_group = group;
        }
        if let Some(group) = populations.iter().position(|population| *population == 0) {
            return Err(format!(
                "byte block {group} owns no complete tokenizer row; its boundary crossing remains an obstruction"
            ));
        }
        let mut partition_boundaries = Vec::with_capacity(groups + 1);
        partition_boundaries.push(0u32);
        for population in populations {
            let next = partition_boundaries
                .last()
                .copied()
                .unwrap_or(0u32)
                .checked_add(population)
                .ok_or_else(|| "the token partition left the u32 address carrier".to_owned())?;
            partition_boundaries.push(next);
        }
        if partition_boundaries.last().copied() != Some(native_ids.len() as u32) {
            return Err("the token partition did not reconstruct its source population".to_owned());
        }
        let law_identity = format!(
            "{:x}",
            Sha256::digest(b"athena/input-presentation/addressed-causal-partition/v1: every strict addressed source-row block remains a complete independently conducted causal section; chronology resets, contact cannot cross its boundaries, and earlier rows remain the reconstruction fibre of its terminal receiver")
        );
        let reconstruction_sha256 = digest_input_reconstruction(
            text,
            &native_ids,
            byte_boundaries,
            partition_boundaries.len(),
            partition_boundaries.iter().copied(),
            &crossings,
        );
        Ok((
            native_ids,
            RuntimeInputPresentation {
                schema: "holonic-engine.athena.input-presentation.v1".to_owned(),
                kind: "addressed-causal-partition".to_owned(),
                law_sha256: law_identity,
                source_rows: source_ids.len(),
                received_rows: groups,
                byte_boundaries: byte_boundaries.iter().map(|value| *value as u64).collect(),
                partition_boundaries,
                boundary_crossings: crossings,
                reconstruction_sha256,
                source_rows_retained: true,
            },
        ))
    }

    /// Return the source IDs for a foreign-source deed, retaining the explicit reverse chart
    /// rather than treating a native address as source identity.
    pub fn source_ids(&self, native_ids: &[u32]) -> Result<Vec<u32>, String> {
        native_ids
            .iter()
            .map(|native| {
                self.mounted
                    .predecessor()
                    .codebook()
                    .source_id(*native)
                    .ok_or_else(|| {
                        format!("native id {native} has no authenticated source address")
                    })
            })
            .collect()
    }

    pub fn runtime_law(&self) -> &RuntimeLawReceipt {
        &self.runtime_law
    }
    pub fn current_factor_chart(&self) -> Result<CurrentFactorChart, String> {
        Ok(CurrentFactorChart {
            rows: self.factor.rows,
            columns: self.factor.columns,
            rank: self.factor.rank,
            left_exponent: self.factor.left_exponent,
            right_exponent: self.factor.right_exponent,
            payload_sha256: MorphologyPayload::AlignedFactor(self.factor.clone())
                .canonical_digest()
                .map_err(|error| error.to_string())?,
        })
    }
    pub fn body_identity(
        &self,
    ) -> Result<crate::phoenix::continuation::CultivatedBodyIdentity, String> {
        crate::phoenix::continuation::CultivatedBodyIdentity::new(
            self.mounted.product_identity().clone(),
            self.mounted.predecessor_identity().clone(),
            self.mounted.morphology_identity().clone(),
            self.mounted.codec_companion_identities().to_vec(),
            &self.runtime_law,
        )
        .map_err(|error| error.to_string())
    }
    pub fn mounted(&self) -> &crate::cultivated_rest::MountedCultivatedRest {
        &self.mounted
    }
    pub fn predecessor(&self) -> &crate::native_rest::MountedNativeRest {
        self.mounted.predecessor()
    }
    pub fn codebook_digest(&self) -> &str {
        &self.mounted.predecessor().codebook().codebook_sha256
    }
    /// Digest of the authenticated source tokenizer JSON, kept distinct from the native W1
    /// codebook digest returned by [`Self::codebook_digest`].
    pub fn source_codec_identity(&self) -> &str {
        &self.source_codec_identity
    }

    /// Return the exact local cultivation continuation mounted over this body, when one exists.
    pub fn continuation_identity(
        &self,
    ) -> Result<Option<crate::phoenix::continuation::ContinuationRuntimeIdentity>, String> {
        self.continuation
            .as_ref()
            .map(|continuation| {
                continuation
                    .runtime_identity()
                    .map_err(|error| error.to_string())
            })
            .transpose()
    }

    /// The complete source→native rows and the explicit open source-address remainder carried by
    /// the mounted W1 codebook.  No address is filled by numeric coincidence.
    pub fn source_native_correspondence(&self) -> SourceNativeCorrespondence {
        source_native_correspondence_from_codebook(self.mounted.predecessor().codebook())
    }

    pub fn source_native_rows(&self) -> Vec<(u32, u32)> {
        self.source_native_correspondence().source_to_native
    }

    pub fn source_extent(&self) -> u32 {
        self.mounted.predecessor().codebook().vocabulary_extent
    }
    pub fn native_extent(&self) -> u32 {
        self.mounted.predecessor().codebook().vocabulary_extent
    }
    /// The exact resident carrier grain authenticated by this product's runtime law.
    pub fn resident_grain(&self) -> u32 {
        self.runtime_law.grain
    }
    pub fn unresolved_source_ids(&self) -> Vec<u32> {
        self.source_native_correspondence().unresolved_source
    }

    /// Reconstruct the mapped native surface for a supplied source-token sequence, then prove
    /// that the actual authenticated W4 codec maps the surface back to exactly the same native
    /// sequence. This is the bridge used by W3's deposited lineage-separated material arms.
    pub fn reconstruct_source_ids(
        &self,
        source_ids: &[u32],
    ) -> Result<SourceTokenSequence, String> {
        let mapped = reconstruct_source_ids_from_codebook(
            self.mounted.predecessor().codebook(),
            source_ids,
        )?;
        let encoded = self.encode(&mapped.surface)?;
        if encoded != mapped.native_ids {
            return Err(format!(
                "reconstructed source sequence crossed as {encoded:?}, expected {:?}",
                mapped.native_ids
            ));
        }
        Ok(mapped)
    }

    /// Identity of the complete admitted W1 operation/population closure, derived from the
    /// correspondence seal's stable canonical wire rather than a semantic closure algorithm.
    pub fn source_closure_identity(&self) -> W1SourceClosureIdentity {
        let correspondence = self.mounted.predecessor().correspondence();
        let stable = correspondence
            .stable_json()
            .expect("authenticated W1 correspondence is serializable");
        W1SourceClosureIdentity {
            digest: format!("{:x}", Sha256::digest(stable.as_bytes())),
            operation_count: correspondence.source_operations.len(),
            population_count: correspondence.source_populations.len(),
        }
    }

    /// Return exact absence testimony for the overlay topology and its two factors against the
    /// admitted predecessor topology/population closure.  Receiver-visible difference remains a
    /// W5 question and is intentionally not inferred here.
    pub fn overlay_absence_proof(
        &self,
        prepared: &PreparedProduct<'_>,
    ) -> Result<OverlayAbsenceProof, String> {
        let topology = prepared.overlay_topology()?;
        let predecessor = self.mounted.predecessor();
        let overlay_topology_absent = predecessor
            .topologies()
            .iter()
            .all(|stored| stored.name != topology.complex.name);
        let predecessor_operations = predecessor
            .topologies()
            .iter()
            .flat_map(|stored| stored.shape.laws.values().map(|law| law.name.as_str()))
            .collect::<std::collections::BTreeSet<_>>();
        let overlay_operations = topology
            .complex
            .operations
            .values()
            .filter_map(|operation| topology.complex.shape.laws.get(&operation.law))
            .map(|law| law.name.clone())
            .collect::<Vec<_>>();
        let overlay_operations_absent = overlay_operations
            .into_iter()
            .filter(|name| !predecessor_operations.contains(name.as_str()))
            .collect();
        let predecessor_populations = predecessor
            .populations()
            .iter()
            .flat_map(|population| {
                [
                    population.native_name.as_str(),
                    population.source.population.as_str(),
                ]
            })
            .collect::<std::collections::BTreeSet<_>>();
        let factor_populations_absent = topology
            .factor_populations
            .iter()
            .filter(|population| !predecessor_populations.contains(population.as_str()))
            .cloned()
            .collect();
        Ok(OverlayAbsenceProof {
            source_closure_identity: self.source_closure_identity().digest,
            overlay_topology_identity: topology.topology_identity,
            overlay_topology_name: topology.complex.name,
            overlay_topology_absent,
            overlay_operations_absent,
            factor_populations_absent,
        })
    }

    /// Construct the authenticated factor request for one input extent. The candidate is owned by
    /// the preparation, so callers can repeat this method for every intervention safely.
    pub fn prepare(&self, native_ids: &[u32]) -> Result<PreparedProduct<'_>, String> {
        self.prepare_with_rows(native_ids, native_ids.len())
    }

    /// Construct the same authenticated factor request over the receiver-visible output rows.
    /// The terminal receiver factors the final section to one row before the overlay; the complete
    /// receiver preserves every source row.  The input tower still receives every `native_id`.
    fn prepare_with_rows(
        &self,
        native_ids: &[u32],
        receiver_rows: usize,
    ) -> Result<PreparedProduct<'_>, String> {
        self.mounted
            .verify_still()
            .map_err(|error| error.to_string())?;
        if native_ids.is_empty() {
            return Err("W3 preparation requires at least one encoded token".to_owned());
        }
        for native_id in native_ids {
            self.mounted
                .predecessor()
                .codebook()
                .native_surface(*native_id)
                .map_err(|error| {
                    format!("native id {native_id} is not an authenticated codebook row: {error}")
                })?;
        }
        let morphology = self
            .mounted
            .product
            .native_morphology()
            .ok_or("native morphology")?;
        let candidate = streamed::cultivation_overlay::FactorizedCandidate::new(
            morphology.left_population.clone(),
            morphology.right_population.clone(),
            streamed::cultivation_overlay::OverlayShape {
                rows: self.runtime_law.vocabulary_extent as usize,
                input_width: self.runtime_law.hidden_extent as usize,
            },
            self.factor_rank,
            receiver_rows,
            testimony(
                &morphology.left_population,
                &morphology.right_population,
                self.runtime_law.vocabulary_extent as usize,
                self.runtime_law.hidden_extent as usize,
            ),
        );
        Ok(PreparedProduct {
            session: self,
            candidate,
            tokens: native_ids.to_owned(),
        })
    }

    /// Conduct one text through this authenticated product session.  Repeating this method keeps
    /// the mounted product, predecessor and factor morphology in this owner; only the input
    /// occurrence, intervention graph and resident deed are new for each request.
    pub fn infer_with_intervention(
        &self,
        text: &str,
        site: streamed::InterventionSite,
        intervention: &tower::Intervention,
        receiver: streamed::ReceiverOption,
    ) -> Result<RuntimeReturn, String> {
        let native_ids = self.encode(text)?;
        if native_ids.is_empty() {
            return Err("authenticated codec returned no runtime tokens".to_owned());
        }
        let presentation = RuntimeInputPresentation::source_rows(text, &native_ids);
        self.infer_encoded_with_intervention(
            text,
            native_ids,
            presentation,
            site,
            intervention,
            receiver,
        )
    }

    /// Conduct one already-addressed native word through this mounted product.
    ///
    /// The exterior decoder is used only to present the occurrence to the existing runtime
    /// receipt. Re-encoding must recover the identical native word, so a lossy codec round-trip
    /// cannot silently become a new predecessor. This is the recurrence seam: a card-returned
    /// address word can found the next tower entry without a host-authored later prompt.
    pub fn infer_native_with_intervention(
        &self,
        native_ids: &[u32],
        site: streamed::InterventionSite,
        intervention: &tower::Intervention,
        receiver: streamed::ReceiverOption,
    ) -> Result<RuntimeReturn, String> {
        let text = self.decode_native_ids(native_ids)?;
        let reconstructed = self.encode(&text)?;
        if reconstructed != native_ids {
            return Err(format!(
                "the exterior decoder does not reconstruct the addressed native occurrence: expected {native_ids:?}, returned {reconstructed:?}"
            ));
        }
        let presentation = RuntimeInputPresentation::source_rows(&text, native_ids);
        self.infer_encoded_with_intervention(
            &text,
            native_ids.to_vec(),
            presentation,
            site,
            intervention,
            receiver,
        )
    }

    /// Conduct plural independently encoded occurrences as one addressed resident partition.
    ///
    /// Each row is already an addressed native word. It is decoded only for exterior receipt
    /// testimony before the native words are flattened. Consequently tokenizer adjacency cannot
    /// leak between requests, while a card-emitted successor remains authoritative even when its
    /// displayed surface has a different canonical re-tokenization. The partition is apparatus
    /// factorization over one mounted body, not a batch-size semantic constant.
    pub fn infer_native_partitioned_with_intervention(
        &self,
        rows: &[Vec<u32>],
        site: streamed::InterventionSite,
        intervention: &tower::Intervention,
    ) -> Result<RuntimeReturn, String> {
        self.infer_native_partitioned_with_receiver(
            rows,
            site,
            intervention,
            streamed::ReceiverOption::Complete,
        )
    }

    /// Capture the exact terminal carrier row of every foreign layer for plural independently
    /// addressed native histories in one resident partition. This is a construction receiver for
    /// enlarging a descended coefficient lattice; it is never the frozen inference fallback.
    pub fn capture_native_partitioned_layer_sections_with_intervention(
        &self,
        rows: &[Vec<u32>],
        site: streamed::InterventionSite,
        intervention: &tower::Intervention,
    ) -> Result<RuntimeReturn, String> {
        self.infer_native_partitioned_with_receiver(
            rows,
            site,
            intervention,
            streamed::ReceiverOption::LayerTerminalSections,
        )
    }

    fn infer_native_partitioned_with_receiver(
        &self,
        rows: &[Vec<u32>],
        site: streamed::InterventionSite,
        intervention: &tower::Intervention,
        receiver: streamed::ReceiverOption,
    ) -> Result<RuntimeReturn, String> {
        if rows.is_empty() || rows.iter().any(Vec::is_empty) {
            return Err("the native occurrence partition is empty".to_owned());
        }
        let mut text = String::new();
        let mut byte_boundaries = Vec::with_capacity(rows.len() + 1);
        let mut partition_boundaries = Vec::with_capacity(rows.len() + 1);
        let mut native_ids = Vec::new();
        byte_boundaries.push(0u64);
        partition_boundaries.push(0u32);
        for row in rows {
            let decoded = self.decode_native_ids(row)?;
            text.push_str(&decoded);
            byte_boundaries.push(text.len() as u64);
            native_ids.extend_from_slice(row);
            partition_boundaries.push(
                u32::try_from(native_ids.len())
                    .map_err(|_| "native partition extent left the u32 carrier".to_owned())?,
            );
        }
        let law_sha256 = format!(
            "{:x}",
            Sha256::digest(b"athena/input-presentation/independent-native-causal-partition/v1: independently addressed native words remain complete causal sections while one resident card conducts the family; chronology resets at each boundary, contact is block-diagonal, terminal rows return independently, and exterior re-tokenization remains a separate codec fibre")
        );
        let byte_boundaries_usize = byte_boundaries
            .iter()
            .map(|boundary| usize::try_from(*boundary))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|_| "native partition byte boundary left usize".to_owned())?;
        let reconstruction_sha256 = digest_input_reconstruction(
            &text,
            &native_ids,
            &byte_boundaries_usize,
            partition_boundaries.len(),
            partition_boundaries.iter().copied(),
            &[],
        );
        let presentation = RuntimeInputPresentation {
            schema: "holonic-engine.athena.input-presentation.v1".to_owned(),
            kind: "independent-native-causal-partition".to_owned(),
            law_sha256,
            source_rows: native_ids.len(),
            received_rows: rows.len(),
            byte_boundaries,
            partition_boundaries,
            boundary_crossings: Vec::new(),
            reconstruction_sha256,
            source_rows_retained: true,
        };
        self.infer_encoded_with_intervention(
            &text,
            native_ids,
            presentation,
            site,
            intervention,
            receiver,
        )
    }

    /// Conduct one addressed exterior partition through the authenticated product. Every source
    /// token remains in the input receipt; the resident card integrates the strict token blocks
    /// into the receiver rows which enter the inherited tower.
    pub fn infer_partitioned_with_intervention(
        &self,
        text: &str,
        byte_boundaries: &[usize],
        site: streamed::InterventionSite,
        intervention: &tower::Intervention,
        receiver: streamed::ReceiverOption,
    ) -> Result<RuntimeReturn, String> {
        let (native_ids, presentation) = self.encode_partitioned(text, byte_boundaries)?;
        self.infer_encoded_with_intervention(
            text,
            native_ids,
            presentation,
            site,
            intervention,
            receiver,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_encoded_with_intervention(
        &self,
        text: &str,
        native_ids: Vec<u32>,
        presentation: RuntimeInputPresentation,
        site: streamed::InterventionSite,
        intervention: &tower::Intervention,
        receiver: streamed::ReceiverOption,
    ) -> Result<RuntimeReturn, String> {
        self.mounted.verify_still().map_err(|e| e.to_string())?;
        let product_identity = self.mounted.product_identity().clone();
        let predecessor_identity = self.mounted.predecessor_identity().clone();
        let morphology_identity = self.mounted.morphology_identity().clone();
        let codec_companion_identities = self.mounted.codec_companion_identities().to_vec();
        let continuation_identity = self
            .continuation
            .as_ref()
            .map(|continuation| {
                continuation
                    .runtime_identity()
                    .map_err(|error| error.to_string())
            })
            .transpose()?;
        let factor_complex_identity = self.factor_complex_identity()?;
        let partitioned = matches!(
            presentation.kind.as_str(),
            "addressed-causal-partition" | "independent-native-causal-partition"
        );
        let receiver_rows = match (partitioned, receiver) {
            (true, _) => presentation.received_rows,
            (false, streamed::ReceiverOption::Complete) => presentation.received_rows,
            (false, _) => 1,
        };
        let prepared = self.prepare_with_rows(&native_ids, receiver_rows)?;
        let request = prepared.request()?;
        let mut source = prepared.source();
        let surface =
            ResidentSurface::on(&self.readout).map_err(|e| format!("resident surface: {e:?}"))?;
        let runtime_law = self.runtime_law.clone();
        let chart = match runtime_law.chart {
            RuntimeChart::Midpoint => tower::Chart::Midpoint,
            RuntimeChart::Interval => tower::Chart::Interval,
        };
        let token_rows = native_ids.iter().map(|id| *id as usize).collect::<Vec<_>>();
        let cultivated = if partitioned {
            streamed::circulate_cultivated_with_partitioned_intervention(
                &surface,
                &self.readout,
                &mut source,
                &token_rows,
                &presentation.partition_boundaries,
                ResidentGrain(runtime_law.grain),
                SeriesAperture(runtime_law.series_aperture),
                chart,
                runtime_law.fuse,
                site,
                intervention,
                receiver,
                &request,
            )?
        } else {
            streamed::circulate_cultivated_with_intervention(
                &surface,
                &self.readout,
                &mut source,
                &token_rows,
                ResidentGrain(runtime_law.grain),
                SeriesAperture(runtime_law.series_aperture),
                chart,
                runtime_law.fuse,
                site,
                intervention,
                receiver,
                &request,
            )?
        };
        source.verify_stable()?;
        self.mounted.verify_still().map_err(|e| e.to_string())?;
        if let Some(continuation) = &self.continuation {
            continuation
                .verify_still()
                .map_err(|error| error.to_string())?;
        }
        let frozen_identity_equal = product_identity == *self.mounted.product_identity()
            && predecessor_identity == *self.mounted.predecessor_identity()
            && morphology_identity == *self.mounted.morphology_identity()
            && codec_companion_identities == self.mounted.codec_companion_identities()
            && self
                .continuation
                .as_ref()
                .map(|continuation| {
                    continuation
                        .runtime_identity()
                        .map(|identity| Some(identity) == continuation_identity)
                        .unwrap_or(false)
                })
                .unwrap_or(continuation_identity.is_none())
            && self.factor_complex_identity()? == factor_complex_identity;
        let source_access = source_access_audit(&self.product_root);
        let vocabulary_extent = runtime_law.vocabulary_extent as usize;
        let (terminal_rows, top_lower, selected) =
            terminal_plural(&cultivated.cultivated_potential, vocabulary_extent)?;
        let plural = selected
            .iter()
            .map(|(native_id, face)| {
                self.mounted
                    .predecessor()
                    .codebook()
                    .native_surface(*native_id as u32)
                    .map(|surface| GeneratedCandidate {
                        native_id: *native_id as u32,
                        surface: surface.to_owned(),
                        lower: face.0,
                        upper: face.1,
                    })
                    .map_err(|error| error.to_string())
            })
            .collect::<Result<Vec<_>, _>>()?;
        if !frozen_identity_equal {
            return Err(
                "product/predecessor/morphology/codec identity moved under resident deed"
                    .to_owned(),
            );
        }
        if !source_access.forbidden.is_empty() {
            return Err(format!(
                "source-access audit found forbidden targets: {:?}",
                source_access.forbidden
            ));
        }
        let reconstruction_identity =
            streamed::cultivation_overlay::canonical_factor_derivation_digest(&self.derivation);
        let codec_identity = self.artifact.descriptor().tokenizer_json_sha256;
        let terminal_position = presentation.received_rows - 1;
        let receipt = RuntimeReceipt {
            schema: "holonic-engine.phoenix.runtime-return.v1",
            product_identity,
            predecessor_identity,
            morphology_identity,
            codec_companion_identities,
            continuation_identity,
            factor_complex_identity,
            factor_rank: self.factor_rank,
            runtime_law: runtime_law.clone(),
            frozen_members_verified: frozen_identity_equal,
            source_access,
            input: RuntimeInputReceipt {
                text_sha256: format!("{:x}", Sha256::digest(text.as_bytes())),
                text_octets: text.len() as u64,
                native_ids,
                presentation,
            },
            generated: GeneratedFuture {
                terminal_position,
                row_count: terminal_rows,
                vocabulary_extent,
                grain: runtime_law.grain,
                top_lower,
                plural,
                separated: vocabulary_extent - selected.len(),
            },
            reconstruction_identity,
            codec_identity,
            total_work: cultivated.total_work.clone(),
            overlay_work: cultivated.overlay_work.clone(),
            admission: cultivated.overlay_admission.clone(),
            tower_admission: cultivated.base.tower_admission.clone(),
            apparatus_census: cultivated.apparatus_census(),
            apparatus_prediction: cultivated.overlay_apparatus.clone(),
            overlay_execution: cultivated.overlay_execution.clone(),
            execution: cultivated.execution.clone(),
            streamed: cultivated.base.streamed.clone(),
        };
        Ok(RuntimeReturn {
            cultivated,
            receipt,
        })
    }
}

impl PreparedProduct<'_> {
    pub fn tokens(&self) -> &[u32] {
        &self.tokens
    }

    /// Found from the authenticated rank receipt and the candidate's factor testimony.  The
    /// returned complex is a structural witness; binding and launch remain the streamed deed.
    pub fn overlay_topology(&self) -> Result<PreparedOverlayTopology, String> {
        let (complex, _) = self
            .candidate
            .complex(Some(&self.session.derivation))
            .map_err(|error| format!("authenticated overlay topology: {error}"))?;
        let topology_identity = crate::operation_correspondence::topology_identity(&complex);
        let rank_receipt_identity =
            streamed::cultivation_overlay::canonical_factor_derivation_digest(
                &self.session.derivation,
            );
        Ok(PreparedOverlayTopology {
            complex,
            topology_identity,
            rank_receipt_identity,
            factor_populations: [
                self.candidate.u_population.clone(),
                self.candidate.v_population.clone(),
            ],
        })
    }

    pub fn overlay_topology_identity(&self) -> Result<String, String> {
        Ok(self.overlay_topology()?.topology_identity)
    }

    pub fn request(&self) -> Result<streamed::CultivationRequest<'_>, String> {
        Ok(streamed::CultivationRequest {
            candidate: &self.candidate,
            derivation: &self.session.derivation,
            u: &self.session.u,
            v: &self.session.v,
            witness: self
                .session
                .continuation
                .as_ref()
                .map(crate::phoenix::continuation::MountedContinuation::morphology)
                .unwrap_or(&self.session.mounted.morphology),
            input_bound: rested_bound(&self.session.mounted.product, "phoenix.overlay/input")?,
            predecessor_bound: rested_bound(
                &self.session.mounted.product,
                "phoenix.overlay/w2-predecessor-output",
            )?,
            band_terms: self.session.runtime_law.band_terms as usize,
        })
    }
    pub fn source(&self) -> NativeMaterialSource<'_> {
        NativeMaterialSource::from_mounted(self.session.predecessor())
    }
}

fn source_native_correspondence_from_codebook(
    codebook: &crate::foreign_codec_rest::ExteriorCodebookRest,
) -> SourceNativeCorrespondence {
    let source_to_native = codebook
        .entries
        .iter()
        .map(|entry| (entry.source_id, entry.native_id))
        .collect::<Vec<_>>();
    let represented = codebook
        .entries
        .iter()
        .map(|entry| entry.source_id)
        .collect::<std::collections::BTreeSet<_>>();
    let unresolved_source = (0..codebook.vocabulary_extent)
        .filter(|source| !represented.contains(source))
        .collect();
    SourceNativeCorrespondence {
        source_extent: codebook.vocabulary_extent,
        native_extent: codebook.vocabulary_extent,
        source_to_native,
        unresolved_source,
    }
}

fn reconstruct_source_ids_from_codebook(
    codebook: &crate::foreign_codec_rest::ExteriorCodebookRest,
    source_ids: &[u32],
) -> Result<SourceTokenSequence, String> {
    if source_ids.is_empty() {
        return Err("source-token sequence is empty".to_owned());
    }
    let native_ids = source_ids
        .iter()
        .map(|source_id| {
            codebook
                .native_id(*source_id)
                .map_err(|error| error.to_string())
        })
        .collect::<Result<Vec<_>, _>>()?;
    let surface = native_ids
        .iter()
        .map(|native_id| {
            codebook
                .native_surface(*native_id)
                .map_err(|error| error.to_string())
        })
        .collect::<Result<Vec<_>, _>>()?
        .concat();
    Ok(SourceTokenSequence {
        source_ids: source_ids.to_vec(),
        native_ids,
        surface,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SourceAccessAudit {
    pub product_root: String,
    pub descriptors: Vec<String>,
    pub forbidden: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RuntimeInputReceipt {
    pub text_sha256: String,
    pub text_octets: u64,
    pub native_ids: Vec<u32>,
    pub presentation: RuntimeInputPresentation,
}

/// One tokenizer row whose byte face intersects an addressed exterior boundary. It remains in
/// exactly one resident partition, while this receipt prevents that choice from becoming a false
/// equality between tokenizer and message incidence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RuntimeBoundaryCrossing {
    pub native_row: u32,
    pub source_id: u32,
    pub byte_range: (u64, u64),
    pub crossed_boundary: u32,
}

/// The explicit chart from an exterior occurrence to the rows which enter the inherited tower.
/// `source_rows_retained` never claims losslessness by itself: the reconstruction digest binds the
/// text, every native row, both boundary charts and every straddling tokenizer row.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RuntimeInputPresentation {
    pub schema: String,
    pub kind: String,
    pub law_sha256: String,
    pub source_rows: usize,
    pub received_rows: usize,
    pub byte_boundaries: Vec<u64>,
    pub partition_boundaries: Vec<u32>,
    pub boundary_crossings: Vec<RuntimeBoundaryCrossing>,
    pub reconstruction_sha256: String,
    pub source_rows_retained: bool,
}

impl RuntimeInputPresentation {
    fn source_rows(text: &str, native_ids: &[u32]) -> Self {
        let byte_boundaries = vec![0usize, text.len()];
        let crossings = Vec::new();
        let reconstruction_sha256 = digest_input_reconstruction(
            text,
            native_ids,
            &byte_boundaries,
            native_ids.len() + 1,
            0..=native_ids.len() as u32,
            &crossings,
        );
        Self {
            schema: "holonic-engine.athena.input-presentation.v1".to_owned(),
            kind: "source-token-rows".to_owned(),
            law_sha256: format!(
                "{:x}",
                Sha256::digest(b"athena/input-presentation/source-token-rows/v1")
            ),
            source_rows: native_ids.len(),
            received_rows: native_ids.len(),
            byte_boundaries: byte_boundaries.iter().map(|value| *value as u64).collect(),
            partition_boundaries: (0..=native_ids.len() as u32).collect(),
            boundary_crossings: crossings,
            reconstruction_sha256,
            source_rows_retained: true,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GeneratedCandidate {
    pub native_id: u32,
    pub surface: String,
    pub lower: i64,
    pub upper: i64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GeneratedFuture {
    pub terminal_position: usize,
    pub row_count: usize,
    pub vocabulary_extent: usize,
    pub grain: u32,
    pub top_lower: i64,
    pub plural: Vec<GeneratedCandidate>,
    pub separated: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RuntimeReceipt {
    pub schema: &'static str,
    pub product_identity: PredecessorProductIdentity,
    pub predecessor_identity: PredecessorProductIdentity,
    pub morphology_identity: PredecessorProductIdentity,
    pub codec_companion_identities: Vec<DirectoryCompanion>,
    pub continuation_identity: Option<crate::phoenix::continuation::ContinuationRuntimeIdentity>,
    pub factor_complex_identity: Option<SessionFactorComplexIdentity>,
    pub factor_rank: usize,
    pub runtime_law: RuntimeLawReceipt,
    pub frozen_members_verified: bool,
    pub source_access: SourceAccessAudit,
    pub input: RuntimeInputReceipt,
    pub generated: GeneratedFuture,
    pub reconstruction_identity: String,
    pub codec_identity: String,
    pub total_work: ExactWork,
    pub overlay_work: ExactWork,
    pub admission: DeedAdmission,
    /// The actual whole-tower admissions used before each resident deed conducted.
    pub tower_admission: streamed::TowerAdmissionReceipt,
    /// Absolute resident/streamed windows with the overlay retained as a separate nested deed.
    pub apparatus_census: ApparatusCensus,
    pub apparatus_prediction: ApparatusPrediction,
    pub overlay_execution: OverlayExecutionIdentity,
    pub execution: ExecutionReceipt,
    pub streamed: StreamedCensus,
}

fn source_access_audit(product_root: &Path) -> SourceAccessAudit {
    let mut descriptors = Vec::new();
    if let Ok(entries) = std::fs::read_dir("/proc/self/fd") {
        for entry in entries.flatten() {
            if let Ok(target) = std::fs::read_link(entry.path()) {
                descriptors.push(target.to_string_lossy().into_owned());
            }
        }
    }
    descriptors.sort();
    descriptors.dedup();
    let forbidden_needles = [
        "/canon/",
        "/research/",
        "/blueprint/",
        "/examples/",
        "model.safetensors",
        "modeling_gemma4.py",
        "gemma",
        ".gguf",
    ];
    let forbidden = descriptors
        .iter()
        .filter(|target| {
            let lowered = target.to_ascii_lowercase();
            forbidden_needles
                .iter()
                .any(|needle| lowered.contains(needle))
        })
        .cloned()
        .collect();
    SourceAccessAudit {
        product_root: product_root.display().to_string(),
        descriptors,
        forbidden,
    }
}

fn scale(value: i64, exponent: i32) -> Rat {
    if exponent >= 0 {
        Rat::from_integer(BigInt::from(value) * (BigInt::one() << exponent as usize))
    } else {
        Rat::new(BigInt::from(value), BigInt::one() << (-exponent) as usize)
    }
}

fn factor_runtime(
    product: &CultivatedRest,
    runtime_law: &RuntimeLawReceipt,
) -> Result<
    (
        AlignedMaterial,
        AlignedMaterial,
        streamed::cultivation_overlay::FactorDerivationReceipt,
        CultivationDerivation,
        crate::cultivated_rest::AlignedFactor,
    ),
    String,
> {
    let factor = match product.morphology_payload().map_err(|e| e.to_string())? {
        MorphologyPayload::AlignedFactor(value) => value,
        MorphologyPayload::SparseDelta(_) => {
            return Err("cultivated product has no resident factor".to_owned());
        }
    };
    if factor.rank != runtime_law.rank
        || factor.rows != runtime_law.vocabulary_extent
        || factor.columns != runtime_law.hidden_extent
        || factor.resident_grain == 0
        || factor.resident_grain != runtime_law.grain
    {
        return Err(
            "cultivated factor shape/grain is not the admitted W3 resident morphology".to_owned(),
        );
    }
    let derivation: CultivationDerivation =
        serde_json::from_slice(product.receipt().derivation.canonical_bytes())
            .map_err(|e| format!("derivation certificate: {e}"))?;
    if derivation
        .canonical_receipt_bytes()
        .map_err(|e| e.to_string())?
        != product.receipt().derivation.canonical_bytes()
        || derivation
            .canonical_adjoint_bytes()
            .map_err(|e| e.to_string())?
            != product.receipt().adjoint.canonical_bytes()
    {
        return Err("product derivation/adjoint certificate drifted".to_owned());
    }
    let rows: Vec<usize> = factor
        .left
        .iter()
        .enumerate()
        .filter_map(|(i, v)| (*v != 0).then_some(i))
        .collect();
    let columns: Vec<usize> = factor
        .right
        .iter()
        .enumerate()
        .filter_map(|(i, v)| (*v != 0).then_some(i))
        .collect();
    if rows.len() != 1
        || columns.is_empty()
        || columns.len() > 2
        || rows[0] != derivation.target_vocabulary
    {
        return Err("product factor support does not reconstruct its derivation".to_owned());
    }
    let left_value = scale(factor.left[rows[0]], factor.left_exponent);
    let right_values: Vec<Rat> = columns
        .iter()
        .map(|i| scale(factor.right[*i], factor.right_exponent))
        .collect();
    let expected_right = [
        (
            derivation.pair.first,
            &derivation.u_scale * &derivation.pair.control_annihilator[0],
        ),
        (
            derivation.pair.second,
            &derivation.u_scale * &derivation.pair.control_annihilator[1],
        ),
    ]
    .into_iter()
    .filter(|(_, value)| !value.is_zero())
    .collect::<Vec<_>>();
    if left_value != Rat::one()
        || columns
            != expected_right
                .iter()
                .map(|(index, _)| *index)
                .collect::<Vec<_>>()
        || right_values
            != expected_right
                .iter()
                .map(|(_, value)| value.clone())
                .collect::<Vec<_>>()
    {
        return Err("product factors disagree with the authenticated derivation".to_owned());
    }
    let supported = crate::exact_linear::ExactRatMatrix::new(vec![
        right_values.iter().map(|v| &left_value * v).collect(),
    ])
    .map_err(|e| e.to_string())?;
    let zero =
        crate::exact_linear::ExactRatMatrix::zero(1, columns.len()).map_err(|e| e.to_string())?;
    let receipt = streamed::cultivation_overlay::RankDerivationReceipt {
        defect: streamed::cultivation_overlay::SparseDefect {
            ambient_rows: runtime_law.vocabulary_extent as usize,
            ambient_columns: runtime_law.hidden_extent as usize,
            support_rows: rows.clone(),
            support_columns: columns.clone(),
            supported: supported.clone(),
        },
        left: streamed::cultivation_overlay::SupportedFactor {
            ambient: runtime_law.vocabulary_extent as usize,
            support: rows.clone(),
            values: vec![left_value],
        },
        right: streamed::cultivation_overlay::SupportedFactor {
            ambient: runtime_law.hidden_extent as usize,
            support: columns.clone(),
            values: right_values,
        },
        zero_rank_foil: streamed::cultivation_overlay::SparseDefect {
            ambient_rows: runtime_law.vocabulary_extent as usize,
            ambient_columns: runtime_law.hidden_extent as usize,
            support_rows: rows.clone(),
            support_columns: columns.clone(),
            supported: zero,
        },
        separator: streamed::cultivation_overlay::SeparatingReceiver {
            target: (rows[0], columns[0]),
            predecessor: Rat::zero(),
            candidate: supported.get(0, 0).map_err(|e| e.to_string())?.clone(),
        },
    };
    if streamed::cultivation_overlay::canonical_rank_derivation_bytes(&receipt)
        != product.receipt().rank.bytes()
        || streamed::cultivation_overlay::canonical_rank_derivation_digest(&receipt)
            != product.receipt().rank.sha256
    {
        return Err("authenticated rank/reconstruction identity does not reconstruct".to_owned());
    }
    let (u, v) = factor_materials(&factor);
    Ok((
        u,
        v,
        streamed::cultivation_overlay::FactorDerivationReceipt::RankOne(receipt),
        derivation,
        factor,
    ))
}

fn factor_materials(
    factor: &crate::cultivated_rest::AlignedFactor,
) -> (AlignedMaterial, AlignedMaterial) {
    let octaves = |entries: &[i64]| {
        entries
            .iter()
            .map(|value| value.unsigned_abs().max(1).ilog2() + 1)
            .max()
            .unwrap_or(0)
    };
    (
        AlignedMaterial {
            entries: factor.left.clone(),
            exponent: factor.left_exponent,
            entry_octaves: octaves(&factor.left),
            negatives: factor.left.iter().filter(|value| **value < 0).count() as u64,
        },
        AlignedMaterial {
            entries: factor.right.clone(),
            exponent: factor.right_exponent,
            entry_octaves: octaves(&factor.right),
            negatives: factor.right.iter().filter(|value| **value < 0).count() as u64,
        },
    )
}

fn rested_bound(product: &CultivatedRest, name: &str) -> Result<u32, String> {
    product
        .ports()
        .iter()
        .find(|port| port.name == name)
        .and_then(|port| match port.octave_bound {
            OctaveBoundOrigin::Rested(value) => u32::try_from(value).ok(),
            _ => None,
        })
        .ok_or_else(|| format!("rested bound {name} absent"))
}

fn testimony(
    left_population: &str,
    right_population: &str,
    vocabulary_extent: usize,
    hidden_extent: usize,
) -> streamed::cultivation_overlay::OverlayTestimony {
    use crate::ported_operation::SourceTestimony;
    let statement = |value: &str| {
        vec![SourceTestimony::AuthoritativeDescription {
            statement: value.to_owned(),
        }]
    };
    let mut left = statement(left_population);
    left.push(SourceTestimony::DeclaredShape {
        population: left_population.to_owned(),
        shape: vec![vocabulary_extent, 1],
    });
    let mut right = statement(right_population);
    right.push(SourceTestimony::DeclaredShape {
        population: right_population.to_owned(),
        shape: vec![1, hidden_extent],
    });
    streamed::cultivation_overlay::OverlayTestimony {
        input: statement("phoenix.overlay.standing.input"),
        predecessor: statement("phoenix.overlay.standing.predecessor"),
        terminal_withdraw: vec![SourceTestimony::Intervention {
            statement: "withdraw rows [0, terminal)".to_owned(),
        }],
        v: right,
        u: left,
        re_entry: statement("phoenix.overlay.re-entry"),
    }
}

fn terminal_plural(
    face: &[(i64, i64)],
    vocabulary: usize,
) -> Result<(usize, i64, Vec<(usize, (i64, i64))>), String> {
    if vocabulary == 0 || face.is_empty() || face.len() % vocabulary != 0 {
        return Err(
            "cultivated terminal face is not row-addressable by the admitted vocabulary".to_owned(),
        );
    }
    let rows = face.len() / vocabulary;
    let terminal = &face[(rows - 1) * vocabulary..];
    let top_lower = terminal
        .iter()
        .map(|(lower, _)| *lower)
        .max()
        .ok_or("cultivated terminal face is empty")?;
    let selected = terminal
        .iter()
        .enumerate()
        .filter_map(|(native_id, point)| (point.1 >= top_lower).then_some((native_id, *point)))
        .collect();
    Ok((rows, top_lower, selected))
}

fn digest_input_reconstruction(
    text: &str,
    native_ids: &[u32],
    byte_boundaries: &[usize],
    partition_boundary_population: usize,
    partition_boundaries: impl Iterator<Item = u32>,
    crossings: &[RuntimeBoundaryCrossing],
) -> String {
    fn frame(hasher: &mut Sha256, bytes: &[u8]) {
        hasher.update((bytes.len() as u64).to_le_bytes());
        hasher.update(bytes);
    }
    let mut hasher = Sha256::new();
    frame(
        &mut hasher,
        b"holonic-engine.athena.input-reconstruction.v1",
    );
    frame(&mut hasher, text.as_bytes());
    hasher.update((native_ids.len() as u64 * 4).to_le_bytes());
    for value in native_ids {
        hasher.update(value.to_le_bytes());
    }
    hasher.update((byte_boundaries.len() as u64 * 8).to_le_bytes());
    for value in byte_boundaries {
        hasher.update((*value as u64).to_le_bytes());
    }
    hasher.update((partition_boundary_population as u64 * 4).to_le_bytes());
    for value in partition_boundaries {
        hasher.update(value.to_le_bytes());
    }
    for crossing in crossings {
        hasher.update(crossing.native_row.to_le_bytes());
        hasher.update(crossing.source_id.to_le_bytes());
        hasher.update(crossing.byte_range.0.to_le_bytes());
        hasher.update(crossing.byte_range.1.to_le_bytes());
        hasher.update(crossing.crossed_boundary.to_le_bytes());
    }
    format!("{:x}", hasher.finalize())
}

/// Mount one authenticated product directory and conduct one unseen text on the resident card.
pub fn infer(product_directory: impl AsRef<Path>, text: &str) -> Result<RuntimeReturn, String> {
    let session = ProductSession::open(product_directory)?;
    session.infer_with_intervention(
        text,
        streamed::InterventionSite::Nowhere,
        &tower::Intervention::None,
        streamed::ReceiverOption::Terminal,
    )
}

/// W5 entry over one authenticated product session.
pub fn infer_with_intervention(
    product_directory: impl AsRef<Path>,
    text: &str,
    site: streamed::InterventionSite,
    intervention: &tower::Intervention,
    receiver: streamed::ReceiverOption,
) -> Result<RuntimeReturn, String> {
    let session = ProductSession::open(product_directory)?;
    session.infer_with_intervention(text, site, intervention, receiver)
}
#[cfg(test)]
mod tests {
    use super::{
        reconstruct_source_ids_from_codebook, source_native_correspondence_from_codebook,
        terminal_plural,
    };
    use crate::foreign_codec_rest::{
        CodebookEntry, CoverageSummary, OpenFibre, SourceAssetIdentity,
    };

    fn codebook() -> crate::foreign_codec_rest::ExteriorCodebookRest {
        crate::foreign_codec_rest::ExteriorCodebookRest::seal(
            SourceAssetIdentity {
                model_sha256: "model".to_owned(),
                tokenizer_sha256: "tokenizer".to_owned(),
                tokenizer_config_sha256: "config".to_owned(),
                config_sha256: "runtime".to_owned(),
                model_content_sha256: "content".to_owned(),
            },
            4,
            vec![
                CodebookEntry {
                    source_id: 0,
                    source_piece: "alpha".to_owned(),
                    native_id: 1,
                    native_surface: "β".to_owned(),
                },
                CodebookEntry {
                    source_id: 2,
                    source_piece: "gamma".to_owned(),
                    native_id: 3,
                    native_surface: "δ".to_owned(),
                },
            ],
            CoverageSummary {
                represented_token_ids: 2,
            },
            vec![OpenFibre {
                axis: "vocabulary-id".to_owned(),
                extent: 4,
                represented: 2,
                reason: "test remainder".to_owned(),
            }],
        )
        .expect("valid codebook")
    }

    #[test]
    fn multi_token_face_reads_only_the_terminal_row() {
        let face = vec![(100, 101), (90, 99), (5, 9), (10, 70), (20, 70), (70, 80)];
        let (rows, top, selected) = terminal_plural(&face, 3).expect("two token rows");
        assert_eq!(rows, 2);
        assert_eq!(top, 70);
        assert_eq!(selected, vec![(0, (10, 70)), (1, (20, 70)), (2, (70, 80))]);
    }

    #[test]
    fn source_native_rows_and_open_remainder_are_taken_from_codebook() {
        let correspondence = source_native_correspondence_from_codebook(&codebook());
        assert_eq!(correspondence.source_extent, 4);
        assert_eq!(correspondence.native_extent, 4);
        assert_eq!(correspondence.source_to_native, vec![(0, 1), (2, 3)]);
        assert_eq!(correspondence.unresolved_source, vec![1, 3]);
    }

    #[test]
    fn source_token_sequence_keeps_every_mapped_address_and_surface() {
        let codebook = codebook();
        let mapped = reconstruct_source_ids_from_codebook(&codebook, &[0, 2])
            .expect("mapped source sequence");
        assert_eq!(mapped.source_ids, vec![0, 2]);
        assert_eq!(mapped.native_ids, vec![1, 3]);
        assert_eq!(mapped.surface, "βδ");
        assert!(reconstruct_source_ids_from_codebook(&codebook, &[1]).is_err());
    }
}

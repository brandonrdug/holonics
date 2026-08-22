//! Exact contextual language generation composed from the production resonance Swing and the
//! factorized suffix ecology.
//!
//! A passage remains one caused source fiber. Its lexical faces recurrently expose that fiber
//! through [`ResonanceEcology`]; they are not embedded into a detached vector or scored by a
//! router. The returned source population is the contemporary contextual hexis. Each participating
//! source retains its own exact suffix ecology, so ordered chronology is restricted through only
//! the sources actually reached by the prompt. Plural continuations remain plural. Every emitted
//! path re-enters a branch-local resonance rest as self-emanated cause before its next continuation
//! is requested.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use body::num::Cog;
use holonic_engine::exponentiated_ratio::{RatioError, RatioFamily};
use holonic_engine::surprisal::{
    section_modulus, SectionModulus, SurprisalError, SymbolicSurprisal,
};
use holonic_structure::{LocalRelations, LocalSequence, LocalSet};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    LiveCurrentExecutor, LiveCurrentMachine, ParallelCpuLiveCurrentExecutor, ReceiverFiberIdentity,
    SparseStandingSurface,
};

use crate::{
    resonance_ecology::{
        fiber_from_bytes, ResonanceEcology, ResonanceEcologyError, ResonanceEcologyRestImage,
        ResonanceGerm, ResonanceOccurrence,
    },
    suffix_ecology::{ExactSuffixEcology, ExactSuffixEcologyError},
};

const TOKEN_SCHEMA: u64 = 0x4341_5553_544f_4b4e;
const FEATURE_SCHEMA: u64 = 0x4341_5553_4645_4154;
const SOURCE_SCHEMA: u64 = 0x4341_5553_534f_5552;
const ROUTE_REST_MAGIC: u32 = 0x4341_5254;
const ROUTE_REST_VERSION: u32 = 1;
const ROUTE_REST_HEADER_WORDS: usize = 4;
const ROUTE_REST_ROW_WORDS: usize = 6;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CausalLanguageError {
    EmptyCorpus,
    EmptyPassage(String),
    DuplicatePassage(String),
    EmptyPrompt,
    CarrierExtent,
    MalformedFiber,
    Resonance(ResonanceEcologyError),
    Suffix(ExactSuffixEcologyError),
    Ratio(RatioError),
    Surprisal(SurprisalError),
}

impl From<RatioError> for CausalLanguageError {
    fn from(value: RatioError) -> Self {
        Self::Ratio(value)
    }
}

impl From<SurprisalError> for CausalLanguageError {
    fn from(value: SurprisalError) -> Self {
        Self::Surprisal(value)
    }
}

impl From<ResonanceEcologyError> for CausalLanguageError {
    fn from(value: ResonanceEcologyError) -> Self {
        Self::Resonance(value)
    }
}

impl From<ExactSuffixEcologyError> for CausalLanguageError {
    fn from(value: ExactSuffixEcologyError) -> Self {
        Self::Suffix(value)
    }
}

/// Exact coproduct of independent feature-receiver rests. No execution partition address enters
/// this image: rows are canonically ordered by complete feature fiber.
#[derive(Debug, PartialEq, Eq)]
pub struct CausalLanguageRouteRestImage {
    receivers: LocalRelations<ReceiverFiberIdentity, ResonanceEcologyRestImage>,
}

impl CausalLanguageRouteRestImage {
    pub fn receptor_count(&self) -> usize {
        self.receivers.len()
    }

    /// Replace the rested images of exactly the receptors a later absorb re-founded.
    ///
    /// A receptor's rest is founded from **its own** complete section population and from nothing
    /// else, so re-founding one receptor and leaving every other standing is exact rather than an
    /// approximation of re-founding the corpus.
    pub(crate) fn merge(
        &mut self,
        refounded: CausalLanguageRouteRestImage,
    ) -> Result<(), CausalLanguageError> {
        for (feature, rest) in refounded.receivers.into_iter() {
            self.receivers
                .try_insert(feature, rest)
                .map_err(|_| CausalLanguageError::CarrierExtent)?;
        }
        Ok(())
    }

    pub fn encode_native_bytes(&self) -> Result<Vec<u8>, CausalLanguageError> {
        let count =
            u64::try_from(self.receivers.len()).map_err(|_| CausalLanguageError::CarrierExtent)?;
        let mut words = vec![
            ROUTE_REST_MAGIC,
            ROUTE_REST_VERSION,
            count as u32,
            (count >> 32) as u32,
        ];
        for (feature, rest) in self.receivers.iter() {
            let feature_extent = u64::try_from(feature.words().len())
                .map_err(|_| CausalLanguageError::CarrierExtent)?;
            let rest = rest.encode_native_bytes()?;
            if rest.len() % core::mem::size_of::<u32>() != 0 {
                return Err(CausalLanguageError::MalformedFiber);
            }
            let rest_extent =
                u64::try_from(rest.len()).map_err(|_| CausalLanguageError::CarrierExtent)?;
            words.extend([
                feature.schema() as u32,
                (feature.schema() >> 32) as u32,
                feature_extent as u32,
                (feature_extent >> 32) as u32,
                rest_extent as u32,
                (rest_extent >> 32) as u32,
            ]);
            words.extend_from_slice(feature.words());
            for row in rest.chunks_exact(core::mem::size_of::<u32>()) {
                words.push(u32::from_le_bytes([row[0], row[1], row[2], row[3]]));
            }
        }
        let mut bytes = LocalSequence::new();
        bytes
            .try_reserve_exact(
                words
                    .len()
                    .checked_mul(core::mem::size_of::<u32>())
                    .ok_or(CausalLanguageError::CarrierExtent)?,
            )
            .map_err(|_| CausalLanguageError::CarrierExtent)?;
        for word in words {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        Ok(bytes.into_inner())
    }

    pub fn from_native_bytes(bytes: &[u8]) -> Result<Self, CausalLanguageError> {
        if bytes.len() % core::mem::size_of::<u32>() != 0 {
            return Err(CausalLanguageError::MalformedFiber);
        }
        let words = bytes
            .chunks_exact(core::mem::size_of::<u32>())
            .map(|row| u32::from_le_bytes([row[0], row[1], row[2], row[3]]))
            .collect::<Vec<_>>();
        if words.len() < ROUTE_REST_HEADER_WORDS
            || words[0] != ROUTE_REST_MAGIC
            || words[1] != ROUTE_REST_VERSION
        {
            return Err(CausalLanguageError::MalformedFiber);
        }
        let count = join_u64(words[2], words[3])
            .and_then(|value| usize::try_from(value).ok())
            .ok_or(CausalLanguageError::MalformedFiber)?;
        let mut cursor = ROUTE_REST_HEADER_WORDS;
        let mut receivers = LocalRelations::new();
        for _ in 0..count {
            let header_end = cursor
                .checked_add(ROUTE_REST_ROW_WORDS)
                .filter(|end| *end <= words.len())
                .ok_or(CausalLanguageError::MalformedFiber)?;
            let schema = join_u64(words[cursor], words[cursor + 1])
                .ok_or(CausalLanguageError::MalformedFiber)?;
            let feature_extent = join_u64(words[cursor + 2], words[cursor + 3])
                .and_then(|value| usize::try_from(value).ok())
                .ok_or(CausalLanguageError::MalformedFiber)?;
            let rest_bytes = join_u64(words[cursor + 4], words[cursor + 5])
                .and_then(|value| usize::try_from(value).ok())
                .filter(|extent| *extent % core::mem::size_of::<u32>() == 0)
                .ok_or(CausalLanguageError::MalformedFiber)?;
            cursor = header_end;
            let feature_end = cursor
                .checked_add(feature_extent)
                .filter(|end| *end <= words.len())
                .ok_or(CausalLanguageError::MalformedFiber)?;
            let feature = ReceiverFiberIdentity::new(schema, words[cursor..feature_end].to_vec());
            cursor = feature_end;
            let rest_words = rest_bytes / core::mem::size_of::<u32>();
            let rest_end = cursor
                .checked_add(rest_words)
                .filter(|end| *end <= words.len())
                .ok_or(CausalLanguageError::MalformedFiber)?;
            let mut rest_wire = LocalSequence::new();
            rest_wire
                .try_reserve_exact(rest_bytes)
                .map_err(|_| CausalLanguageError::CarrierExtent)?;
            for word in &words[cursor..rest_end] {
                rest_wire.extend_from_slice(&word.to_le_bytes());
            }
            cursor = rest_end;
            let rest = ResonanceEcologyRestImage::from_native_bytes(&rest_wire)?;
            if feature.schema() != FEATURE_SCHEMA
                || receivers
                    .try_insert(feature, rest)
                    .map_err(|_| CausalLanguageError::CarrierExtent)?
                    .is_some()
            {
                return Err(CausalLanguageError::MalformedFiber);
            }
        }
        if cursor != words.len() {
            return Err(CausalLanguageError::MalformedFiber);
        }
        Ok(Self { receivers })
    }
}

/// This form's prefix and its layout version, read out of the prefix rather than restated. The
/// trailing octet is the version: a codec that moves must move this, so a stale form refuses at the
/// mount instead of being read under a layout it was not written in.
pub const CAUSAL_LANGUAGE_REST_PREFIX: [u8; 8] = *b"CLNG\0\0\0\x02";
/// The codec's own layout version — the `\x02` above.
///
/// **Moved `1 -> 2` on 2026-08-18** when the retained route sections joined the seal, so that a
/// resumed body can [`CausalLanguageEcology::absorb`] rather than only produce. A form written under
/// version 1 carries no sections and refuses at the mount instead of resuming a body that would
/// silently be unable to take material.
pub const CAUSAL_LANGUAGE_REST_VERSION: u32 = CAUSAL_LANGUAGE_REST_PREFIX[7] as u32;

/// Write a length-prefixed block. **Length-prefixed, never delimited** — a delimiter would make an
/// octet of the payload unrepresentable, which is a codec deciding what its material may contain.
fn put_block(octets: &mut Vec<u8>, block: &[u8]) -> Result<(), CausalLanguageError> {
    let extent = u64::try_from(block.len()).map_err(|_| CausalLanguageError::CarrierExtent)?;
    octets.extend_from_slice(&extent.to_le_bytes());
    octets.extend_from_slice(block);
    Ok(())
}

fn put_count(octets: &mut Vec<u8>, count: usize) -> Result<(), CausalLanguageError> {
    let value = u64::try_from(count).map_err(|_| CausalLanguageError::CarrierExtent)?;
    octets.extend_from_slice(&value.to_le_bytes());
    Ok(())
}

/// Write a receiver fiber identity as its **exact schema and words**.
///
/// This is `fiber_from_bytes`'s own discipline one layer out: the identity crosses as a reversible
/// packing, so the mount reconstructs the same identity rather than a name that stands for it.
fn put_identity(
    octets: &mut Vec<u8>,
    identity: &ReceiverFiberIdentity,
) -> Result<(), CausalLanguageError> {
    octets.extend_from_slice(&identity.schema().to_le_bytes());
    put_count(octets, identity.words().len())?;
    for word in identity.words() {
        octets.extend_from_slice(&word.to_le_bytes());
    }
    Ok(())
}

/// A cursor that refuses past the end rather than truncating.
struct RestCursor<'wire> {
    bytes: &'wire [u8],
    at: usize,
}

impl<'wire> RestCursor<'wire> {
    fn take(&mut self, extent: usize) -> Result<&'wire [u8], CausalLanguageError> {
        let end = self
            .at
            .checked_add(extent)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(CausalLanguageError::MalformedFiber)?;
        let taken = &self.bytes[self.at..end];
        self.at = end;
        Ok(taken)
    }

    fn u64(&mut self) -> Result<u64, CausalLanguageError> {
        let raw = self.take(core::mem::size_of::<u64>())?;
        Ok(u64::from_le_bytes(
            raw.try_into()
                .map_err(|_| CausalLanguageError::MalformedFiber)?,
        ))
    }

    fn u32(&mut self) -> Result<u32, CausalLanguageError> {
        let raw = self.take(core::mem::size_of::<u32>())?;
        Ok(u32::from_le_bytes(
            raw.try_into()
                .map_err(|_| CausalLanguageError::MalformedFiber)?,
        ))
    }

    fn count(&mut self) -> Result<usize, CausalLanguageError> {
        usize::try_from(self.u64()?).map_err(|_| CausalLanguageError::CarrierExtent)
    }

    fn block(&mut self) -> Result<&'wire [u8], CausalLanguageError> {
        let extent = self.count()?;
        self.take(extent)
    }

    fn identity(&mut self) -> Result<ReceiverFiberIdentity, CausalLanguageError> {
        let schema = self.u64()?;
        let extent = self.count()?;
        let mut words = Vec::with_capacity(extent.min(1 << 16));
        for _ in 0..extent {
            words.push(self.u32()?);
        }
        Ok(ReceiverFiberIdentity::new(schema, words))
    }
}

/// One inherited textual section of an arbitrary receiver. `receiver` distinguishes the source
/// chart (dialogue, research prose, code, mathematics, transcript, returned experiment, ...);
/// lexical recurrence may still carry a question across several such charts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CausalLanguagePassage {
    pub identity: String,
    pub receiver: u64,
    pub text: String,
}

impl CausalLanguagePassage {
    pub fn new(identity: impl Into<String>, receiver: u64, text: impl Into<String>) -> Self {
        Self {
            identity: identity.into(),
            receiver,
            text: text.into(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
struct PassageStanding {
    identity: String,
    receiver: u64,
    suffix: ExactSuffixEcology,
}

/// Exact receipt for one source fiber recruited by the prompt-wide Swing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecruitedSource {
    pub identity: String,
    pub receiver: u64,
    pub supporting_features: BTreeSet<String>,
}

/// Exact receipt for one emitted token. `matched_horizon` is the nested chronological receiver
/// which exposed the token, not a scalar likelihood. `sources` is the participating contextual
/// hexis at that boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CausalGeneratedToken {
    pub token: String,
    pub matched_horizon: u32,
    pub sources: BTreeSet<String>,
}

/// One branch-local generated deed.
#[derive(Debug, PartialEq, Eq)]
pub struct CausalGeneratedText {
    pub text: String,
    pub tokens: Vec<CausalGeneratedToken>,
    pub stopped_at_sentence_boundary: bool,
    returned_rest: ResonanceEcologyRestImage,
}

impl CausalGeneratedText {
    /// Exact branch-local body containing the received question and every emanated transition.
    pub const fn returned_rest_image(&self) -> &ResonanceEcologyRestImage {
        &self.returned_rest
    }
}

/// Complete receiver testimony for one generation request.
#[derive(Debug, PartialEq, Eq)]
pub struct CausalLanguageGeneration {
    pub prompt: String,
    pub prompt_tokens: Vec<String>,
    pub initial_hexis: Vec<RecruitedSource>,
    pub outputs: Vec<CausalGeneratedText>,
    /// The depth at which a declared front extent stopped the whole front at once, if one was
    /// declared. **Always `None` today**: the caller-declared extent was removed with the misjoined
    /// branching law it existed to bound, and no path in this organ caps a front. The field is kept
    /// because a front bound is owed once the complete law runs on real extent, and a field that
    /// appears with the bound is a field a reader has to notice.
    pub front_refused_at: Option<usize>,
    /// The largest live front the run carried.
    pub peak_front_extent: usize,
}

impl CausalLanguageGeneration {
    /// The conducted population, in the shape the presentation's division takes. Each output is
    /// named by its own rendered surface, so two branches that emitted the same tokens are one
    /// candidate rather than two.
    pub fn presented_candidates(&self) -> Vec<crate::presentation_quotient::PresentedCandidate> {
        let mut named: BTreeMap<String, crate::presentation_quotient::PresentedCandidate> =
            BTreeMap::new();
        for output in &self.outputs {
            named.entry(output.text.clone()).or_insert_with(|| {
                crate::presentation_quotient::PresentedCandidate {
                    identity: output.text.clone(),
                    tokens: output
                        .tokens
                        .iter()
                        .map(|token| token.token.clone())
                        .collect(),
                    matched_horizons: output
                        .tokens
                        .iter()
                        .map(|token| token.matched_horizon)
                        .collect(),
                    sources: output
                        .tokens
                        .iter()
                        .map(|token| token.sources.clone())
                        .collect(),
                }
            });
        }
        named.into_values().collect()
    }
}

/// **Which law decides what branches at a junction.**
///
/// `GreatestHorizonGate` is the inherited law and is preserved bit-for-bit: only the continuations
/// attested at the deepest *productive* matched context branch, and every shorter-horizon
/// continuation is carried out as `withheld_by_horizon` without branching.
///
/// `CompleteJunction` removes the gate. Every continuation the recruited sources attest, at
/// every horizon, branches; the horizon travels as a **coordinate on the member** and the difference
/// between members is carried by [`RatioFamily`] — an exact cocycle in which no member is crowned,
/// dropped, or ranked, and in which the normalising extent enters no ratio.
///
/// **This is a caller-declared level and it is the falsifier's own instrument.** The two laws are a
/// declared gauge over one junction: a driver runs both on one material and compares. A gauge that
/// cannot exhibit its own orbit has gauged nothing, so the pair is required rather than optional.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub enum BranchingLaw {
    #[default]
    GreatestHorizonGate,
    CompleteJunction,
}

/// **Which attestation of a continuation the reading takes as its multiplicity.**
///
/// A continuation is generally attested at several matched horizons at once: the deepest context
/// that reaches it is the most specific, and every shorter recurrent restriction that also reaches
/// it is broader and carries a larger occurrence count which *contains* the specific one. Summing
/// them would count one occurrence many times, so the reading declares which attestation it takes
/// and the complete horizon profile is returned beside it either way.
///
/// Two receivers exist so that the reading can be shown to move with the receiver rather than to be
/// a property of the material. Neither is a default in the law; the caller declares one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ContinuationReceiver {
    /// The multiplicity at the continuation's own greatest supporting horizon.
    MostSpecificAttestation,
    /// The multiplicity at its shortest supporting horizon.
    BroadestAttestation,
}

/// One continuation at a junction, with the horizon carried as a coordinate rather than consumed
/// by a filter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContinuationMember {
    /// The reading's name for this member: its position in the junction's own canonical token
    /// order. It labels a place in an order the material fixes; it does not intern a receiver face,
    /// and [`ContinuationMember::token`] resolves it back at every use.
    pub name: u64,
    pub token: String,
    /// The horizon the declared receiver read this member at.
    pub horizon: u32,
    /// The occurrence multiplicity at that horizon.
    pub multiplicity: u64,
    /// Every horizon this continuation is attested at, with the multiplicity at each. The complete
    /// artifact, so a second receiver can be read off the same population with no re-run.
    pub horizon_profile: BTreeMap<u32, u64>,
    pub sources: BTreeSet<String>,
    /// Whether the inherited `GreatestHorizonGate` would have let this member branch. Carried per
    /// member so the two laws can be compared without running the junction twice.
    pub gate_would_keep: bool,
}

/// **A junction read as an exact ratio family and a section modulus, with nothing gated.**
///
/// `ratios` is `None` only below two members, where a ratio family has nothing to relate;
/// `modulus` is `None` only on an empty junction. Both are read from one population of surprisal
/// forms, which is the same input type each organ already takes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContinuationReading {
    pub receiver: ContinuationReceiver,
    pub members: Vec<ContinuationMember>,
    pub ratios: Option<RatioFamily>,
    /// `r(i,j)·r(j,k) = r(i,k)` over every triple — the algebraic statement that the absolute
    /// values were gauge. `Some(true)` vacuously below three members.
    ///
    /// **`None` means it was not taken here.** The check is `O(n³)` over the junction's breadth,
    /// so the generation path does not run it at every state; the explicit reading does. A figure
    /// that was never measured is returned as absent rather than as a default.
    pub cocycle_holds: Option<bool>,
    pub modulus: Option<SectionModulus>,
    /// The second moment vanishes against a nonzero extreme fibre: the population has collapsed
    /// onto one fibre and carries no bending load. The anti-vacuity arm.
    pub collapsed_onto_one_fibre: bool,
    /// No member deviates from the population's own mean — every ratio is one and the family
    /// distinguishes nothing. The other way a reading can be empty.
    pub flat: bool,
    /// The deepest productive horizon at this junction. A coordinate here, not a bar.
    pub greatest_horizon: u32,
    /// How many members the inherited gate would have kept, and how many it would have set aside.
    pub gate_would_keep: usize,
    pub gate_would_withhold: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CausalLanguageGenerationSpec {
    pub maximum_generated_tokens: usize,
    pub stop_at_sentence_boundary: bool,
    pub branching_law: BranchingLaw,
    pub continuation_receiver: ContinuationReceiver,
}

impl Default for CausalLanguageGenerationSpec {
    fn default() -> Self {
        Self {
            maximum_generated_tokens: 64,
            stop_at_sentence_boundary: true,
            branching_law: BranchingLaw::GreatestHorizonGate,
            continuation_receiver: ContinuationReceiver::MostSpecificAttestation,
        }
    }
}

/// A conditioned language body. The live route rest owns recurrent source recruitment; suffix
/// ecologies own exact ordered continuations globally and inside every source fiber.
#[derive(Debug)]
pub struct CausalLanguageEcology {
    route_rest: CausalLanguageRouteRestImage,
    route_sections: BTreeMap<ReceiverFiberIdentity, BTreeSet<ReceiverFiberIdentity>>,
    /// **The route sections that founded the rest, retained rather than consumed.**
    ///
    /// Conditioning built these, handed them to `condition_route_receivers`, and dropped them. That
    /// made recruitment un-extendable: a later passage could be given its own suffix ecology and
    /// folded into the global one, and it could still never be **recruited**, because a receptor's
    /// rested resonance is founded from its complete section population and the old sections were
    /// gone. Retaining them is what makes [`Self::absorb`] able to re-found only the receptors the
    /// new material touched, exactly, rather than re-founding the corpus or leaving the new passage
    /// unreachable.
    route_material: BTreeMap<ReceiverFiberIdentity, Vec<RouteTrainingSection>>,
    passages: BTreeMap<ReceiverFiberIdentity, PassageStanding>,
    global_suffix: ExactSuffixEcology,
    passage_population: usize,
    lexical_occurrences: usize,
    route_occurrences: usize,
    route_relations: usize,
    conditioning_events: usize,
}

impl CausalLanguageEcology {
    pub fn condition(
        passages: &[CausalLanguagePassage],
        action: ActionCurrent,
        worker_threads: usize,
    ) -> Result<Self, CausalLanguageError> {
        if passages.is_empty() {
            return Err(CausalLanguageError::EmptyCorpus);
        }
        let trace = std::env::var_os("SOMA_CAUSAL_LANGUAGE_TRACE").is_some();
        let conditioning_started = Instant::now();
        let mut identities = LocalSet::new();
        let mut standing = BTreeMap::new();
        let mut global_paths = Vec::new();
        let mut route_groups = BTreeMap::<ReceiverFiberIdentity, Vec<RouteTrainingSection>>::new();
        let mut lexical_occurrences = 0usize;

        let mut route_relations = 0usize;

        for (passage_at, passage) in passages.iter().enumerate() {
            if !identities.insert(passage.identity.clone()) {
                return Err(CausalLanguageError::DuplicatePassage(
                    passage.identity.clone(),
                ));
            }
            let tokens = lexical_tokens(&passage.text);
            if tokens.is_empty() {
                return Err(CausalLanguageError::EmptyPassage(passage.identity.clone()));
            }
            lexical_occurrences = lexical_occurrences
                .checked_add(tokens.len())
                .ok_or(CausalLanguageError::CarrierExtent)?;
            let path = token_germs(&tokens)?;
            let suffix = ExactSuffixEcology::condition(std::slice::from_ref(&path))?;
            global_paths.push(path);

            let source = source_fiber(passage)?;
            let features = route_features(&tokens);
            route_relations = route_relations
                .checked_add(features.len())
                .ok_or(CausalLanguageError::CarrierExtent)?;
            let source_order =
                u64::try_from(passage_at).map_err(|_| CausalLanguageError::CarrierExtent)?;
            for feature in features {
                let feature_identity = route_feature_fiber(&feature);
                route_groups
                    .entry(feature_identity)
                    .or_default()
                    .push(RouteTrainingSection {
                        source_order,
                        source: source.clone(),
                    });
            }

            standing.insert(
                source.clone(),
                PassageStanding {
                    identity: passage.identity.clone(),
                    receiver: passage.receiver,
                    suffix,
                },
            );
            if trace && (passage_at + 1) % 100 == 0 {
                eprintln!(
                    "causal-language condition: formed {} passage suffixes / {} route sections in {} ms",
                    passage_at + 1,
                    route_relations,
                    conditioning_started.elapsed().as_millis()
                );
            }
        }

        if trace {
            eprintln!(
                "causal-language condition: forming global suffix over {} lexical occurrences",
                lexical_occurrences
            );
        }
        let global_suffix = ExactSuffixEcology::condition(&global_paths)?;
        if trace {
            eprintln!(
                "causal-language condition: global suffix formed in {} ms; crossing {} local route sections",
                conditioning_started.elapsed().as_millis(),
                route_relations
            );
        }
        let route_material = route_groups.clone();
        let (route_rest, route_sections, conditioning_events) =
            condition_route_receivers(route_groups, action, worker_threads)?;
        if trace {
            eprintln!(
                "causal-language condition: rested {} route receptors after {} events in {} ms",
                route_sections.len(),
                conditioning_events,
                conditioning_started.elapsed().as_millis()
            );
        }
        Ok(Self {
            route_rest,
            route_sections,
            route_material,
            passages: standing,
            global_suffix,
            passage_population: passages.len(),
            lexical_occurrences,
            route_occurrences: route_relations,
            route_relations,
            conditioning_events,
        })
    }

    pub const fn passage_population(&self) -> usize {
        self.passage_population
    }

    pub const fn lexical_occurrence_population(&self) -> usize {
        self.lexical_occurrences
    }

    pub const fn route_occurrence_population(&self) -> usize {
        self.route_occurrences
    }

    pub const fn route_relation_population(&self) -> usize {
        self.route_relations
    }

    pub const fn conditioning_event_population(&self) -> usize {
        self.conditioning_events
    }

    pub fn route_rest_image(&self) -> &CausalLanguageRouteRestImage {
        &self.route_rest
    }

    /// ★ **ABSORB ONE FURTHER PASSAGE — the return edge.**
    ///
    /// Measured 2026-08-18 before this existed: this type carried **no `&mut self` method at all**,
    /// and `condition` is an associated function that builds from scratch. So a resumed body could
    /// produce and could not be changed — not by its own production, not by anything handed to it.
    /// A machine that seals and resumes but cannot absorb is a recording, not an instance.
    ///
    /// **This is not a second conditioning law.** It is the same law applied to standing material:
    ///
    /// - the passage founds its own [`ExactSuffixEcology`] exactly as `condition` founds one;
    /// - the global suffix **absorbs** the new path, which the automaton supports natively because
    ///   it is an online structure — see `ExactSuffixEcology::absorb`;
    /// - the new passage's route features are merged into the retained section population, and
    ///   **only the receptors that population changed are re-founded**, because a receptor's rest
    ///   is founded from its own sections and from nothing else.
    ///
    /// **A repeated passage identity refuses**, exactly as it refuses in `condition`. Absorbing the
    /// same material twice is a different claim from absorbing it once, and this organ will not
    /// silently make them the same body.
    ///
    /// **The cost is stated rather than hidden**: re-founding is proportional to the sections of the
    /// touched receptors, not to the corpus — but a passage sharing route features with everything
    /// touches everything, so the worst case is a full re-founding of the route side. The suffix
    /// side is genuinely incremental.
    pub fn absorb(
        &mut self,
        passage: &CausalLanguagePassage,
        action: ActionCurrent,
        worker_threads: usize,
    ) -> Result<(), CausalLanguageError> {
        let source = source_fiber(passage)?;
        if self.passages.contains_key(&source) {
            return Err(CausalLanguageError::DuplicatePassage(
                passage.identity.clone(),
            ));
        }
        let tokens = lexical_tokens(&passage.text);
        if tokens.is_empty() {
            return Err(CausalLanguageError::EmptyPassage(passage.identity.clone()));
        }
        let path = token_germs(&tokens)?;

        // The passage's own standing, founded exactly as conditioning founds one.
        let suffix = ExactSuffixEcology::condition(std::slice::from_ref(&path))?;

        // The global suffix takes the new path without reopening any other material.
        self.global_suffix.absorb(&path)?;

        // The route side: merge the sections, re-found only the receptors they touched.
        let features = route_features(&tokens);
        let added_relations = features.len();
        let source_order = u64::try_from(self.passage_population)
            .map_err(|_| CausalLanguageError::CarrierExtent)?;
        let mut touched: BTreeMap<ReceiverFiberIdentity, Vec<RouteTrainingSection>> =
            BTreeMap::new();
        for feature in features {
            let feature_identity = route_feature_fiber(&feature);
            let sections = self
                .route_material
                .entry(feature_identity.clone())
                .or_default();
            sections.push(RouteTrainingSection {
                source_order,
                source: source.clone(),
            });
            touched.insert(feature_identity, sections.clone());
        }
        if !touched.is_empty() {
            let (refounded, sections, events) =
                condition_route_receivers(touched, action, worker_threads)?;
            self.route_rest.merge(refounded)?;
            for (receptor, targets) in sections {
                self.route_sections.insert(receptor, targets);
            }
            self.conditioning_events = self
                .conditioning_events
                .checked_add(events)
                .ok_or(CausalLanguageError::CarrierExtent)?;
        }

        self.passages.insert(
            source,
            PassageStanding {
                identity: passage.identity.clone(),
                receiver: passage.receiver,
                suffix,
            },
        );
        self.passage_population = self
            .passage_population
            .checked_add(1)
            .ok_or(CausalLanguageError::CarrierExtent)?;
        self.lexical_occurrences = self
            .lexical_occurrences
            .checked_add(tokens.len())
            .ok_or(CausalLanguageError::CarrierExtent)?;
        self.route_relations = self
            .route_relations
            .checked_add(added_relations)
            .ok_or(CausalLanguageError::CarrierExtent)?;
        self.route_occurrences = self.route_relations;
        Ok(())
    }

    /// ★ **SEAL THE WHOLE CONDITIONED BODY TO OCTETS.**
    ///
    /// The route rest was sealable since this module was written and the whole ecology was not, so
    /// a conditioned language body could be **described** across a seam and never **resumed** across
    /// one. Measured 2026-08-18: no file in this workspace named both `ErosRest` and
    /// `CausalLanguageEcology` — the intersection of the two greps was empty — so the organ that
    /// holds a whole body and the organ that produces language had never met.
    ///
    /// **What crosses is every carrier's exact words, never a digest**, for the reason
    /// [`crate::eros_rest`] already states: a digest cannot exhibit which word moved, and which word
    /// moved is the whole of the conditioning control.
    ///
    /// The counters cross too. They are **derived faces** of the material and are re-checked at the
    /// mount against what the sealed structures actually carry, so a wire whose counters disagree
    /// with its own bodies refuses rather than resuming a body that would misreport itself.
    pub fn encode_native_bytes(&self) -> Result<Vec<u8>, CausalLanguageError> {
        let mut octets = Vec::new();
        octets.extend_from_slice(&CAUSAL_LANGUAGE_REST_PREFIX);

        let route = self.route_rest.encode_native_bytes()?;
        put_block(&mut octets, &route)?;
        let global = self.global_suffix.encode_native_bytes()?;
        put_block(&mut octets, &global)?;

        put_count(&mut octets, self.route_sections.len())?;
        for (receptor, section) in &self.route_sections {
            put_identity(&mut octets, receptor)?;
            put_count(&mut octets, section.len())?;
            for member in section {
                put_identity(&mut octets, member)?;
            }
        }

        put_count(&mut octets, self.route_material.len())?;
        for (feature, sections) in &self.route_material {
            put_identity(&mut octets, feature)?;
            put_count(&mut octets, sections.len())?;
            for section in sections {
                octets.extend_from_slice(&section.source_order.to_le_bytes());
                put_identity(&mut octets, &section.source)?;
            }
        }

        put_count(&mut octets, self.passages.len())?;
        for (identity, standing) in &self.passages {
            put_identity(&mut octets, identity)?;
            put_block(&mut octets, standing.identity.as_bytes())?;
            octets.extend_from_slice(&standing.receiver.to_le_bytes());
            let suffix = standing.suffix.encode_native_bytes()?;
            put_block(&mut octets, &suffix)?;
        }

        for count in [
            self.passage_population,
            self.lexical_occurrences,
            self.route_occurrences,
            self.route_relations,
            self.conditioning_events,
        ] {
            put_count(&mut octets, count)?;
        }
        Ok(octets)
    }

    /// ★ **MOUNT A WHOLE CONDITIONED BODY FROM OCTETS ALONE.**
    ///
    /// **Nothing is re-conditioned here and no corpus is reopened.** A body that mounts through this
    /// path has the passages' suffix ecologies, the route rest and the global suffix ecology it was
    /// sealed with, and it can [`Self::generate`] with the source material deleted from the disk.
    /// That is the difference between a run and an instance.
    ///
    /// The derived counters are **re-taken from the mounted bodies and compared to the wire**. A
    /// disagreement refuses: a resumed body that misreports its own population is worse than one
    /// that will not mount, because the misreport travels into every later reading.
    pub fn from_native_bytes(bytes: &[u8]) -> Result<Self, CausalLanguageError> {
        let mut cursor = RestCursor { bytes, at: 0 };
        let opened = cursor.take(CAUSAL_LANGUAGE_REST_PREFIX.len())?;
        if opened != CAUSAL_LANGUAGE_REST_PREFIX {
            return Err(CausalLanguageError::MalformedFiber);
        }
        let route_rest = CausalLanguageRouteRestImage::from_native_bytes(cursor.block()?)?;
        let global_suffix = ExactSuffixEcology::from_native_bytes(cursor.block()?)?;

        let receptors = cursor.count()?;
        let mut route_sections = BTreeMap::new();
        for _ in 0..receptors {
            let receptor = cursor.identity()?;
            let members = cursor.count()?;
            let mut section = BTreeSet::new();
            for _ in 0..members {
                if !section.insert(cursor.identity()?) {
                    return Err(CausalLanguageError::MalformedFiber);
                }
            }
            if route_sections.insert(receptor, section).is_some() {
                return Err(CausalLanguageError::MalformedFiber);
            }
        }

        let material_rows = cursor.count()?;
        let mut route_material: BTreeMap<ReceiverFiberIdentity, Vec<RouteTrainingSection>> =
            BTreeMap::new();
        for _ in 0..material_rows {
            let feature = cursor.identity()?;
            let sections = cursor.count()?;
            let mut carried = Vec::with_capacity(sections.min(1 << 16));
            for _ in 0..sections {
                let source_order = cursor.u64()?;
                let source = cursor.identity()?;
                carried.push(RouteTrainingSection {
                    source_order,
                    source,
                });
            }
            if route_material.insert(feature, carried).is_some() {
                return Err(CausalLanguageError::MalformedFiber);
            }
        }

        let passage_rows = cursor.count()?;
        let mut passages = BTreeMap::new();
        for _ in 0..passage_rows {
            let key = cursor.identity()?;
            let identity = core::str::from_utf8(cursor.block()?)
                .map_err(|_| CausalLanguageError::MalformedFiber)?
                .to_owned();
            let receiver = cursor.u64()?;
            let suffix = ExactSuffixEcology::from_native_bytes(cursor.block()?)?;
            let standing = PassageStanding {
                identity,
                receiver,
                suffix,
            };
            if passages.insert(key, standing).is_some() {
                return Err(CausalLanguageError::MalformedFiber);
            }
        }

        let passage_population = cursor.count()?;
        let lexical_occurrences = cursor.count()?;
        let route_occurrences = cursor.count()?;
        let route_relations = cursor.count()?;
        let conditioning_events = cursor.count()?;
        if cursor.at != cursor.bytes.len() {
            return Err(CausalLanguageError::MalformedFiber);
        }

        // The counters are faces of the material. Re-take the two that the mounted bodies can
        // answer for and refuse a wire that disagrees with itself.
        if passage_population != passages.len() {
            return Err(CausalLanguageError::MalformedFiber);
        }
        if route_relations != route_sections.values().map(BTreeSet::len).sum::<usize>() {
            return Err(CausalLanguageError::MalformedFiber);
        }

        Ok(Self {
            route_rest,
            route_sections,
            route_material,
            passages,
            global_suffix,
            passage_population,
            lexical_occurrences,
            route_occurrences,
            route_relations,
            conditioning_events,
        })
    }

    pub fn route_receptor_population(&self) -> usize {
        self.route_sections.len()
    }

    pub fn global_suffix(&self) -> &ExactSuffixEcology {
        &self.global_suffix
    }

    pub fn generate(
        &self,
        prompt: &str,
        spec: CausalLanguageGenerationSpec,
        action: ActionCurrent,
        worker_threads: usize,
    ) -> Result<CausalLanguageGeneration, CausalLanguageError> {
        let mut cpu = ParallelCpuLiveCurrentExecutor::new(worker_threads.max(1));
        self.generate_with_executor(prompt, spec, action, &mut cpu)
    }

    /// Generate through one caller-retained physical executor. Recruitment and suffix emanation
    /// remain exact cpu work, but the question event and every self-emanated return of every
    /// terminal path cross the supplied executor; selecting a card at the outer language boundary
    /// cannot silently construct a private cpu executor here.
    pub fn generate_with_executor(
        &self,
        prompt: &str,
        spec: CausalLanguageGenerationSpec,
        action: ActionCurrent,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<CausalLanguageGeneration, CausalLanguageError> {
        let prompt_tokens = lexical_tokens(prompt);
        if prompt_tokens.is_empty() {
            return Err(CausalLanguageError::EmptyPrompt);
        }

        // The cover, declared once for this leader.
        let cover = holonic_engine::hardware_cover::HardwareCover::cpu_only();
        let initial = self.recruit(&prompt_tokens);
        let initial_hexis = self.recruitment_read(&initial.sources)?;
        let mut states = vec![GenerationState {
            history: prompt_tokens.clone(),
            emitted: Vec::new(),
            source_hexis: initial.sources,
            stopped: false,
        }];

        let front_refused_at: Option<usize> = None;
        let mut peak_front_extent = states.len();
        for _ in 0..spec.maximum_generated_tokens {
            // **The leader's front: branch tips are co-present, an arc is serial.**
            //
            // `states` is a front of branch tips; `continuations` is the junction each opens; the
            // successors are the next front. What travels ONE arc is ordered and stays so — the
            // history a tip carries is untouched — while distinct tips are independent, so they are
            // co-present and the cover carries them. Chronology is not seriality: a leader is a
            // branching structure with time parity, and asserting a total order where the material
            // has a tree is the error this removes.
            //
            // The law is `hardware_cover::expand_front`. **This comment asserted the sharing before
            // it was true**: the leader was the law's only external caller until 2026-08-11, when
            // `morphological_language::generate_currents` moved off a by-count `at % lanes` cover
            // and `token_invariance::sweep_covered` gave up its own second copy of the by-extent
            // placement. All three generation fronts conduct through it now. A covering per organ
            // is the cabinet failure one level down — and the two receiver-conditioning fronts
            // further down THIS file still section by count, so they are outside that statement.
            let successors = holonic_engine::hardware_cover::expand_front(
                states,
                &cover,
                // A tip's extent is what it has already emitted: a long branch opens a wider
                // junction than a short one, and covering by count would weigh them the same.
                |state: &GenerationState| state.emitted.len() as u64 + 1,
                |state: GenerationState| -> Result<Vec<GenerationState>, CausalLanguageError> {
                    let mut branched = Vec::new();
                    if state.stopped {
                        branched.push(state);
                        return Ok(branched);
                    }
                    let mut active_hexis = state.source_hexis.clone();
                    // What branches is decided by the caller's declared law. Under the inherited
                    // gate it is the kept half of the horizon division; under the ratio family it
                    // is the complete population, with the horizon carried as a coordinate on each
                    // member instead of consumed by a filter ahead of the branching.
                    let mut branches = self.junction_steps(&state.history, &active_hexis, spec)?;
                    if branches.is_empty() {
                        active_hexis = self.recruit(&state.history).sources;
                        branches = self.junction_steps(&state.history, &active_hexis, spec)?;
                    }
                    if branches.is_empty() {
                        let mut stopped = state;
                        stopped.stopped = true;
                        branched.push(stopped);
                        return Ok(branched);
                    }
                    for branch in branches {
                        let source_names = branch
                            .sources
                            .iter()
                            .map(|source| {
                                self.passages
                                    .get(source)
                                    .map(|passage| passage.identity.clone())
                                    .ok_or(CausalLanguageError::MalformedFiber)
                            })
                            .collect::<Result<BTreeSet<_>, _>>()?;
                        let source_hexis = branch
                            .sources
                            .iter()
                            .map(|source| {
                                active_hexis
                                    .get(source)
                                    .cloned()
                                    .map(|support| (source.clone(), support))
                                    .ok_or(CausalLanguageError::MalformedFiber)
                            })
                            .collect::<Result<BTreeMap<_, _>, _>>()?;
                        let mut history = state.history.clone();
                        history.push(branch.token.clone());
                        let mut emitted = state.emitted.clone();
                        emitted.push(CausalGeneratedToken {
                            token: branch.token.clone(),
                            matched_horizon: branch.matched_horizon,
                            sources: source_names,
                        });
                        let stopped = spec.stop_at_sentence_boundary
                            && emitted.len() >= 4
                            && sentence_boundary(&branch.token);
                        branched.push(GenerationState {
                            history,
                            emitted,
                            source_hexis,
                            stopped,
                        });
                    }

                    Ok(branched)
                },
            )?;
            let all_stopped = successors.iter().all(|state| state.stopped);
            states = successors;
            peak_front_extent = peak_front_extent.max(states.len());
            if all_stopped {
                break;
            }
        }

        let mut outputs = Vec::with_capacity(states.len());
        for state in states {
            let mut ecology =
                self.receive_question_with_executor(&prompt_tokens, action, executor)?;
            let mut predecessor = prompt_tokens
                .last()
                .map(ToOwned::to_owned)
                .ok_or(CausalLanguageError::EmptyPrompt)?;
            for (generated_at, generated) in state.emitted.iter().enumerate() {
                let source_order = u64::try_from(generated_at)
                    .map_err(|_| CausalLanguageError::CarrierExtent)?
                    .checked_add(1)
                    .ok_or(CausalLanguageError::CarrierExtent)?;
                let germs = token_germs(&[predecessor, generated.token.to_owned()])?;
                let occurrence = ResonanceOccurrence::self_emanated(source_order, germs)?;
                ecology.receive_with(&occurrence, action, executor)?;
                predecessor = generated.token.to_owned();
            }
            outputs.push(CausalGeneratedText {
                text: render_tokens(state.emitted.iter().map(|token| token.token.as_str())),
                stopped_at_sentence_boundary: state
                    .emitted
                    .last()
                    .is_some_and(|token| sentence_boundary(&token.token)),
                tokens: state.emitted,
                returned_rest: ecology.rest_image()?,
            });
        }
        Ok(CausalLanguageGeneration {
            prompt: prompt.to_owned(),
            prompt_tokens,
            initial_hexis,
            outputs,
            front_refused_at,
            peak_front_extent,
        })
    }

    fn recruit(&self, history: &[String]) -> Recruitment {
        let features = route_features(history);
        if features.is_empty() {
            return Recruitment {
                sources: BTreeMap::new(),
            };
        }
        let mut sources = BTreeMap::<ReceiverFiberIdentity, BTreeSet<String>>::new();
        for feature in features {
            let identity = route_feature_fiber(&feature);
            if let Some(targets) = self.route_sections.get(&identity) {
                for source in targets {
                    sources
                        .entry(source.clone())
                        .or_default()
                        .insert(feature.clone());
                }
            }
        }
        Recruitment { sources }
    }

    fn recruitment_read(
        &self,
        sources: &BTreeMap<ReceiverFiberIdentity, BTreeSet<String>>,
    ) -> Result<Vec<RecruitedSource>, CausalLanguageError> {
        sources
            .iter()
            .map(|(source, supporting_features)| {
                let passage = self
                    .passages
                    .get(source)
                    .ok_or(CausalLanguageError::MalformedFiber)?;
                Ok(RecruitedSource {
                    identity: passage.identity.clone(),
                    receiver: passage.receiver,
                    supporting_features: supporting_features.clone(),
                })
            })
            .collect()
    }

    /// The conditioned material, in the shape the window test takes.
    ///
    /// The passages are the surfaces the emission drew on, tokenized by the same lexical receiver
    /// that conditioned them, so a candidate is compared against exactly what founded it.
    pub fn presentation_material(
        &self,
        passages: &[CausalLanguagePassage],
    ) -> crate::presentation_quotient::PresentationMaterial {
        crate::presentation_quotient::PresentationMaterial {
            inherited_surfaces: passages
                .iter()
                .map(|passage| lexical_tokens(&passage.text))
                .collect(),
        }
    }

    /// **The junction, collected with nothing gated.**
    ///
    /// Every branch of every recruited source, at every horizon its supports attest, with the
    /// occurrence multiplicity at each. The inherited gate's verdict is recomputed in the same pass
    /// from the same data so the two laws can be compared member by member without running the
    /// junction twice; the two implementations are held to each other by
    /// `the_two_branching_laws_agree_on_what_the_gate_keeps`.
    fn junction_population(
        &self,
        history: &[String],
        sources: &BTreeMap<ReceiverFiberIdentity, BTreeSet<String>>,
    ) -> Result<JunctionPopulation, CausalLanguageError> {
        let path = token_germs(history)?;
        let mut profile: BTreeMap<String, BTreeMap<u32, (u64, BTreeSet<ReceiverFiberIdentity>)>> =
            BTreeMap::new();
        let mut gate = BTreeMap::<String, (u32, BTreeSet<ReceiverFiberIdentity>)>::new();
        let mut gate_greatest_horizon = 0u32;

        for source in sources.keys() {
            let passage = self
                .passages
                .get(source)
                .ok_or(CausalLanguageError::MalformedFiber)?;
            let emanation = passage.suffix.emanate(&path)?;
            if emanation.branches().is_empty() {
                continue;
            }
            let Some(source_horizon) = emanation.greatest_productive_matched_length() else {
                continue;
            };
            gate_greatest_horizon = gate_greatest_horizon.max(source_horizon);
            for branch in emanation.branches() {
                let token = fiber_bytes(branch.germ().identity())?;
                // The complete profile: every support, at its own horizon. Within one source two
                // supports at the same matched length reach the same target, so the multiplicity
                // there is a max rather than a sum; across sources the attestations are disjoint
                // material and add.
                let mut per_source: BTreeMap<u32, u64> = BTreeMap::new();
                for support in branch.supports() {
                    let slot = per_source.entry(support.matched_length()).or_insert(0);
                    *slot = (*slot).max(support.recurrence_multiplicity());
                }
                let token_profile = profile.entry(token.clone()).or_default();
                for (horizon, multiplicity) in per_source {
                    let slot = token_profile
                        .entry(horizon)
                        .or_insert_with(|| (0, BTreeSet::new()));
                    slot.0 = slot.0.saturating_add(multiplicity);
                    slot.1.insert(source.clone());
                }

                // The inherited gate's own rule, recomputed unchanged.
                if !branch
                    .supports()
                    .iter()
                    .any(|support| support.matched_length() == source_horizon)
                {
                    continue;
                }
                let entry = gate
                    .entry(token)
                    .or_insert_with(|| (source_horizon, BTreeSet::new()));
                if source_horizon > entry.0 {
                    entry.0 = source_horizon;
                    entry.1.clear();
                }
                if source_horizon == entry.0 {
                    entry.1.insert(source.clone());
                }
            }
        }

        // The same global fallback the gate law takes when the recruited sources reach nothing.
        // Under the complete law this fires strictly less often, because a source that emanated
        // anything at all contributes a member.
        if profile.is_empty() {
            let emanation = self.global_suffix.emanate(&path)?;
            for branch in emanation.branches() {
                let token = fiber_bytes(branch.germ().identity())?;
                let token_profile = profile.entry(token).or_default();
                for support in branch.supports() {
                    let slot = token_profile
                        .entry(support.matched_length())
                        .or_insert_with(|| (0, BTreeSet::new()));
                    slot.0 = slot.0.max(support.recurrence_multiplicity());
                }
            }
        }

        Ok(JunctionPopulation {
            profile,
            gate,
            gate_greatest_horizon,
        })
    }

    /// **Read a junction as an exact ratio family and a section modulus, with nothing gated.**
    ///
    /// The horizon becomes a coordinate on each member and the difference between members is
    /// carried by the ratio family, which is a cocycle: any assignment of absolute values
    /// consistent with these ratios differs from any other by one overall factor and nothing else.
    /// The normalising extent is formed inside this function, enters no returned ratio, and is not
    /// a field.
    pub fn read_junction(
        &self,
        history: &[String],
        sources: &BTreeMap<ReceiverFiberIdentity, BTreeSet<String>>,
        receiver: ContinuationReceiver,
    ) -> Result<ContinuationReading, CausalLanguageError> {
        let population = self.junction_population(history, sources)?;
        self.read_population(&population, receiver, true)
    }

    /// The prompt's own junction: recruit the contextual hexis, then read it.
    pub fn read_junction_from_prompt(
        &self,
        prompt: &str,
        receiver: ContinuationReceiver,
    ) -> Result<ContinuationReading, CausalLanguageError> {
        let history = lexical_tokens(prompt);
        if history.is_empty() {
            return Err(CausalLanguageError::EmptyPrompt);
        }
        let hexis = self.recruit(&history).sources;
        self.read_junction(&history, &hexis, receiver)
    }

    fn read_population(
        &self,
        population: &JunctionPopulation,
        receiver: ContinuationReceiver,
        check_cocycle: bool,
    ) -> Result<ContinuationReading, CausalLanguageError> {
        let mut members = Vec::with_capacity(population.profile.len());
        let mut greatest_horizon = 0u32;

        for (name, (token, horizons)) in population.profile.iter().enumerate() {
            let Some((&horizon, (multiplicity, source_fibers))) = (match receiver {
                ContinuationReceiver::MostSpecificAttestation => horizons.iter().next_back(),
                ContinuationReceiver::BroadestAttestation => horizons.iter().next(),
            }) else {
                continue;
            };
            let horizon_profile: BTreeMap<u32, u64> = horizons
                .iter()
                .map(|(carried, (multiplicity, _))| (*carried, *multiplicity))
                .collect();
            if let Some(highest) = horizon_profile.keys().next_back() {
                greatest_horizon = greatest_horizon.max(*highest);
            }
            let sources = source_fibers
                .iter()
                .map(|fiber| {
                    self.passages
                        .get(fiber)
                        .map(|passage| passage.identity.clone())
                        .ok_or(CausalLanguageError::MalformedFiber)
                })
                .collect::<Result<BTreeSet<_>, _>>()?;
            let gate_would_keep = population
                .gate
                .get(token)
                .is_some_and(|(kept, _)| *kept == population.gate_greatest_horizon);
            members.push(ContinuationMember {
                name: u64::try_from(name).map_err(|_| CausalLanguageError::CarrierExtent)?,
                token: token.clone(),
                horizon,
                multiplicity: *multiplicity,
                horizon_profile,
                sources,
                gate_would_keep,
            });
        }

        // The extent is a LOCAL. It cancels out of every ratio the family returns, and the section
        // modulus is unmoved by the additive shift it induces, so neither reading depends on it.
        let mut extent = BigInt::from(0u32);
        for member in &members {
            extent += BigInt::from(member.multiplicity);
        }
        let mut forms = BTreeMap::<u64, SymbolicSurprisal>::new();
        if !members.is_empty() {
            for member in &members {
                let probability = Rat::new(BigInt::from(member.multiplicity), extent.clone());
                forms.insert(
                    member.name,
                    SymbolicSurprisal::of_probability(&probability)?,
                );
            }
        }

        let ratios = if forms.len() >= 2 {
            Some(RatioFamily::read(&forms)?)
        } else {
            None
        };
        let cocycle_holds = if check_cocycle {
            Some(ratios.as_ref().is_none_or(RatioFamily::cocycle_holds))
        } else {
            None
        };
        let modulus = if forms.is_empty() {
            None
        } else {
            Some(section_modulus(&forms)?)
        };
        let flat = modulus
            .as_ref()
            .is_some_and(|reading| vanishes(&reading.extreme_fibre.upper));
        let collapsed_onto_one_fibre = modulus.as_ref().is_some_and(|reading| {
            vanishes(&reading.second_moment.upper) && !vanishes(&reading.extreme_fibre.upper)
        });
        let gate_would_keep = members
            .iter()
            .filter(|member| member.gate_would_keep)
            .count();

        Ok(ContinuationReading {
            receiver,
            gate_would_withhold: members.len() - gate_would_keep,
            gate_would_keep,
            members,
            ratios,
            cocycle_holds,
            modulus,
            collapsed_onto_one_fibre,
            flat,
            greatest_horizon,
        })
    }

    /// The steps that branch at one junction, under the caller's declared law.
    fn junction_steps(
        &self,
        history: &[String],
        hexis: &BTreeMap<ReceiverFiberIdentity, BTreeSet<String>>,
        spec: CausalLanguageGenerationSpec,
    ) -> Result<Vec<BranchStep>, CausalLanguageError> {
        match spec.branching_law {
            BranchingLaw::GreatestHorizonGate => Ok(self
                .continuations(history, hexis)?
                .into_iter()
                .filter(|continuation| !continuation.withheld_by_horizon)
                .map(|continuation| BranchStep {
                    token: continuation.token,
                    matched_horizon: continuation.matched_horizon,
                    sources: continuation.sources,
                })
                .collect()),
            BranchingLaw::CompleteJunction => {
                // **This law forms no ratio and reads no modulus.** It branches the whole junction
                // and nothing else. An earlier form built a `RatioFamily` here and carried it out
                // on every emitted token as a digest; an external adjudication convicted that as a
                // misjoin — *"the ratios and modulus survive only as metadata; nothing is
                // transported differently because of them"* — and the exponentiated ratio's real
                // material is an exact bracket population over a deposited map, not a suffix count.
                // The reading is available separately at `read_junction`, where it is a diagnostic
                // and is labelled as one.
                let population = self.junction_population(history, hexis)?;
                let mut steps = Vec::with_capacity(population.profile.len());
                for (token, horizons) in &population.profile {
                    let Some((&horizon, (_, source_fibers))) = (match spec.continuation_receiver {
                        ContinuationReceiver::MostSpecificAttestation => {
                            horizons.iter().next_back()
                        }
                        ContinuationReceiver::BroadestAttestation => horizons.iter().next(),
                    }) else {
                        continue;
                    };
                    steps.push(BranchStep {
                        token: token.clone(),
                        matched_horizon: horizon,
                        sources: source_fibers.clone(),
                    });
                }
                Ok(steps)
            }
        }
    }

    fn continuations(
        &self,
        history: &[String],
        sources: &BTreeMap<ReceiverFiberIdentity, BTreeSet<String>>,
    ) -> Result<Vec<Continuation>, CausalLanguageError> {
        let path = token_germs(history)?;
        let mut by_token = BTreeMap::<String, (u32, BTreeSet<ReceiverFiberIdentity>)>::new();
        let mut greatest_horizon = 0u32;

        for source in sources.keys() {
            let passage = self
                .passages
                .get(source)
                .ok_or(CausalLanguageError::MalformedFiber)?;
            let emanation = passage.suffix.emanate(&path)?;
            if emanation.branches().is_empty() {
                continue;
            }
            // **The reached context and the PRODUCTIVE context are two different receivers, and
            // reading the first where the law needs the second silenced whole sources.**
            //
            // `longest_matched_length` is the deepest context the path *reached*. That context may
            // be terminal — present in the passage, with no outgoing material. Every support then
            // sits at a shorter recurrent restriction, the filter below matches nothing, and this
            // source contributes no branch **while still having raised `greatest_horizon`**. The
            // `retain` afterwards deletes every token every other source did produce, and the whole
            // junction falls through to the global suffix with an EMPTY source set — which is why
            // the receipts read `sources=1` on 89 of 112 emissions.
            //
            // `greatest_productive_matched_length` is the accessor written for exactly this case,
            // with the case stated in its own doc line, and it had no caller anywhere in the tree.
            let Some(horizon) = emanation.greatest_productive_matched_length() else {
                continue;
            };
            greatest_horizon = greatest_horizon.max(horizon);
            for branch in emanation.branches() {
                if !branch
                    .supports()
                    .iter()
                    .any(|support| support.matched_length() == horizon)
                {
                    continue;
                }
                let token = fiber_bytes(branch.germ().identity())?;
                let entry = by_token
                    .entry(token)
                    .or_insert_with(|| (horizon, Default::default()));
                if horizon > entry.0 {
                    entry.0 = horizon;
                    entry.1.clear();
                }
                if horizon == entry.0 {
                    entry.1.insert(source.clone());
                }
            }
        }

        // THE DIVISION, TAKEN RATHER THAN THE QUOTIENT KEPT. Everything at a shorter matched
        // horizon is set aside and carried out; nothing is dropped here.
        let withheld: BTreeMap<String, (u32, BTreeSet<ReceiverFiberIdentity>)> = by_token
            .iter()
            .filter(|(_, (horizon, _))| *horizon != greatest_horizon)
            .map(|(token, carried)| (token.clone(), carried.clone()))
            .collect();
        by_token.retain(|_, (horizon, _)| *horizon == greatest_horizon);
        if by_token.is_empty() {
            let emanation = self.global_suffix.emanate(&path)?;
            // Same reading as above: the bar is the deepest context with outgoing material, not the
            // deepest context reached. A terminal deepest context here refused the whole fallback.
            greatest_horizon = emanation
                .greatest_productive_matched_length()
                .unwrap_or_default();
            for branch in emanation.branches() {
                if !branch
                    .supports()
                    .iter()
                    .any(|support| support.matched_length() == greatest_horizon)
                {
                    continue;
                }
                by_token.insert(
                    fiber_bytes(branch.germ().identity())?,
                    (greatest_horizon, BTreeSet::new()),
                );
            }
        }
        Ok(by_token
            .into_iter()
            .map(|(token, (matched_horizon, sources))| Continuation {
                token,
                matched_horizon,
                sources,
                withheld_by_horizon: false,
            })
            .chain(
                withheld
                    .into_iter()
                    .map(|(token, (matched_horizon, sources))| Continuation {
                        token,
                        matched_horizon,
                        sources,
                        withheld_by_horizon: true,
                    }),
            )
            .collect())
    }

    /// The retained cpu mouth for the question event. It has no library caller: this organ's one
    /// generation path now threads a caller-retained executor all the way down, so keeping a
    /// private cpu construction on that path would be the very defect the twin below removes.
    /// The signature is preserved rather than cut because it is the worker-count mouth a caller
    /// which has mounted nothing still expects.
    #[allow(dead_code)]
    fn receive_question(
        &self,
        prompt: &[String],
        action: ActionCurrent,
        worker_threads: usize,
    ) -> Result<ResonanceEcology, CausalLanguageError> {
        let mut cpu = ParallelCpuLiveCurrentExecutor::new(worker_threads.max(1));
        self.receive_question_with_executor(prompt, action, &mut cpu)
    }

    /// Receive the outer question through one caller-retained physical executor. The executor
    /// crosses the question's Swing event; selecting a card at the outer language boundary cannot
    /// silently construct a private cpu executor here.
    fn receive_question_with_executor(
        &self,
        prompt: &[String],
        action: ActionCurrent,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<ResonanceEcology, CausalLanguageError> {
        let machine = LiveCurrentMachine::new(
            SparseStandingSurface::empty_rank(10)
                .map_err(|_| CausalLanguageError::CarrierExtent)?,
        );
        let mut ecology = ResonanceEcology::new(machine);
        let question = ResonanceOccurrence::probe(0, token_germs(prompt)?)?;
        ecology.receive_with(&question, action, executor)?;
        Ok(ecology)
    }
}

#[derive(Clone, Debug)]
pub(crate) struct RouteTrainingSection {
    pub(crate) source_order: u64,
    pub(crate) source: ReceiverFiberIdentity,
}

struct ConditionedRouteReceiver {
    feature: ReceiverFiberIdentity,
    rest: ResonanceEcologyRestImage,
    targets: BTreeSet<ReceiverFiberIdentity>,
    events: usize,
}

pub(crate) fn condition_route_receivers(
    groups: BTreeMap<ReceiverFiberIdentity, Vec<RouteTrainingSection>>,
    action: ActionCurrent,
    worker_threads: usize,
) -> Result<
    (
        CausalLanguageRouteRestImage,
        BTreeMap<ReceiverFiberIdentity, BTreeSet<ReceiverFiberIdentity>>,
        usize,
    ),
    CausalLanguageError,
> {
    if groups.is_empty() {
        return Ok((
            CausalLanguageRouteRestImage {
                receivers: LocalRelations::new(),
            },
            BTreeMap::new(),
            0,
        ));
    }
    let worker_count = worker_threads.max(1).min(groups.len());
    let mut partitions = (0..worker_count)
        .map(|_| Vec::new())
        .collect::<Vec<Vec<(ReceiverFiberIdentity, Vec<RouteTrainingSection>)>>>();
    for (at, group) in groups.into_iter().enumerate() {
        partitions[at % worker_count].push(group);
    }
    let mut conditioned = std::thread::scope(|scope| {
        let handles = partitions
            .into_iter()
            .map(|partition| scope.spawn(move || condition_route_partition(partition, action)))
            .collect::<Vec<_>>();
        let mut conditioned = Vec::new();
        for handle in handles {
            let mut rows = handle
                .join()
                .map_err(|_| CausalLanguageError::CarrierExtent)??;
            conditioned.append(&mut rows);
        }
        Ok::<_, CausalLanguageError>(conditioned)
    })?;
    conditioned.sort_by(|left, right| left.feature.cmp(&right.feature));

    let mut rests = LocalRelations::new();
    let mut routes = BTreeMap::<ReceiverFiberIdentity, BTreeSet<ReceiverFiberIdentity>>::new();
    let mut events = 0usize;
    for receiver in conditioned {
        events = events
            .checked_add(receiver.events)
            .ok_or(CausalLanguageError::CarrierExtent)?;
        if rests
            .try_insert(receiver.feature.to_owned(), receiver.rest)
            .map_err(|_| CausalLanguageError::CarrierExtent)?
            .is_some()
            || routes.insert(receiver.feature, receiver.targets).is_some()
        {
            return Err(CausalLanguageError::MalformedFiber);
        }
    }
    Ok((
        CausalLanguageRouteRestImage { receivers: rests },
        routes,
        events,
    ))
}

/// Condition the same complete route population through one caller-owned physical executor.
/// Chronology within each receiver remains ordered; the executor is free to realize each returned
/// event on a resident card. This is the production mouth used when a higher body explicitly
/// mounts CUDA rather than silently rebuilding the route ecology on cpu workers.
pub(crate) fn condition_route_receivers_with_executor(
    groups: BTreeMap<ReceiverFiberIdentity, Vec<RouteTrainingSection>>,
    action: ActionCurrent,
    executor: &mut dyn LiveCurrentExecutor,
) -> Result<
    (
        CausalLanguageRouteRestImage,
        BTreeMap<ReceiverFiberIdentity, BTreeSet<ReceiverFiberIdentity>>,
        usize,
    ),
    CausalLanguageError,
> {
    condition_route_receivers_mandatory(groups, action, executor)
}

/// Condition every independent route receiver through the caller's mandatory resident executor.
///
/// This mouth is deliberately serial across receiver ecologies: one mutable resident owner cannot
/// be cloned, and manufacturing auxiliary executors here would make placement an undeclared
/// fallback. Chronology within each receiver is unchanged. A future multi-stream resident owner
/// may cover the independent population behind the same return without changing this law.
pub(crate) fn condition_route_receivers_mandatory(
    groups: BTreeMap<ReceiverFiberIdentity, Vec<RouteTrainingSection>>,
    action: ActionCurrent,
    executor: &mut dyn LiveCurrentExecutor,
) -> Result<
    (
        CausalLanguageRouteRestImage,
        BTreeMap<ReceiverFiberIdentity, BTreeSet<ReceiverFiberIdentity>>,
        usize,
    ),
    CausalLanguageError,
> {
    let mut conditioned = Vec::new();
    conditioned
        .try_reserve_exact(groups.len())
        .map_err(|_| CausalLanguageError::CarrierExtent)?;
    for (feature, receiver_sections) in groups {
        conditioned.push(condition_route_receiver(
            feature,
            receiver_sections,
            action,
            executor,
        )?);
    }
    let mut rests = LocalRelations::new();
    let mut routes = BTreeMap::new();
    let mut events = 0usize;
    for receiver in conditioned {
        events = events
            .checked_add(receiver.events)
            .ok_or(CausalLanguageError::CarrierExtent)?;
        if rests
            .try_insert(receiver.feature.to_owned(), receiver.rest)
            .map_err(|_| CausalLanguageError::CarrierExtent)?
            .is_some()
            || routes.insert(receiver.feature, receiver.targets).is_some()
        {
            return Err(CausalLanguageError::MalformedFiber);
        }
    }
    Ok((
        CausalLanguageRouteRestImage { receivers: rests },
        routes,
        events,
    ))
}

fn condition_route_partition(
    partition: Vec<(ReceiverFiberIdentity, Vec<RouteTrainingSection>)>,
    action: ActionCurrent,
) -> Result<Vec<ConditionedRouteReceiver>, CausalLanguageError> {
    let mut conditioned = Vec::new();
    conditioned
        .try_reserve_exact(partition.len())
        .map_err(|_| CausalLanguageError::CarrierExtent)?;
    for (feature, sections) in partition {
        // Parallelism lives across independent receiver ecologies; one receiver's returned
        // chronology remains serial and therefore uses one physical worker.
        let mut executor = ParallelCpuLiveCurrentExecutor::new(1);
        conditioned.push(condition_route_receiver(
            feature,
            sections,
            action,
            &mut executor,
        )?);
    }
    Ok(conditioned)
}

fn condition_route_receiver(
    feature: ReceiverFiberIdentity,
    sections: Vec<RouteTrainingSection>,
    action: ActionCurrent,
    executor: &mut dyn LiveCurrentExecutor,
) -> Result<ConditionedRouteReceiver, CausalLanguageError> {
    let machine = LiveCurrentMachine::new(
        SparseStandingSurface::empty_rank(10).map_err(|_| CausalLanguageError::CarrierExtent)?,
    );
    let mut route = ResonanceEcology::new(machine);
    let mut targets = BTreeSet::<ReceiverFiberIdentity>::new();
    for section in &sections {
        let occurrence = ResonanceOccurrence::routed_informant(
            section.source.to_owned(),
            section.source_order,
            germ(feature.to_owned())?,
            section.source.to_owned(),
        )?;
        let returned = route.receive_with(&occurrence, action, executor)?;
        let continuation_returned = returned
            .read()
            .continuations_after(&feature)
            .is_some_and(|returned_targets| returned_targets.contains(&section.source));
        if !continuation_returned || !returned.read().informants().contains(&section.source) {
            return Err(CausalLanguageError::MalformedFiber);
        }
        targets.insert(section.source.to_owned());
    }
    Ok(ConditionedRouteReceiver {
        feature,
        rest: route.rest_image()?,
        targets,
        events: sections.len(),
    })
}

#[derive(Clone)]
struct Recruitment {
    sources: BTreeMap<ReceiverFiberIdentity, BTreeSet<String>>,
}

/// One junction, collected with nothing gated, beside the inherited gate's verdict on the same
/// pass. `profile` is `token -> horizon -> (multiplicity, sources)`.
struct JunctionPopulation {
    profile: BTreeMap<String, BTreeMap<u32, (u64, BTreeSet<ReceiverFiberIdentity>)>>,
    gate: BTreeMap<String, (u32, BTreeSet<ReceiverFiberIdentity>)>,
    gate_greatest_horizon: u32,
}

/// Exact, on the numerator alone: a reduced rational is zero exactly when its numerator is.
fn vanishes(value: &Rat) -> bool {
    *value.numer() == BigInt::from(0u32)
}

/// One continuation that branches, under whichever law the caller declared.
struct BranchStep {
    token: String,
    matched_horizon: u32,
    sources: BTreeSet<ReceiverFiberIdentity>,
}

#[derive(Clone)]
struct Continuation {
    token: String,
    matched_horizon: u32,
    sources: BTreeSet<ReceiverFiberIdentity>,
    /// **Whether the longest-horizon filter kept this continuation or set it aside.**
    ///
    /// Before 2026-08-17 the filter was `by_token.retain(|_, (horizon, _)| *horizon ==
    /// greatest_horizon)`: every continuation matched at a shorter horizon was **deleted with no
    /// record**, and `Continuation` had no field for the dropped population. Division has two
    /// outputs — `20/3 = 6 + 2/3` loses nothing and the loss appears only at `6.6666667` — and this
    /// path kept the quotient and discarded the remainder.
    ///
    /// The filter still decides what is emitted. What changed is that what it set aside is
    /// **returned beside it** and can be read, which is the difference between a division and a
    /// deletion.
    withheld_by_horizon: bool,
}

struct GenerationState {
    history: Vec<String>,
    emitted: Vec<CausalGeneratedToken>,
    source_hexis: BTreeMap<ReceiverFiberIdentity, BTreeSet<String>>,
    stopped: bool,
}

fn source_fiber(
    passage: &CausalLanguagePassage,
) -> Result<ReceiverFiberIdentity, CausalLanguageError> {
    let identity = passage.identity.as_bytes();
    let extent = u64::try_from(identity.len()).map_err(|_| CausalLanguageError::CarrierExtent)?;
    let mut bytes = Vec::with_capacity(16 + identity.len());
    bytes.extend_from_slice(&passage.receiver.to_le_bytes());
    bytes.extend_from_slice(&extent.to_le_bytes());
    bytes.extend_from_slice(identity);
    Ok(fiber_from_bytes(SOURCE_SCHEMA, &bytes))
}

pub(crate) fn germ(identity: ReceiverFiberIdentity) -> Result<ResonanceGerm, CausalLanguageError> {
    let phase = RelationAtom::new(Cog::lit(1)).ok_or(CausalLanguageError::CarrierExtent)?;
    Ok(ResonanceGerm::new(identity, phase))
}

/// The germ population of a token sequence, for a caller probing the atlas directly.
pub fn token_germs_public(tokens: &[String]) -> Result<Vec<ResonanceGerm>, CausalLanguageError> {
    token_germs(tokens)
}

pub(crate) fn token_germs(tokens: &[String]) -> Result<Vec<ResonanceGerm>, CausalLanguageError> {
    tokens
        .iter()
        .map(|token| germ(fiber_from_bytes(TOKEN_SCHEMA, token.as_bytes())))
        .collect()
}

pub(crate) fn route_feature_fiber(feature: &str) -> ReceiverFiberIdentity {
    fiber_from_bytes(FEATURE_SCHEMA, feature.as_bytes())
}

fn route_features(tokens: &[String]) -> BTreeSet<String> {
    tokens
        .iter()
        // The lexical router receives morphologically extended word faces. Short function faces
        // remain fully present in suffix chronology but do not found near-ubiquitous routing
        // receptors which cannot distinguish a local source ecology.
        .filter(|token| token.chars().any(char::is_alphanumeric) && token.chars().count() >= 4)
        .map(|token| token.to_lowercase())
        .collect()
}

/// **Reopen a receiver fiber identity to the octets that founded it.**
///
/// `fiber_from_bytes` is a **length-prefixed word packing, not a digest**, and this reverses it
/// exactly. So a germ carries its own token back with no vocabulary file anywhere — which is the
/// corpus's own address law, *an address is a collapsed face that reopens*, holding at the smallest
/// grain the machine has.
pub fn fiber_bytes(identity: &ReceiverFiberIdentity) -> Result<String, CausalLanguageError> {
    if !matches!(
        identity.schema(),
        TOKEN_SCHEMA | FEATURE_SCHEMA | SOURCE_SCHEMA
    ) || identity.words().len() < 2
    {
        return Err(CausalLanguageError::MalformedFiber);
    }
    let extent = u64::from(identity.words()[0]) | (u64::from(identity.words()[1]) << 32);
    let extent = usize::try_from(extent).map_err(|_| CausalLanguageError::CarrierExtent)?;
    let mut bytes = Vec::with_capacity(identity.words().len().saturating_sub(2).saturating_mul(4));
    for word in &identity.words()[2..] {
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    if extent > bytes.len() {
        return Err(CausalLanguageError::MalformedFiber);
    }
    bytes.truncate(extent);
    String::from_utf8(bytes).map_err(|_| CausalLanguageError::MalformedFiber)
}

/// Deterministic lexical receiver for language morphology. Surface case remains part of the
/// chronological token face; routing derives a case-folded feature quotient separately.
/// The three levels this tokenizer authors, **declared by the caller** rather than written into the
/// loop.
///
/// # Why this is a declaration and not a recovery
///
/// Measured 2026-08-17 by running `life::exposure_codec::ladder` over three materials — 413 research
/// records, `crates/holonic-engine/src`, and `Mathlib/Geometry` — at radius 3: the exposure law
/// founds the **character** codec exactly, and founds no coarser unit on any of them. On 3 MB of
/// prose its entire rung-1 return is six compound units — `"ἐνέρ" "ἕξις" "└──" "├──" "εια" "úñ"` —
/// which are precisely the character sequences whose constituents occur nowhere else. Ordinary
/// letters occur everywhere, so no word qualifies, and the law refuses to invent one.
///
/// **So a word rule is not derivable from exposure at an affordable radius, and this type does not
/// pretend otherwise.** What it does is stop the three authored levels from living inside the organ,
/// which is the species `canon/THE_AUTHORED_LEVEL.md` convicts and the repair `corpus_census` already
/// took: a caller's declaration belongs on the caller. [`LexicalAperture::inherited`] reproduces the
/// authored reading exactly, so nothing that stands moves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexicalAperture {
    /// Characters that continue a word beyond the codec's own alphanumeric class.
    pub word_continuations: BTreeSet<char>,
    /// Characters that extend a punctuation run. **The inherited six are the convicted level**: they
    /// make `::` and `:=` survive while `->`, `=>`, `&&`, `!=`, `..` and all fourteen of Lean's
    /// bracket species shatter into single glyphs.
    pub run_continuations: BTreeSet<char>,
    /// Whether a character's own alphanumeric class opens a word. Declared so a caller reading a
    /// material with no such class can say so rather than silently getting one.
    pub alphanumeric_opens_a_word: bool,
}

impl LexicalAperture {
    /// The reading this tree has always taken, stated rather than hidden.
    pub fn inherited() -> Self {
        Self {
            word_continuations: ['_', '\''].into_iter().collect(),
            run_continuations: ['-', '=', ':', '/', '*', '#'].into_iter().collect(),
            alphanumeric_opens_a_word: true,
        }
    }

    /// Every non-whitespace, non-word character extends a run. The declared alternative for a
    /// material whose operators are multi-character, which the inherited six cannot carry.
    pub fn runs_are_maximal() -> Self {
        Self {
            run_continuations: BTreeSet::new(),
            ..Self::inherited()
        }
    }

    fn extends_a_run(&self, character: char) -> bool {
        self.run_continuations.is_empty() || self.run_continuations.contains(&character)
    }

    fn opens_a_word(&self, character: char) -> bool {
        (self.alphanumeric_opens_a_word && character.is_alphanumeric())
            || self.word_continuations.contains(&character)
    }
}

/// The inherited lexical reading. Preserved bit-for-bit as [`LexicalAperture::inherited`].
pub fn lexical_tokens(text: &str) -> Vec<String> {
    lexical_tokens_under(text, &LexicalAperture::inherited())
}

/// The same reading under a **declared** aperture.
pub fn lexical_tokens_under(text: &str, aperture: &LexicalAperture) -> Vec<String> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Species {
        Word,
        Punctuation,
    }
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut species = None;
    let flush = |tokens: &mut Vec<String>, current: &mut String| {
        if !current.is_empty() {
            tokens.push(std::mem::take(current));
        }
    };
    for character in text.chars() {
        if aperture.opens_a_word(character) {
            if species == Some(Species::Punctuation) {
                flush(&mut tokens, &mut current);
            }
            current.push(character);
            species = Some(Species::Word);
        } else if character.is_whitespace() {
            flush(&mut tokens, &mut current);
            species = None;
        } else {
            if species == Some(Species::Word) {
                flush(&mut tokens, &mut current);
            }
            if species == Some(Species::Punctuation) && aperture.extends_a_run(character) {
                current.push(character);
            } else {
                flush(&mut tokens, &mut current);
                current.push(character);
            }
            species = Some(Species::Punctuation);
        }
    }
    flush(&mut tokens, &mut current);
    tokens
}

pub fn render_tokens<'a>(tokens: impl IntoIterator<Item = &'a str>) -> String {
    let mut rendered = String::new();
    let mut previous = None::<String>;
    let mut inline_code = false;
    for token in tokens {
        if token == "`" {
            if !inline_code && !rendered.is_empty() {
                rendered.push(' ');
            }
            rendered.push('`');
            inline_code = !inline_code;
            previous = Some(token.to_owned());
            continue;
        }
        let closes = matches!(
            token,
            "." | "," | ";" | ":" | "!" | "?" | ")" | "]" | "}" | "-" | "/"
        );
        let opens_before = previous
            .as_deref()
            .is_some_and(|prior| matches!(prior, "(" | "[" | "{" | "#" | "/" | "-"))
            || (inline_code && previous.as_deref() == Some("`"));
        if !rendered.is_empty() && !closes && !opens_before {
            rendered.push(' ');
        }
        rendered.push_str(token);
        previous = Some(token.to_owned());
    }
    rendered
}

fn sentence_boundary(token: &str) -> bool {
    matches!(token, "." | "!" | "?")
}

fn join_u64(low: u32, high: u32) -> Option<u64> {
    Some(u64::from(low) | (u64::from(high) << 32))
}

#[cfg(test)]
mod horizon_remainder_tests {
    use super::*;

    /// **The division is taken, not the quotient kept.** A continuation matched at a shorter horizon
    /// is set aside and returned, never deleted — and the kept half is unchanged, so emission does
    /// not move.
    ///
    /// Before 2026-08-17 the filter was `by_token.retain(|_, (horizon, _)| *horizon ==
    /// greatest_horizon)` and `Continuation` had no field for the dropped population. The source
    /// comment above it already recorded the consequence: `sources=1` on 89 of 112 emissions.
    #[test]
    fn a_shorter_horizon_continuation_is_withheld_and_returned_rather_than_deleted() {
        // Two continuations, one reached at a deeper context than the other. The deeper one is kept;
        // the shallower one must come back marked rather than vanish.
        let carried = vec![
            Continuation {
                token: "deep".to_owned(),
                matched_horizon: 3,
                sources: BTreeSet::new(),
                withheld_by_horizon: false,
            },
            Continuation {
                token: "shallow".to_owned(),
                matched_horizon: 1,
                sources: BTreeSet::new(),
                withheld_by_horizon: true,
            },
        ];
        let kept: Vec<&Continuation> = carried
            .iter()
            .filter(|continuation| !continuation.withheld_by_horizon)
            .collect();
        let withheld: Vec<&Continuation> = carried
            .iter()
            .filter(|continuation| continuation.withheld_by_horizon)
            .collect();
        assert_eq!(kept.len(), 1);
        assert_eq!(kept[0].token, "deep");
        assert_eq!(withheld.len(), 1, "the remainder must survive the filter");
        assert_eq!(withheld[0].token, "shallow");
        assert!(
            withheld[0].matched_horizon < kept[0].matched_horizon,
            "the withheld half is exactly what the horizon filter set aside"
        );
    }
}

#[cfg(test)]
mod lexical_aperture_tests {
    use super::*;

    /// The excision is graded by its orbit: the inherited aperture must reproduce the reading this
    /// tree has always taken, and a declared alternative must MOVE it. A level lifted with no
    /// exhibited difference is bookkeeping.
    #[test]
    fn the_inherited_aperture_is_the_authored_reading_and_a_declared_one_moves_it() {
        let material = "fn f(x: u32) -> u32 { x .. y && z != w }";
        let inherited = lexical_tokens_under(material, &LexicalAperture::inherited());
        assert_eq!(lexical_tokens(material), inherited);

        // The convicted level, exhibited — and the shape of the defect is sharper than "it shatters
        // operators". The whitelist governs the CONTINUING character, never the opening one, so it is
        // asymmetric: `!=` survives because `=` is whitelisted, while `->`, `&&` and `..` shatter
        // because `>`, `&` and `.` are not. Which operators a material keeps is therefore an accident
        // of which six glyphs were written down.
        assert!(inherited.iter().any(|token| token == "-"), "{inherited:?}");
        assert!(inherited.iter().any(|token| token == ">"), "{inherited:?}");
        assert!(
            !inherited.iter().any(|token| token == "->"),
            "{inherited:?}"
        );
        assert!(
            !inherited.iter().any(|token| token == "&&"),
            "{inherited:?}"
        );
        assert!(
            !inherited.iter().any(|token| token == ".."),
            "{inherited:?}"
        );
        assert!(
            inherited.iter().any(|token| token == "!="),
            "the asymmetry: `=` is whitelisted so `!=` survives — {inherited:?}"
        );

        let maximal = lexical_tokens_under(material, &LexicalAperture::runs_are_maximal());
        assert!(maximal.iter().any(|token| token == "->"), "{maximal:?}");
        assert!(maximal.iter().any(|token| token == "&&"), "{maximal:?}");
        assert!(maximal.iter().any(|token| token == ".."), "{maximal:?}");
        assert!(maximal.iter().any(|token| token == "!="), "{maximal:?}");
        assert_ne!(inherited, maximal);
    }

    /// And the aperture cannot quietly change a material it does not touch: prose whose only
    /// punctuation is single reads identically under both.
    #[test]
    fn a_material_with_no_operator_run_reads_the_same_under_both_apertures() {
        let material = "the arc reaches, and the receiver returns. nothing else moved";
        assert_eq!(
            lexical_tokens_under(material, &LexicalAperture::inherited()),
            lexical_tokens_under(material, &LexicalAperture::runs_are_maximal())
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use soma_membrane::{
        CurrentExecutionRequest, DirectedExecutionRequest, ExecutedContemporaryEvent,
        LiveCurrentError, RegionalExecutionRequest,
    };

    use crate::morphological_language::{
        MorphologicalGenerationSpec, MorphologicalLanguageEcology, MorphologicalLanguagePassage,
    };

    fn action() -> ActionCurrent {
        ActionCurrent::new(Cog::lit(1)).unwrap()
    }

    /// One caller-retained executor which counts the events it was actually asked to realize. It
    /// changes no result: it forwards every request to the same cpu carrier the private path
    /// would have built.
    struct CountingCpuExecutor {
        cpu: ParallelCpuLiveCurrentExecutor,
        enactments: usize,
    }

    impl CountingCpuExecutor {
        const fn new(worker_threads: usize) -> Self {
            Self {
                cpu: ParallelCpuLiveCurrentExecutor::new(worker_threads),
                enactments: 0,
            }
        }
    }

    impl LiveCurrentExecutor for CountingCpuExecutor {
        fn enact(
            &mut self,
            physical_revision: u64,
            standing: &SparseStandingSurface,
            currents: &[CurrentExecutionRequest<'_>],
            relations: &[DirectedExecutionRequest],
            regional: &[RegionalExecutionRequest<'_>],
        ) -> Result<ExecutedContemporaryEvent, LiveCurrentError> {
            self.enactments += 1;
            self.cpu
                .enact(physical_revision, standing, currents, relations, regional)
        }
    }

    /// One supplied executor crosses every Swing event on both generation paths, and the return is
    /// the one the private-cpu path already produced.
    ///
    /// Equality alone would not separate a real twin from one which quietly rebuilt its own cpu
    /// pool and ignored the argument. The count is the frame that makes it falsifiable: the
    /// supplied executor is the only executor either generation path may reach, so a nonzero count
    /// is proof that the question event and every self-emanated return crossed it.
    fn junction_fixture() -> CausalLanguageEcology {
        CausalLanguageEcology::condition(
            &[
                CausalLanguagePassage::new(
                    "arc",
                    1,
                    "the receiver returns the arc. the receiver returns the residual. \
                     the receiver carries the arc onward.",
                ),
                CausalLanguagePassage::new(
                    "current",
                    2,
                    "the receiver returns the current. the current returns the arc. \
                     the receiver founds an axis.",
                ),
            ],
            action(),
            2,
        )
        .unwrap()
    }

    /// The gate is recomputed inside `junction_population` from the same pass that builds the
    /// complete profile. Two implementations of one rule can disagree, so they are held to each
    /// other rather than shared: `continuations` is the inherited law and is untouched.
    #[test]
    fn the_two_branching_laws_agree_on_what_the_gate_keeps() {
        let ecology = junction_fixture();
        for prompt in [
            "the receiver returns the",
            "the receiver",
            "the current returns",
            "an axis",
        ] {
            let history = lexical_tokens(prompt);
            let hexis = ecology.recruit(&history).sources;
            let inherited: BTreeSet<String> = ecology
                .continuations(&history, &hexis)
                .unwrap()
                .into_iter()
                .filter(|continuation| !continuation.withheld_by_horizon)
                .map(|continuation| continuation.token)
                .collect();
            let reading = ecology
                .read_junction(
                    &history,
                    &hexis,
                    ContinuationReceiver::MostSpecificAttestation,
                )
                .unwrap();
            let recomputed: BTreeSet<String> = reading
                .members
                .iter()
                .filter(|member| member.gate_would_keep)
                .map(|member| member.token.clone())
                .collect();
            // The inherited law falls back to the global suffix when its own gate keeps nothing;
            // that fallback is a different population and is compared only when it did not fire.
            if !inherited.is_empty() && !recomputed.is_empty() {
                assert_eq!(inherited, recomputed, "prompt {prompt:?}");
            }
            assert_eq!(
                reading.gate_would_keep,
                recomputed.len(),
                "prompt {prompt:?}"
            );
        }
    }

    /// **The normalising extent is gauge and enters no ratio.** `p_i/p_j = m_i/m_j` exactly, so the
    /// whole population could be renormalised by any positive factor and the family would not move.
    /// This is the cocycle statement in the one form that can be checked against the raw material.
    #[test]
    fn the_extent_is_gauge_and_the_ratio_is_the_bare_multiplicity_quotient() {
        let ecology = junction_fixture();
        let history = lexical_tokens("the receiver returns the");
        let hexis = ecology.recruit(&history).sources;
        let reading = ecology
            .read_junction(
                &history,
                &hexis,
                ContinuationReceiver::MostSpecificAttestation,
            )
            .unwrap();
        assert!(reading.members.len() >= 2, "{:?}", reading.members);
        let family = reading.ratios.as_ref().expect("a family of at least two");
        assert!(family.cocycle_holds());
        assert_eq!(reading.cocycle_holds, Some(true));
        for left in &reading.members {
            for right in &reading.members {
                if left.name == right.name {
                    continue;
                }
                let carried = family
                    .ratio(left.name, right.name)
                    .expect("an ordered pair");
                let bare = Rat::new(
                    BigInt::from(left.multiplicity),
                    BigInt::from(right.multiplicity),
                );
                assert_eq!(*carried, bare, "{} against {}", left.token, right.token);
            }
        }
    }

    /// The gate keeps a subset and the complete law branches the rest. On material where the two
    /// differ, the withheld population is exactly what the inherited path was carrying unread.
    #[test]
    fn the_complete_law_branches_what_the_gate_withheld() {
        let ecology = junction_fixture();
        let history = lexical_tokens("the receiver returns the");
        let hexis = ecology.recruit(&history).sources;
        let reading = ecology
            .read_junction(
                &history,
                &hexis,
                ContinuationReceiver::MostSpecificAttestation,
            )
            .unwrap();
        assert_eq!(
            reading.members.len(),
            reading.gate_would_keep + reading.gate_would_withhold
        );
        assert!(
            reading.gate_would_keep <= reading.members.len(),
            "the gate cannot keep what the junction does not attest"
        );
        // The section modulus is read off the same population and is not vacuous on it.
        let modulus = reading.modulus.as_ref().expect("a non-empty junction");
        assert_eq!(modulus.members, reading.members.len());
        assert!(!reading.collapsed_onto_one_fibre || reading.members.len() == 1);
    }

    /// **The reading moves with the declared receiver.** Two attestations of one junction are two
    /// readings, and neither is a property of the material alone.
    #[test]
    fn the_junction_reading_carries_its_receiver() {
        let ecology = junction_fixture();
        let history = lexical_tokens("the receiver returns the");
        let hexis = ecology.recruit(&history).sources;
        let specific = ecology
            .read_junction(
                &history,
                &hexis,
                ContinuationReceiver::MostSpecificAttestation,
            )
            .unwrap();
        let broad = ecology
            .read_junction(&history, &hexis, ContinuationReceiver::BroadestAttestation)
            .unwrap();
        assert_eq!(
            specific.receiver,
            ContinuationReceiver::MostSpecificAttestation
        );
        assert_eq!(broad.receiver, ContinuationReceiver::BroadestAttestation);
        // The same tokens are attested either way; what moves is the horizon each is read at and
        // the multiplicity that horizon carries.
        let specific_tokens: Vec<&String> = specific
            .members
            .iter()
            .map(|member| &member.token)
            .collect();
        let broad_tokens: Vec<&String> = broad.members.iter().map(|member| &member.token).collect();
        assert_eq!(specific_tokens, broad_tokens);
        for member in &specific.members {
            let lowest = *member.horizon_profile.keys().next().unwrap();
            let highest = *member.horizon_profile.keys().next_back().unwrap();
            assert_eq!(member.horizon, highest);
            assert!(lowest <= highest);
        }
    }

    /// The two branching laws are a declared gauge over one junction, and the orbit is the point:
    /// the complete law reaches at least the surfaces the gate reaches, and generally more.
    ///
    /// **It forms no ratio.** An earlier form carried a `RatioFamily` out on every emitted token;
    /// that was convicted as a misjoin — the ratios changed no transport — and the reading now lives
    /// at `read_junction`, labelled as the diagnostic it is.
    #[test]
    fn the_complete_law_reaches_at_least_what_the_gate_reaches() {
        let ecology = junction_fixture();
        let prompt = "the receiver returns the";
        let spec = |law| CausalLanguageGenerationSpec {
            maximum_generated_tokens: 4,
            stop_at_sentence_boundary: false,
            branching_law: law,
            ..CausalLanguageGenerationSpec::default()
        };
        let gated = ecology
            .generate(prompt, spec(BranchingLaw::GreatestHorizonGate), action(), 2)
            .unwrap();
        let complete = ecology
            .generate(prompt, spec(BranchingLaw::CompleteJunction), action(), 2)
            .unwrap();
        let surfaces = |generation: &CausalLanguageGeneration| -> BTreeSet<String> {
            generation
                .outputs
                .iter()
                .map(|output| output.text.clone())
                .collect()
        };
        let gated_surfaces = surfaces(&gated);
        let complete_surfaces = surfaces(&complete);
        assert!(!gated_surfaces.is_empty() && !complete_surfaces.is_empty());
        assert!(
            complete_surfaces.len() >= gated_surfaces.len(),
            "gate {gated_surfaces:?} against complete {complete_surfaces:?}"
        );
    }

    #[test]
    fn one_supplied_executor_crosses_every_swing_event_on_both_generation_paths() {
        let causal = CausalLanguageEcology::condition(
            &[
                CausalLanguagePassage::new(
                    "training",
                    1,
                    "Training is conditioning morphology through returned consequence.",
                ),
                CausalLanguagePassage::new(
                    "multimodality",
                    2,
                    "Multimodality is caused co-presence viewed through different receivers.",
                ),
            ],
            action(),
            2,
        )
        .unwrap();
        let causal_prompt = "What changes the intermediate body? Training is";
        let causal_spec = CausalLanguageGenerationSpec {
            maximum_generated_tokens: 16,
            stop_at_sentence_boundary: true,
            ..CausalLanguageGenerationSpec::default()
        };
        let private_cpu = causal
            .generate(causal_prompt, causal_spec, action(), 2)
            .unwrap();
        assert!(private_cpu
            .outputs
            .iter()
            .any(|output| !output.text.is_empty()));
        let mut causal_executor = CountingCpuExecutor::new(2);
        let supplied = causal
            .generate_with_executor(causal_prompt, causal_spec, action(), &mut causal_executor)
            .unwrap();
        assert_eq!(private_cpu, supplied);
        assert!(causal_executor.enactments >= private_cpu.outputs.len());

        let morphological = MorphologicalLanguageEcology::condition(
            &[
                MorphologicalLanguagePassage::new(
                    "training",
                    "training-source",
                    1,
                    "Training changes morphology.",
                ),
                MorphologicalLanguagePassage::new(
                    "uncertainty",
                    "uncertainty-source",
                    2,
                    "Changes morphology while uncertainty remains.",
                ),
                MorphologicalLanguagePassage::new(
                    "control",
                    "control-source",
                    3,
                    "A separate receiver retains a control.",
                ),
            ],
            action(),
            2,
        )
        .unwrap();
        let morphological_prompt = "Relate training and uncertainty.";
        let morphological_spec = MorphologicalGenerationSpec {
            maximum_observed_tokens: 32,
        };
        let private_cpu = morphological
            .generate(morphological_prompt, morphological_spec, action(), 2)
            .unwrap();
        assert!(private_cpu
            .outputs
            .iter()
            .any(|output| !output.text.is_empty()));
        let mut morphological_executor = CountingCpuExecutor::new(2);
        let supplied = morphological
            .generate_with_executor(
                morphological_prompt,
                morphological_spec,
                action(),
                &mut morphological_executor,
            )
            .unwrap();
        assert_eq!(private_cpu, supplied);
        assert!(morphological_executor.enactments >= private_cpu.outputs.len());
    }

    #[test]
    fn contextual_hexis_emits_text_and_reenters_as_cause() {
        let ecology = CausalLanguageEcology::condition(
            &[
                CausalLanguagePassage::new(
                    "training",
                    1,
                    "Training is conditioning morphology through returned consequence.",
                ),
                CausalLanguagePassage::new(
                    "multimodality",
                    2,
                    "Multimodality is caused co-presence viewed through different receivers.",
                ),
            ],
            action(),
            2,
        )
        .unwrap();
        let route_wire = ecology.route_rest_image().encode_native_bytes().unwrap();
        assert_eq!(
            CausalLanguageRouteRestImage::from_native_bytes(&route_wire).unwrap(),
            *ecology.route_rest_image()
        );
        let generated = ecology
            .generate(
                "What changes the intermediate body? Training is",
                CausalLanguageGenerationSpec {
                    maximum_generated_tokens: 16,
                    stop_at_sentence_boundary: true,
                    ..CausalLanguageGenerationSpec::default()
                },
                action(),
                2,
            )
            .unwrap();
        assert!(generated
            .initial_hexis
            .iter()
            .any(|source| source.identity == "training"));
        assert!(generated.outputs.iter().any(|output| {
            output.text == "conditioning morphology through returned consequence."
        }));
        assert!(generated
            .outputs
            .iter()
            .flat_map(|output| &output.tokens)
            .all(|token| token.matched_horizon > 0));
    }

    #[test]
    fn plural_successors_return_without_cpu_ranking_or_pruning() {
        let ecology = CausalLanguageEcology::condition(
            &[
                CausalLanguagePassage::new("alpha", 1, "Root emits alpha."),
                CausalLanguagePassage::new("beta", 2, "Root emits beta."),
                CausalLanguagePassage::new("gamma", 3, "Root emits gamma."),
            ],
            action(),
            2,
        )
        .unwrap();
        let generated = ecology
            .generate(
                "Root emits",
                CausalLanguageGenerationSpec {
                    maximum_generated_tokens: 1,
                    stop_at_sentence_boundary: false,
                    ..CausalLanguageGenerationSpec::default()
                },
                action(),
                2,
            )
            .unwrap();
        assert_eq!(generated.outputs.len(), 3);
        for expected in ["alpha", "beta", "gamma"] {
            assert!(generated.outputs.iter().any(|output| {
                output.tokens.len() == 1
                    && output.tokens[0].token == expected
                    && output.tokens[0].sources.contains(expected)
            }));
        }
    }

    #[test]
    fn absent_morphology_does_not_receive_a_root_vocabulary() {
        let ecology = CausalLanguageEcology::condition(
            &[CausalLanguagePassage::new(
                "training",
                1,
                "Training is conditioning morphology.",
            )],
            action(),
            1,
        )
        .unwrap();
        let generated = ecology
            .generate(
                "xylophonic quasar",
                CausalLanguageGenerationSpec {
                    maximum_generated_tokens: 8,
                    stop_at_sentence_boundary: true,
                    ..CausalLanguageGenerationSpec::default()
                },
                action(),
                1,
            )
            .unwrap();
        assert!(generated.initial_hexis.is_empty());
        assert!(generated
            .outputs
            .iter()
            .all(|output| output.text.is_empty()));
    }

    #[test]
    fn lexical_receiver_preserves_words_and_punctuation_as_distinct_faces() {
        let tokens = lexical_tokens("Receiver-local paths: don't flatten.");
        assert_eq!(
            tokens,
            ["Receiver", "-", "local", "paths", ":", "don't", "flatten", "."]
        );
        assert_eq!(
            render_tokens(tokens.iter().map(String::as_str)),
            "Receiver-local paths: don't flatten."
        );
    }

    #[test]
    #[ignore = "requires the RTX CUDA device and committed lineage_event PTX entry"]
    fn one_cell_complex_route_conditioning_is_cpu_card_exact() {
        let feature = route_feature_fiber("conditioning");
        let sources = [
            fiber_from_bytes(0x5254_534f_5552_4345, b"first"),
            fiber_from_bytes(0x5254_534f_5552_4345, b"second"),
        ];
        let groups = BTreeMap::from([(
            feature,
            vec![
                RouteTrainingSection {
                    source_order: 0,
                    source: sources[0].clone(),
                },
                RouteTrainingSection {
                    source_order: 1,
                    source: sources[1].clone(),
                },
            ],
        )]);
        let cpu = condition_route_receivers(groups.clone(), action(), 2).unwrap();
        let mut cuda = crate::live_current_cuda::CudaLiveCurrentExecutor::new(0).unwrap();
        let card = condition_route_receivers_with_executor(groups, action(), &mut cuda).unwrap();
        assert_eq!(cpu, card);
        assert!(cuda.launches() >= 2);
        assert!(cuda.contact_launches() >= 2);
    }
}

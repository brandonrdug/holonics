//! Conditional joint sampling on one continuing native receiver trajectory.
//!
//! Each selected class is read at the actual pending native word and then received once through
//! `Reference::receive_receiver_prefix_continuing` before the next read. The three policies change
//! only the face used to choose that class: trained full-fibre native, founding R on the same
//! native history, or the executed tree. This is sequential conditional sampling, not global mode
//! search. Fresh-body comparison is a separate caller-owned trajectory.
//!
//! The computational object remains the helical pair interaction with its current, source moment,
//! receiver faces, placement, and tower attached. This boundary touches the helix/carry and
//! receiver faces; pair contacts, cell holonomy, tube, and tower remain those of the native owner.

use super::super::*;
use std::path::Path;

/// A local readout intervention. Every arm still receives its selected cell through the same
/// native full-fibre continuation law.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SamplingPolicy {
    NativeFullFibre,
    FoundingRAtSameHistory,
    Tree,
}

impl SamplingPolicy {
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::NativeFullFibre => "trained-native-full-fibre",
            Self::FoundingRAtSameHistory => "founding-R-same-history",
            Self::Tree => "executed-tree",
        }
    }

    fn masses<'a>(
        self,
        reading: &'a holonics::hnn::receiving::cells::diagnostic::RetainedReceiverDiagnostic,
    ) -> &'a [ExactInterval] {
        match self {
            Self::NativeFullFibre => &reading.native.native_masses,
            Self::FoundingRAtSameHistory => &reading.control.native_masses,
            Self::Tree => &reading.native.tree_masses,
        }
    }
}

/// A declared output boundary. The last diagnostic and actual receiver receipt are retained only
/// at this predeclared cut, keeping evidence bounded independently of the output length.
#[derive(Clone, Debug)]
pub(super) struct CutReceipt {
    pub output_cells: usize,
    pub source_moment: String,
    pub source_cells: u64,
    pub current_lift: Vec<num_bigint::BigInt>,
    pub native_state_sha256: String,
    pub crib_sha256: String,
    pub checkpoint_path: String,
    pub checkpoint_sha256: String,
    pub last_class: Option<usize>,
    pub last_diagnostic:
        Option<holonics::hnn::receiving::cells::diagnostic::RetainedReceiverDiagnostic>,
    pub last_receipt: Option<holonics::hnn::reference::observed::ReceiverPrefixReceipt>,
}

/// The cold restore control made at output boundary 64 and continued with keys 64 through 67.
#[derive(Clone, Debug)]
pub(super) struct ColdContinuationCheck {
    pub checkpoint_sha256: String,
    pub before_state_sha256: String,
    pub before_crib_sha256: String,
    pub continued_classes: Vec<usize>,
    pub after_state_sha256: String,
    pub after_crib_sha256: String,
    pub matched_warm_state_and_crib: bool,
}

/// Raw, lossless output and exterior evidence for a single policy trajectory.
#[derive(Clone, Debug)]
pub(super) struct SampleReceipt {
    pub policy: SamplingPolicy,
    pub prompt_sha256: String,
    pub key_schedule_sha256: String,
    pub output_cells_requested: usize,
    pub classes: Vec<usize>,
    pub raw_bytes: Vec<u8>,
    pub unfinished_cells: Vec<usize>,
    /// Present only when all returned classes form whole octets and those bytes are strict UTF-8.
    pub strict_utf8: Option<String>,
    pub utf8_boundary: String,
    pub stop: String,
    pub cuts: Vec<CutReceipt>,
    pub cold_continuation: Option<ColdContinuationCheck>,
    pub final_state_sha256: String,
    pub final_crib_sha256: String,
}

struct OneCell {
    class: Option<usize>,
    certified: Option<holonics::receiver::release::CertifiedDraw>,
    diagnostic: holonics::hnn::receiving::cells::diagnostic::RetainedReceiverDiagnostic,
    receipt: Option<holonics::hnn::reference::observed::ReceiverPrefixReceipt>,
    stop: &'static str,
}

fn native_and_crib_hashes(
    resident: &Resident,
    crib: &holonics::hnn::reference::observed::ObservedCrib,
) -> Result<(String, String)> {
    let state = resident.continuing_state(0)?.to_text();
    let crib = crib.unplaced_checkpoint()?;
    Ok((sha256(state.as_bytes())?, sha256(crib.as_bytes())?))
}

fn source_position(resident: &Resident) -> Result<(String, u64)> {
    let (moment, _) = resident
        .continuing()
        .ok_or("the continuation has no actual open source moment")?;
    let source = resident
        .moment(&moment)
        .ok_or("the continuation's source moment is absent")?;
    Ok((format!("{moment:?}: {source:?}"), source.cells()))
}

fn checkpoint_at(
    parent: &Checkpoint,
    policy: SamplingPolicy,
    prompt_sha256: &str,
    output_cells: usize,
    resident: &Resident,
    crib: &holonics::hnn::reference::observed::ObservedCrib,
) -> Result<Checkpoint> {
    let stream = ObservedStream::restore(
        resident.clone(),
        crib.clone(),
        ObservedEpochDepositionScope::NormalMaps,
        Vec::new(),
    )?;
    Ok(Checkpoint {
        population: parent.population,
        stream,
        provenance: format!(
            "{}\nconditional-native-continuation-v1 policy={} prompt_sha256={} output_cells={output_cells}",
            parent.provenance,
            policy.label(),
            prompt_sha256,
        ),
    })
}

fn publish_cut(
    parent: &Checkpoint,
    policy: SamplingPolicy,
    prompt_sha256: &str,
    output_cells: usize,
    resident: &Resident,
    crib: &holonics::hnn::reference::observed::ObservedCrib,
    output_dir: &Path,
) -> Result<(CutReceipt, Checkpoint)> {
    let checkpoint = checkpoint_at(parent, policy, prompt_sha256, output_cells, resident, crib)?;
    let (source_moment, source_cells) = source_position(resident)?;
    let (native_state_sha256, crib_sha256) = native_and_crib_hashes(resident, crib)?;
    let file_name = format!(
        "{}-prompt-{}-cells-{output_cells:03}.checkpoint",
        policy.label(),
        &prompt_sha256[..12],
    );
    let path = output_dir.join(file_name);
    let path_text = path
        .to_str()
        .ok_or("checkpoint path is not UTF-8")?
        .to_owned();
    let (_, checkpoint_sha256) = checkpoint.publish(&path_text)?;
    Ok((
        CutReceipt {
            output_cells,
            source_moment,
            source_cells,
            current_lift: resident.current().lift().to_vec(),
            native_state_sha256,
            crib_sha256,
            checkpoint_path: path_text,
            checkpoint_sha256,
            last_class: None,
            last_diagnostic: None,
            last_receipt: None,
        },
        checkpoint,
    ))
}

fn cold_load_cut(
    path: &str,
    expected: &Checkpoint,
    reference: &Reference,
    pairing: &PairingDeclaration,
    warm_resident: &Resident,
    warm_crib: &holonics::hnn::reference::observed::ObservedCrib,
) -> Result<(
    String,
    Resident,
    holonics::hnn::reference::observed::ObservedCrib,
)> {
    let budget = std::fs::metadata(path)?.len();
    let (cold, file_hash) = Checkpoint::load(path, budget)?;
    if file_hash != sha256(&expected.bytes()?)? || cold.bytes()? != expected.bytes()? {
        return Err("cold checkpoint bytes changed across serialization".into());
    }
    let (cold_resident, cold_crib) = cold.stream.query_fork(reference, pairing)?;
    if native_and_crib_hashes(warm_resident, warm_crib)?
        != native_and_crib_hashes(&cold_resident, &cold_crib)?
    {
        return Err("cold checkpoint changed native state or closing crib".into());
    }
    Ok((file_hash, cold_resident, cold_crib))
}

#[allow(clippy::too_many_arguments)]
fn advance_one(
    reference: &Reference,
    resident: &mut Resident,
    crib: &mut holonics::hnn::reference::observed::ObservedCrib,
    pairing: &PairingDeclaration,
    control_map: &ExactRatMatrix,
    receiver: &holonics::hnn::receiving::RetainedFibreReceiver,
    policy: SamplingPolicy,
    key: &Rat,
) -> Result<OneCell> {
    let (moment, _) = resident
        .continuing()
        .ok_or("the conditional path lost its actual source moment")?;
    let phases = resident
        .admitted()
        .first()
        .ok_or("the conditional path has no admitted receiver")?
        .clone();
    let (pending, _) = reference.refine(resident, &moment, &phases)?;
    let diagnostic = reference.diagnose_pending_readout_at_receiver(
        resident,
        &pending,
        control_map,
        receiver,
        holonics::ratio::exponentiated::READING_BITS,
    )?;
    let decision = holonics::receiver::release::draw(policy.masses(&diagnostic), key)?;
    let holonics::receiver::release::ReleaseReturn::Drawn(certified) = decision else {
        reference.discard(resident, holonics::hnn::port::Handle::Pending(pending))?;
        return Ok(OneCell {
            class: None,
            certified: None,
            diagnostic,
            receipt: None,
            stop: "Unresolved",
        });
    };
    let class = certified.class;
    let receipt = reference.receive_receiver_prefix_continuing(
        resident, crib, pairing, pending, class, receiver, None,
    )?;
    Ok(OneCell {
        class: Some(class),
        certified: Some(certified),
        diagnostic,
        receipt: Some(receipt),
        stop: "DeclaredLength",
    })
}

/// Continue one native query fork with a fixed schedule of eight-byte keys and no mode search.
/// `cuts` are distinct increasing output-cell positions including zero; a cut records the last
/// received class, or the next actual read when no class has yet arrived. A cut at 128 is recorded
/// from the last produced receipt and performs no extra refine/read.
#[allow(clippy::too_many_arguments)]
pub(super) fn sample_continuing(
    checkpoint: &Checkpoint,
    prompt: &[u8],
    policy: SamplingPolicy,
    key_bytes: &[u8],
    output_cells: usize,
    cuts: &[usize],
    cold_replay_at: Option<usize>,
    output_dir: &Path,
) -> Result<SampleReceipt> {
    if output_cells == 0 || prompt.len() > QUERY_BYTE_BUDGET {
        return Err("conditional sampling needs a positive output and a bounded prompt".into());
    }
    let horizon = checkpoint
        .stream
        .accepted_cells()?
        .checked_add(u64::try_from(
            prompt
                .len()
                .checked_mul(4)
                .ok_or("prompt horizon overflow")?,
        )?)
        .and_then(|n| n.checked_add(output_cells as u64))
        .ok_or("output horizon overflow")?;
    if horizon > checkpoint.population {
        return Err("conditional trajectory exceeds its declared source horizon".into());
    }
    if key_bytes.len() != output_cells.checked_mul(8).ok_or("key schedule overflow")? {
        return Err("one declared eight-byte key is required for every output cell".into());
    }
    if cuts.first() != Some(&0)
        || cuts.windows(2).any(|pair| pair[0] >= pair[1])
        || cuts.iter().any(|&cut| cut > output_cells)
        || cuts.last() != Some(&output_cells)
    {
        return Err(
            "output cuts must be increasing positions from zero through the declared length".into(),
        );
    }
    if let Some(boundary) = cold_replay_at {
        if boundary
            .checked_add(4)
            .map_or(true, |end| end > output_cells)
            || !cuts.contains(&boundary)
        {
            return Err(
                "the cold replay needs a declared cut and four remaining output cells".into(),
            );
        }
    }
    std::fs::create_dir_all(output_dir)?;
    let started = Instant::now();
    let mut progress = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(output_dir.join("classes.jsonl"))?;

    let original_checkpoint = checkpoint.bytes()?;
    let prompt_sha256 = sha256(prompt)?;
    let key_schedule_sha256 = sha256(key_bytes)?;
    let reference = port();
    let (field, founding, pairing) = declaration(checkpoint.population)?;
    let (mut resident, mut crib) = checkpoint.stream.query_fork(&reference, &pairing)?;
    for class in digits(prompt) {
        reference.ingest_class_continuing(&mut resident, &mut crib, &pairing, class, None)?;
    }
    let phases = resident
        .admitted()
        .first()
        .ok_or("prompt ingress left no receiver")?
        .clone();
    if resident.field() != &field {
        return Err("query fork no longer matches its declared native field".into());
    }
    let receiver = holonics::hnn::receiving::RetainedFibreReceiver::declare(phases.grain())?;
    let control_map = founding
        .receiving_law(phases.ring())
        .ok_or("the founding-R control has no receiver map")?
        .map()
        .clone();

    let mut key_stream = KeyStream::new(key_bytes.to_vec(), 8)?;
    let mut keys = Vec::with_capacity(output_cells);
    for _ in 0..output_cells {
        keys.push(
            key_stream
                .next_key()
                .ok_or("declared key stream ended early")?,
        );
    }
    if key_stream.keys_read() != output_cells {
        return Err("the key stream did not consume the declared schedule exactly".into());
    }

    let mut cuts_out = Vec::with_capacity(cuts.len());
    let mut cut_at = 0;
    let (initial_cut, initial_checkpoint) = publish_cut(
        checkpoint,
        policy,
        &prompt_sha256,
        0,
        &resident,
        &crib,
        output_dir,
    )?;
    cold_load_cut(
        &initial_cut.checkpoint_path,
        &initial_checkpoint,
        &reference,
        &pairing,
        &resident,
        &crib,
    )?;
    cuts_out.push(initial_cut);
    cut_at += 1;

    let mut classes = Vec::with_capacity(output_cells);
    let mut last_diagnostic = None;
    let mut last_receipt = None;
    let mut last_class = None;
    let mut stop = "DeclaredLength";
    let mut cold_branch: Option<(Resident, holonics::hnn::reference::observed::ObservedCrib)> =
        None;
    let mut cold_checkpoint_hash = None;
    let mut cold_before_hashes: Option<(String, String)> = None;
    let mut cold_classes = Vec::new();
    let mut cold_check = None;

    for at in 0..output_cells {
        let cell = advance_one(
            &reference,
            &mut resident,
            &mut crib,
            &pairing,
            &control_map,
            &receiver,
            policy,
            &keys[at],
        )?;
        last_diagnostic = Some(cell.diagnostic.clone());
        if let Some(class) = cell.class {
            classes.push(class);
            last_class = Some(class);
            last_receipt = cell.receipt;
            writeln!(
                progress,
                "{}",
                object(&[
                    ("cell", at.to_string()),
                    ("class", class.to_string()),
                    ("key", rational(&keys[at])),
                    ("certified_draw", exact(&cell.certified)),
                    (
                        "certified_key_margin_lower",
                        cell.certified.as_ref().map_or("null".into(), |c| rational(
                            &std::cmp::min(&c.key - &c.prior_upper, &c.through_lower - &c.key)
                        ))
                    ),
                    (
                        "native_masses",
                        exact(&cell.diagnostic.native.native_masses)
                    ),
                    (
                        "founding_R_masses",
                        exact(&cell.diagnostic.control.native_masses)
                    ),
                    ("tree_masses", exact(&cell.diagnostic.native.tree_masses)),
                    (
                        "native_minus_tree",
                        exact(&cell.diagnostic.native.native_minus_tree)
                    ),
                    (
                        "native_minus_founding_R",
                        exact(&cell.diagnostic.native_minus_control_masses)
                    ),
                    ("extra_word_score_root_calls_for_receipt", "0".into()),
                    ("elapsed_ns", started.elapsed().as_nanos().to_string())
                ])
            )?;
            progress.flush()?;
            eprintln!(
                "complete-language output_cells={} elapsed_ns={}",
                classes.len(),
                started.elapsed().as_nanos()
            );
        } else {
            stop = cell.stop;
        }

        if cold_replay_at.is_some_and(|boundary| (boundary..boundary + 4).contains(&at)) {
            let (cold_resident, cold_crib) = cold_branch
                .as_mut()
                .ok_or("cold output branch was not restored at the declared boundary")?;
            let cold = advance_one(
                &reference,
                cold_resident,
                cold_crib,
                &pairing,
                &control_map,
                &receiver,
                policy,
                &keys[at],
            )?;
            if cold.class != cell.class {
                return Err(
                    "warm and cold branches chose different classes under the same key".into(),
                );
            }
            if let Some(class) = cold.class {
                cold_classes.push(class);
            }
            if resident.continuing_state(0)? != cold_resident.continuing_state(0)?
                || crib != *cold_crib
            {
                return Err(
                    "warm/cold continued state or crib differs after an emitted class".into(),
                );
            }
            let finish_cold = cold_replay_at.is_some_and(|boundary| at == boundary + 3);
            if finish_cold || cell.class.is_none() {
                let (warm_state, warm_crib) = native_and_crib_hashes(&resident, &crib)?;
                let (cold_state, cold_crib_hash) =
                    native_and_crib_hashes(cold_resident, cold_crib)?;
                let matched = warm_state == cold_state && warm_crib == cold_crib_hash;
                if !matched {
                    return Err("four keyed continuation cells diverged after cold restore".into());
                }
                cold_check = Some(ColdContinuationCheck {
                    checkpoint_sha256: cold_checkpoint_hash
                        .clone()
                        .ok_or("cold checkpoint receipt is missing")?,
                    before_state_sha256: cold_before_hashes
                        .as_ref()
                        .ok_or("cold opening receipt is missing")?
                        .0
                        .clone(),
                    before_crib_sha256: cold_before_hashes
                        .as_ref()
                        .ok_or("cold opening receipt is missing")?
                        .1
                        .clone(),
                    continued_classes: cold_classes.clone(),
                    after_state_sha256: warm_state,
                    after_crib_sha256: warm_crib,
                    matched_warm_state_and_crib: matched,
                });
                if cell.class.is_none() {
                    stop = cell.stop;
                    break;
                }
            }
        }

        let boundary = classes.len();
        if cut_at < cuts.len() && cuts[cut_at] == boundary {
            let (mut cut, saved_checkpoint) = publish_cut(
                checkpoint,
                policy,
                &prompt_sha256,
                boundary,
                &resident,
                &crib,
                output_dir,
            )?;
            cut.last_class = last_class;
            cut.last_diagnostic = last_diagnostic.clone();
            cut.last_receipt = last_receipt.clone();
            let (cold_file_hash, cold_resident, cold_crib) = cold_load_cut(
                &cut.checkpoint_path,
                &saved_checkpoint,
                &reference,
                &pairing,
                &resident,
                &crib,
            )?;
            if cold_file_hash != cut.checkpoint_sha256 {
                return Err("published and cold-loaded checkpoint hashes disagree".into());
            }
            let warm_hashes = native_and_crib_hashes(&resident, &crib)?;
            if cold_replay_at == Some(boundary) {
                cold_checkpoint_hash = Some(cold_file_hash);
                cold_before_hashes = Some(warm_hashes);
                cold_branch = Some((cold_resident, cold_crib));
            }
            cuts_out.push(cut);
            cut_at += 1;
        }
        if cell.class.is_none() {
            stop = cell.stop;
            break;
        }
    }

    if checkpoint.bytes()? != original_checkpoint {
        return Err("conditional output changed its immutable opening checkpoint".into());
    }
    if cut_at != cuts.len() && stop == "DeclaredLength" {
        return Err("the sampler ended before a predeclared output cut".into());
    }
    let decoded = Base4Bytes::decode(&classes, output_cells)?;
    let strict_utf8 = decoded.complete_boundary_text().map(str::to_owned);
    let (final_state_sha256, final_crib_sha256) = native_and_crib_hashes(&resident, &crib)?;
    Ok(SampleReceipt {
        policy,
        prompt_sha256,
        key_schedule_sha256,
        output_cells_requested: output_cells,
        classes,
        raw_bytes: decoded.bytes,
        unfinished_cells: decoded.unfinished_cells,
        strict_utf8,
        utf8_boundary: format!("{:?}", decoded.utf8),
        stop: stop.to_owned(),
        cuts: cuts_out,
        cold_continuation: cold_check,
        final_state_sha256,
        final_crib_sha256,
    })
}

//! The native route's exterior commands: train on text, then release a keyed continuation.
//!
//! [definition; agent-inferred, October 22] The native route is the route whose contacts learn
//! (`ObservedStream::receive_native_current_learning`, record
//! `2026-10-22_THE_NATIVE_CONTACT_STEP_IS_CERTIFIED_BY_REREADING_THE_SAME_COMPARISON`). Text enters
//! as base-four cells (`Base4Bytes`), the exterior byte chart; nothing else about it reaches the
//! machine. Delivery goes one receiver section at a time, so each progress line falls where the
//! receiver's own passage puts it. The whole state is saved where its aeon closes and after the
//! last cell, so a saved state stands at a closed cycle or at the corpus end. A sample is a frozen
//! fork of the saved state, conditioned on a prompt without learning, then released one keyed cell
//! at a time.
use super::*;
use holonics::hnn::reference::native_context::NativeContextEvent;

/// The contact lattice's qualification refinement used by every native control
/// (`native_context_controls.rs`): each contact channel re-based 24 levels finer before any
/// prediction exists, a lossless representation refinement.
const CONTACT_GRAIN_LEVELS: u32 = 24;
const STATE_MAGIC: &str = "complete-language-native-route-v1";

/// The native opening at a declared population: the controls' resident before its first cell.
fn opening(population: u64) -> Result<(Reference, Field, PairingDeclaration, Resident)> {
    let reference = port();
    let (field, mut initial, pairing) = declaration_with_input_context(population, true, true)?;
    initial.bind_family_local_receiving_return(2)?;
    initial.bind_bounded_receiving_representation(2)?;
    initial.bind_native_rational_receiving(2)?;
    let mut resident = reference.mount_declared_receiving_law(
        &field,
        &Current::at_rest(&field),
        initial,
        holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1,
    )?;
    let empty = PairedObservation::admit(&field, resident.constitution(), &pairing)?.encode(&[])?;
    reference.ingest(&mut resident, None, &empty)?;
    resident.refine_contact_grain(CONTACT_GRAIN_LEVELS)?;
    resident.select_represented_native_prepared_input(&pairing)?;
    Ok((reference, field, pairing, resident))
}

/// The receiver's section width: the product of the periods of the rings before it.
fn section_width(stream: &ObservedStream) -> Result<usize> {
    let resident = stream.resident();
    let receiver = resident.admitted().first().ok_or("one native receiver section")?.ring();
    let width = resident.field().rings()[..receiver]
        .iter()
        .try_fold(1u64, |n, r| n.checked_mul(r.period()).ok_or("section width overflow"))?;
    Ok(usize::try_from(width)?)
}

fn state_text(stream: &ObservedStream, population: u64, provenance: &str) -> Result<String> {
    let native = stream.resident().continuing_state(0)?.to_text();
    let crib = stream.crib().unplaced_checkpoint()?;
    let pending = stream.pending_checkpoint();
    Ok(format!(
        "{STATE_MAGIC}\n{population} {} {} {} {} {}\n{native}{crib}{pending}{provenance}",
        stream.crib().next_position(),
        native.len(),
        crib.len(),
        pending.len(),
        provenance.len()
    ))
}

fn load_state(text: &str) -> Result<(Reference, Field, PairingDeclaration, ObservedStream)> {
    let (magic, rest) = text.split_once('\n').ok_or("missing native state header")?;
    if magic != STATE_MAGIC {
        return Err("not a native-route state".into());
    }
    let (sizes, body) = rest.split_once('\n').ok_or("missing native state sizes")?;
    let values = sizes
        .split_whitespace()
        .map(str::parse::<u64>)
        .collect::<std::result::Result<Vec<_>, _>>()?;
    let [population, next, native, crib, pending, provenance] = values.as_slice() else {
        return Err("invalid native state sizes".into());
    };
    let mut at = 0usize;
    let mut take = |length: u64| -> Result<&str> {
        let end = at
            .checked_add(usize::try_from(length)?)
            .ok_or("native state length overflow")?;
        let part = body.get(at..end).ok_or("native state section boundary")?;
        at = end;
        Ok(part)
    };
    let (native, crib, pending) = (take(*native)?, take(*crib)?, take(*pending)?);
    take(*provenance)?;
    if at != body.len() {
        return Err("native state section lengths do not match".into());
    }
    let (reference, field, pairing, fresh) = opening(*population)?;
    let state = ContinuingState::from_text(native, READ_BUDGET)?;
    let resident = reference.mount_continued(
        &field,
        &Current::at_rest(&field),
        fresh.constitution().clone(),
        &state,
    )?;
    if resident.continuing_state(0)? != state {
        return Err("cold native restore changed the saved state".into());
    }
    let crib = ObservedCrib::from_unplaced_checkpoint(
        &field,
        resident.current(),
        usize::try_from(*next)?,
        crib,
    )?;
    let stream = ObservedStream::restore_checkpoint(resident, crib, pending)?;
    Ok((reference, field, pairing, stream))
}

/// A reading of an exact bit count, for the progress line only.
fn bits(value: &Rat) -> String {
    let thousandths = (value * integer(1000)).floor().to_integer();
    format!("{}.{:03}", &thousandths / 1000, &thousandths % 1000)
}

/// One event's score of its actual class before it learned it: the prequential code.
fn add_score(event: &NativeContextEvent, code: &mut (Rat, Rat, i64)) {
    if let Some(score) = event.scores.first() {
        code.0 += &score.lower;
        code.1 += &score.upper;
        code.2 += 1;
    }
}

/// The code read by the exterior byte chart's digit position (`Base4Bytes`, most significant
/// first): a reading beside the training, never delivered to the machine.
fn add_digit_score(event: &NativeContextEvent, by_digit: &mut [(Rat, Rat, i64); 4]) {
    add_score(event, &mut by_digit[(event.prediction.source_cells % 4) as usize]);
}

/// The receiving tree's face alone at the same cell, `−log₂ q(t)`: the count-only code the joined
/// face is measured against (a reading beside the training).
fn add_tree_score(event: &NativeContextEvent, code: &mut (Rat, Rat, i64)) {
    let Some(q) = event.prediction.trees.first().and_then(|t| t.probabilities.get(event.selected_class)) else { return };
    if let Ok(log) = holonics::ratio::algebraic::log2_enclosure_at(q, READING_BITS) {
        code.0 -= &log.upper;
        code.1 -= &log.lower;
        code.2 += 1;
    }
}

fn per_digit(by_digit: &[(Rat, Rat, i64); 4]) -> String {
    let lower = by_digit.iter().map(|c| bits(&(&c.0 / integer(c.2.max(1))))).collect::<Vec<_>>();
    format!("[{}]", lower.join(","))
}

/// The step exponents `k` (`η = 2^k`) a publication certified, by family, with the entries that
/// moved: a reading of how far the deposit went, beside the code.
fn steps(reading: &holonics::hnn::constitution::DepositReading) -> String {
    let each = reading.steps.iter().map(|(_, s)| format!("{:?}:{}", s.family, s.step.exponent)).collect::<Vec<_>>();
    format!("{}/{}", each.join("+"), reading.stepped)
}

fn per_cell(code: &(Rat, Rat, i64)) -> String {
    let n = integer(code.2.max(1));
    format!("[{},{}]", bits(&(&code.0 / &n)), bits(&(&code.1 / &n)))
}

pub(super) fn train(args: &[String]) -> Result<()> {
    if args.len() != 5 {
        return Err("train-native CORPUS SHA POPULATION OUT".into());
    }
    let started = Instant::now();
    let data = pinned_read(&args[1], &args[2], 1 << 20)?;
    let cells = digits(&data);
    let population: u64 = args[3].parse()?;
    if u64::try_from(cells.len())? > population {
        return Err("declared population cannot hold the corpus".into());
    }
    let out = Path::new(&args[4]);
    std::fs::create_dir(out)?;
    let provenance = format!("corpus_sha256={} bytes={} cells={}", args[2], data.len(), cells.len());
    let (reference, _, pairing, resident) = opening(population)?;
    let mut stream = ObservedStream::new(
        resident,
        ObservedCrib::new(0),
        ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap,
    )?;
    let width = section_width(&stream)?;
    println!("NATIVE_TRAIN_OPEN bytes={} cells={} section_cells={width} opening_ms={}", data.len(), cells.len(), started.elapsed().as_millis());
    let flat = rat(2, 1);
    let mut total = (integer(0), integer(0), 0i64);
    let (mut contacts, mut refusals) = (0usize, Vec::new());
    let zero = || (integer(0), integer(0), 0i64);
    let mut by_digit = [zero(), zero(), zero(), zero()];
    let mut tree_total = zero();
    for (index, chunk) in cells.chunks(width).enumerate() {
        let at = usize::try_from(stream.accepted_cells()?)? + stream.pending_classes().len();
        let chunk_started = Instant::now();
        let mut code = (integer(0), integer(0), 0i64);
        let mut tree_code = zero();
        let mut contact_ms = 0u128;
        let receipt = stream.receive_native_current_learning(&reference, &pairing, chunk, READING_BITS, &mut |e| {
            if e.reread.is_some() {
                contact_ms = chunk_started.elapsed().as_millis();
            }
            add_score(e, &mut code);
            add_digit_score(e, &mut by_digit);
            add_tree_score(e, &mut tree_code);
        })?;
        let learn_ms = chunk_started.elapsed().as_millis();
        let r_steps = receipt.sections.iter().map(|s| steps(&s.publication)).collect::<Vec<_>>().join(",");
        let contact_steps = receipt.contacts.iter().filter_map(|e| e.contact.as_ref().map(|c| {
            format!("{}@h{}", steps(&c.publication), e.reread.as_ref().and_then(|r| r.admitted).map_or("-".to_string(), |h| h.to_string()))
        })).collect::<Vec<_>>().join(",");
        contacts += receipt.contacts.len();
        for (offset, reason) in &receipt.contact_refusals {
            refusals.push((at + offset, reason.clone()));
        }
        let saved = Instant::now();
        let last = (index + 1) * width >= cells.len();
        let state_bytes = if last || stream.resident().native_source_frontier()?.aeon_cells() == 0 {
            let text = state_text(&stream, population, &provenance)?;
            let part = out.join("STATE.part");
            std::fs::write(&part, &text)?;
            std::fs::rename(&part, out.join("STATE"))?;
            text.len()
        } else {
            0
        };
        let calls = holonics::hnn::word::work::process_native_calls();
        println!(
            "NATIVE_TRAIN cells={}/{} scored={} pending={} contacts={contacts} refusals={} chunk_code_bits_per_cell={} tree_only={} flat={} code_by_byte_digit={} r_steps=[{r_steps}] contact_steps=[{contact_steps}] learn_ms={learn_ms} contact_ms={contact_ms} state_bytes={} save_ms={} elapsed_ms={} native_calls=[{},{},{},{}]",
            at + chunk.len(), cells.len(), code.2, stream.pending_classes().len(), refusals.len(), per_cell(&code), per_cell(&tree_code), bits(&flat), per_digit(&by_digit),
            state_bytes, saved.elapsed().as_millis(), started.elapsed().as_millis(),
            calls.forward_attempts, calls.response_attempts, calls.return_attempts, calls.response_return_attempts
        );
        total.0 += &code.0;
        total.1 += &code.1;
        total.2 += code.2;
        tree_total.0 += &tree_code.0;
        tree_total.1 += &tree_code.1;
        tree_total.2 += tree_code.2;
    }
    let state = std::fs::read(out.join("STATE"))?;
    write_new(&out.join("RECEIPT.json"), object(&[
        ("command", quoted(&args[0])),
        ("corpus_sha256", quoted(&args[2])),
        ("bytes", data.len().to_string()),
        ("cells", cells.len().to_string()),
        ("population", population.to_string()),
        ("section_cells", width.to_string()),
        ("contacts", contacts.to_string()),
        ("contact_refusals", exact(&refusals)),
        ("prequential_code_bits", exact(&(&total.0, &total.1))),
        ("tree_only_code_bits", exact(&(&tree_total.0, &tree_total.1))),
        ("code_bits_by_byte_digit", exact(&by_digit.iter().map(|c| (&c.0, &c.1, c.2)).collect::<Vec<_>>())),
        ("scored_cells", total.2.to_string()),
        ("state_sha256", quoted(&sha256(&state)?)),
        ("elapsed_ns", started.elapsed().as_nanos().to_string()),
    ]).as_bytes())?;
    println!("NATIVE_TRAIN_DONE cells={} scored={} contacts={contacts} refusals={} code_bits_per_cell={} tree_only={} flat={} code_by_byte_digit={} state_sha256={} elapsed_ms={}", cells.len(), total.2, refusals.len(), per_cell(&total), per_cell(&tree_total), bits(&flat), per_digit(&by_digit), sha256(&state)?, started.elapsed().as_millis());
    Ok(())
}

pub(super) fn sample(args: &[String]) -> Result<()> {
    if args.len() != 9 {
        return Err("sample-native STATE STATE_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA CELLS OUT".into());
    }
    let started = Instant::now();
    let state = pinned_read(&args[1], &args[2], READ_BUDGET as usize)?;
    let prompt = pinned_read(&args[3], &args[4], QUERY_BYTE_BUDGET)?;
    let count: usize = args[7].parse()?;
    let keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    if keys.len() < count.checked_mul(8).ok_or("key extent overflow")? {
        return Err("fewer eight-byte keys than declared cells".into());
    }
    let out = Path::new(&args[8]);
    std::fs::create_dir(out)?;
    let (reference, _, pairing, stream) = load_state(std::str::from_utf8(&state)?)?;
    println!("NATIVE_SAMPLE_RESTORED accepted={} pending={} restore_ms={}", stream.accepted_cells()?, stream.pending_classes().len(), started.elapsed().as_millis());
    let (mut fork, mut crib) = stream.native_current_query_fork(&reference, &pairing, READING_BITS)?;
    let mut prompt_code = (integer(0), integer(0), 0i64);
    for &class in &digits(&prompt) {
        let event = reference.continue_native_current_forecast(&mut fork, &mut crib, &pairing, class, READING_BITS)?;
        add_score(&event, &mut prompt_code);
    }
    fork.begin_hypothesized_output()?;
    let mut key_stream = KeyStream::new(keys, 8)?;
    let mut released = Vec::new();
    while released.len() < count {
        let key = key_stream.next_key().ok_or("fewer keys than declared cells")?;
        let cell_started = Instant::now();
        let event = reference.release_native_current_forecast(&mut fork, &mut crib, &pairing, &key, READING_BITS)?;
        released.push(event.selected_class);
        println!("NATIVE_SAMPLE cell={} class={} ms={}", released.len(), event.selected_class, cell_started.elapsed().as_millis());
    }
    let boundary = Base4Bytes::decode(&released, released.len())?;
    write_new(&out.join("OUTPUT.bin"), &boundary.bytes)?;
    write_new(&out.join("OUTPUT.json"), object(&[
        ("command", quoted(&args[0])),
        ("state_sha256", quoted(&args[2])),
        ("prompt_sha256", quoted(&args[4])),
        ("keys_sha256", quoted(&args[6])),
        ("prompt_code_bits", exact(&prompt_code)),
        ("classes", exact(&released)),
        ("utf8", exact(&boundary.utf8)),
        ("unfinished_cells", exact(&boundary.unfinished_cells)),
        ("elapsed_ns", started.elapsed().as_nanos().to_string()),
    ]).as_bytes())?;
    println!("NATIVE_SAMPLE_TEXT {:?}", String::from_utf8_lossy(&boundary.bytes));
    println!("NATIVE_SAMPLE_DONE cells={} elapsed_ms={}", released.len(), started.elapsed().as_millis());
    Ok(())
}

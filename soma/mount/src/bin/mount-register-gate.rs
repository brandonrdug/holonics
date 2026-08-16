//! mount-register-gate — the first bounded CUDA gate for the §XXXII-c REGISTER.
//!
//! The fixed raw-light lineage is carried through the shared `body::carriage` register mouth on
//! the cpu and through the CUDA `scope_register` shell over the same empty axis-64 standing.
//! OWN begins as the all-zero rank-zero seed inside a declared 64²-cell storage aperture; that
//! aperture is an instrument reservation, never the current's starting or final gauge. The gate
//! compares the complete register header ⊕ reservoir, whole carrier/K row, cumulative term counts,
//! every radiation word, the REGISTER stroke status, and the true terminal cursor.
//!
//! CUDA runs twice from fresh state: uninterrupted (`interior_installment = 0`) and one exact
//! interior move per persistent full-grid relaunch (`interior_installment = 1`). A relaunch is a
//! continuation stroke, not a retry. There is no timeout, attempt count, future-light preflight,
//! or fallback axis. Any CUDA/driver error or recast request prints and stops.

use std::time::Instant;

use body::carriage::{
    carry_register_stroke_with_completion, registered_own_row_is_canonical, LineageStroke,
    RegisterStrokeStatus, WordSpan,
};
use body::manifold::{
    self, carrier_row_words, COMPLETION_KIND, COMPLETION_WORDS, RADIATION_BRICK,
    RADIATION_BRICK_LIVE, RADIATION_CUT, RADIATION_FLAGS, RADIATION_FOLD, RADIATION_FORM,
    RADIATION_GRIP, RADIATION_ROTOR, RADIATION_STEP, RADIATION_WORDS,
};
use body::medium::{RegionalForm, FORM_WORDS};
use body::num::COG_WORDS;
use body::seam::SliceWordSeam;
use mount::cuda::LaunchCensus;
use mount::{
    launch_register_carrier_rebase, Context, DeviceBuffer, Dim3, Module, RegisterCarrierRebase,
    RegisterCarrierRebaseKernel, RegisterScopeArguments, RegisterScopeKernel,
    RegisterScopeSurfaceArguments, RegisterScopeSurfaceKernel, RegisterSpan, Result,
};
use soma_abi::{contact as contact_abi, register as register_abi};

const PTX: &[u8] = include_bytes!("../../soma-kernel-cuda/soma_kernel_cuda.ptx");

const BLOCK: u32 = 64;
const DRIVE: u32 = 137;
const STANDING_AXIS: usize = 64;
const STANDING_CELLS: usize = STANDING_AXIS * STANDING_AXIS;
const CAPACITY_CELLS: usize = 64 * 64;
const DEPTH: usize = 4;
const WHOLE: usize = 0;
const ONE_MOVE: usize = 1;
const PLURAL_COMPLETION_ROWS: usize = 17;
const CONTACT_BLOCK: u32 = body::register::REGISTER;
const CONTACT_RECEIPT_BASE: usize = contact_abi::RECEIPT;
const CONTACT_SURFACE_WORDS: usize = contact_abi::SURFACE_WORDS;
const REGISTER_STATUS_WORDS: usize = register_abi::STATUS_WORDS;
const REGISTER_STATUS_KIND: usize = register_abi::STATUS_KIND;
const REGISTER_STATUS_OLD_AXIS: usize = register_abi::STATUS_OLD_AXIS;
const REGISTER_STATUS_NEW_AXIS: usize = register_abi::STATUS_NEW_AXIS;
const REGISTER_STATUS_COMPLETE: u32 = register_abi::STATUS_COMPLETE;
const REGISTER_STATUS_NEEDS_OWN_RECAST: u32 = register_abi::STATUS_NEEDS_OWN_RECAST;
const REGISTER_STATUS_CONTINUE: u32 = register_abi::STATUS_CONTINUE;
const REGISTER_STATUS_NEEDS_CARRIER_REBASE: u32 = register_abi::STATUS_NEEDS_CARRIER_REBASE;
#[cfg(test)]
const REGISTER_RECAST_INCOMPLETE: u32 = register_abi::RECAST_INCOMPLETE;

/// The exact long continuation fixture already exercised by `mount-scope-gate`.
const LIGHT: &[u8] =
    b"the cat sat on the mat and then it ran to see an old dog who was far too shy \
now the cat sat on the mat again and the dog ran to see the old cat by the mat";

#[derive(Debug, PartialEq, Eq)]
struct RegisterTrace {
    owns: Vec<u32>,
    carriers: Vec<u32>,
    counts: [u64; 4],
    radiation: Vec<u32>,
    completion: Vec<u32>,
    worker_receipts: Vec<u32>,
    status: u32,
    old_axis: u32,
    new_axis: u32,
    phase_mask: u32,
    deepest: usize,
    resumed_deposit: bool,
    launches: usize,
}

fn face(exact: bool) -> &'static str {
    if exact {
        "EXACT"
    } else {
        "MISMATCH"
    }
}

fn packed_light() -> Vec<u32> {
    let mut packed = vec![0u32; LIGHT.len().div_ceil(4)];
    for (at, &octet) in LIGHT.iter().enumerate() {
        packed[at >> 2] |= (octet as u32) << ((at & 3) * 8);
    }
    packed
}

/// `[raw offset, raw count, frame previous, frame current, worldline lo, worldline hi,
/// registered-OWN word offset, capacity cells, carrier word offset, carrier row words]`.
fn lane_row() -> [u32; register_abi::LANE_WORDS] {
    [
        0,
        LIGHT.len() as u32,
        LIGHT[0] as u32,
        LIGHT[1] as u32,
        0,
        0,
        0,
        CAPACITY_CELLS as u32,
        0,
        manifold::carrier_row_words(DEPTH) as u32,
    ]
}

fn stroke(interior_installment: usize, completion_stride: usize) -> LineageStroke {
    LineageStroke::registered(
        STANDING_AXIS as i64,
        STANDING_CELLS,
        CAPACITY_CELLS,
        0,
        LIGHT.len(),
        LIGHT[0] as u32,
        LIGHT[1] as u32,
        0,
        0,
        DRIVE,
        RADIATION_WORDS,
    )
    .with_interior_installment(interior_installment)
    .with_completion_stride(completion_stride)
}

fn own_words() -> usize {
    manifold::OWN_REGISTER_WORDS + CAPACITY_CELLS * manifold::OWN_CELL_WORDS
}

fn cursor(carriers: &[u32]) -> u64 {
    carriers[manifold::CARRIER_CURSOR_LO] as u64
        | ((carriers[manifold::CARRIER_CURSOR_HI] as u64) << 32)
}

fn continuation_face(carriers: &[u32]) -> (u32, usize) {
    let at = manifold::carrier_continuation_base(manifold::carrier_row_depth(carriers.len()));
    let phase = carriers[at + manifold::CARRIER_CONTINUATION_PHASE];
    let depth = carriers[at + manifold::CARRIER_CONTINUATION_DEPTH_LO] as u64
        | ((carriers[at + manifold::CARRIER_CONTINUATION_DEPTH_HI] as u64) << 32);
    (phase, depth as usize)
}

fn observe_continuation(carriers: &[u32], phase_mask: &mut u32, deepest: &mut usize) {
    let (phase, depth) = continuation_face(carriers);
    *phase_mask |= 1u32
        .checked_shl(phase)
        .expect("one carrier continuation phase belongs to the eight-face mask");
    *deepest = (*deepest).max(depth);
}

fn read_register_u64(owns: &[u32], lo: usize, hi: usize) -> u64 {
    owns[lo] as u64 | ((owns[hi] as u64) << 32)
}

fn active_axis(owns: &[u32]) -> usize {
    owns[manifold::OWN_REGISTER_AXIS] as usize
}

fn active_occupancy(owns: &[u32]) -> u64 {
    read_register_u64(
        owns,
        manifold::OWN_REGISTER_OCCUPANCY_LO,
        manifold::OWN_REGISTER_OCCUPANCY_HI,
    )
}

fn register_releases(owns: &[u32]) -> u64 {
    read_register_u64(
        owns,
        manifold::OWN_REGISTER_RELEASES_LO,
        manifold::OWN_REGISTER_RELEASES_HI,
    )
}

fn register_narrows(owns: &[u32]) -> u64 {
    read_register_u64(
        owns,
        manifold::OWN_REGISTER_NARROWS_LO,
        manifold::OWN_REGISTER_NARROWS_HI,
    )
}

fn active_live_cells(owns: &[u32]) -> Option<u64> {
    let axis = active_axis(owns);
    if axis == 0 || !axis.is_power_of_two() || axis * axis > CAPACITY_CELLS {
        return None;
    }
    let cells = &owns[manifold::OWN_REGISTER_WORDS
        ..manifold::OWN_REGISTER_WORDS + axis * axis * manifold::OWN_CELL_WORDS];
    Some(
        cells
            .chunks_exact(manifold::OWN_CELL_WORDS)
            .filter(|cell| cell[manifold::OWN_CELL_LIVE] != 0)
            .count() as u64,
    )
}

fn active_row_is_nonvacuous(owns: &[u32]) -> bool {
    active_live_cells(owns).is_some_and(|live| live != 0 && live == active_occupancy(owns))
}

fn validate_radiation_row(row: &[u32]) -> std::result::Result<(), &'static str> {
    if row.len() != RADIATION_WORDS {
        return Err("one radiation row has the manifested word extent");
    }
    let flags = row[RADIATION_FLAGS];
    let fold_step = RADIATION_FOLD | RADIATION_STEP;
    let completion = fold_step | RADIATION_CUT | RADIATION_BRICK_LIVE;
    if !matches!(flags, 0 | RADIATION_FOLD) && flags != fold_step && flags != completion {
        return Err("one radiation row carries a canonical AtomEvent flag species");
    }
    if flags & RADIATION_STEP == 0 {
        if row[RADIATION_GRIP..].iter().any(|word| *word != 0) {
            return Err("a row without STEP carries no dormant payload");
        }
        return Ok(());
    }
    if row[RADIATION_GRIP] as usize >= STANDING_CELLS {
        return Err("a stepped grip lies inside the declared standing chart");
    }
    RegionalForm::unpack_compact_checked(row, RADIATION_FORM)
        .map_err(|_| "a stepped row carries one canonical RegionalForm")?;
    if !body::num::packed_cog_is_canonical(row, RADIATION_ROTOR)
        || !body::num::packed_cog_is_canonical(row, RADIATION_ROTOR + COG_WORDS)
    {
        return Err("a stepped row carries two canonical meeting-rotor Cogs");
    }
    let cut = flags & RADIATION_CUT != 0;
    let cross = manifold::unpack_cog(row, RADIATION_ROTOR);
    let aim = manifold::unpack_cog(row, RADIATION_ROTOR + COG_WORDS);
    if cut && cross.mag == 0 && aim.mag == 0 {
        return Err("a cut carries a formed meeting rotor");
    }
    if flags & RADIATION_BRICK_LIVE == 0 {
        if row[RADIATION_BRICK..].iter().any(|word| *word != 0) {
            return Err("a non-completion carries no dormant brick payload");
        }
    } else {
        if !manifold::packed_node_is_canonical(row, RADIATION_BRICK) {
            return Err("a live brick carries one canonical Node");
        }
        if manifold::unpack_node(row, RADIATION_BRICK).len == 0 {
            return Err("a live brick is not the absent node");
        }
    }
    Ok(())
}

fn validate_radiation(radiation: &[u32]) -> std::result::Result<(), String> {
    if radiation.len() != LIGHT.len() * RADIATION_WORDS {
        return Err("the radiation aperture has one row per delivered octet".to_owned());
    }
    if radiation[..RADIATION_WORDS].iter().any(|word| *word != 0) {
        return Err("the lineage's row zero is exact aperture padding".to_owned());
    }
    for (atom, row) in radiation.chunks_exact(RADIATION_WORDS).enumerate() {
        validate_radiation_row(row).map_err(|message| format!("atom {atom}: {message}"))?;
    }
    Ok(())
}

fn radiation_is_nonvacuous(radiation: &[u32]) -> bool {
    let mut folds = false;
    let mut steps = false;
    let mut cuts = false;
    for row in radiation.chunks_exact(RADIATION_WORDS) {
        let flags = row[RADIATION_FLAGS];
        folds |= flags & RADIATION_FOLD != 0;
        steps |= flags & RADIATION_STEP != 0;
        cuts |= flags & RADIATION_CUT != 0;
    }
    folds && steps && cuts
}

fn append_completion(aperture: &[u32], stream: &mut Vec<u32>) {
    for row in aperture.chunks_exact(COMPLETION_WORDS) {
        if row[COMPLETION_KIND] == 0 {
            break;
        }
        stream.extend_from_slice(row);
    }
}

/// The shared cpu/reference lowering. Installment zero finishes in one call; installment one
/// presents the same current again after each carried interior move until the true raw-light end.
fn cpu_reference(interior_installment: usize, completion_rows: usize) -> RegisterTrace {
    let standing = vec![0u32; STANDING_CELLS * FORM_WORDS];
    let packed = packed_light();
    let mut owns = vec![0u32; own_words()];
    let mut carriers = vec![0u32; carrier_row_words(DEPTH)];
    let mut radiation = vec![0u32; LIGHT.len() * RADIATION_WORDS];
    let completion_stride = completion_rows * COMPLETION_WORDS;
    let mut completion_stream = Vec::new();
    let mut counts = [0u64; 4];
    let mut phase_mask = 0u32;
    let mut deepest = 0usize;
    let mut resumed_deposit = false;
    let mut launches = 0usize;

    let (status, old_axis, new_axis) = loop {
        let prior_phase = continuation_face(&carriers).0;
        let mut completion = vec![0u32; completion_stride];
        let carrier_words = carriers.len();
        let result = carry_register_stroke_with_completion::<SliceWordSeam>(
            &standing,
            &mut owns,
            WordSpan::new(0, own_words()),
            &mut carriers,
            WordSpan::new(0, carrier_words),
            &packed,
            &mut radiation,
            WordSpan::new(0, LIGHT.len() * RADIATION_WORDS),
            &mut completion,
            WordSpan::new(0, completion_stride),
            stroke(interior_installment, completion_stride),
        )
        .expect("the bounded registered cpu layout is formed");
        append_completion(&completion, &mut completion_stream);
        launches += 1;
        counts[0] += result.terms.ride;
        counts[1] += result.terms.found_this;
        counts[2] += result.terms.found_that;
        counts[3] += result.terms.dark;
        if manifold::continuation_is_efferent(prior_phase) && result.terms.total() != 0 {
            resumed_deposit = true;
        }
        observe_continuation(&carriers, &mut phase_mask, &mut deepest);
        assert_eq!(result.cursor, cursor(&carriers));
        match result.status {
            RegisterStrokeStatus::NeedsOwnRecast { old_axis, new_axis } => {
                break (REGISTER_STATUS_NEEDS_OWN_RECAST, old_axis, new_axis)
            }
            RegisterStrokeStatus::NeedsCarrierRebase { required_depth } => {
                let required = usize::try_from(required_depth)
                    .expect("the requested carrier depth is cpu-representable");
                let mut fresh = vec![0u32; carrier_row_words(required)];
                body::carriage::rebase_carrier_row(&carriers, &mut fresh)
                    .expect("the cpu remount retains the exact live carrier");
                carriers = fresh;
                continue;
            }
            RegisterStrokeStatus::Continue => continue,
            RegisterStrokeStatus::Complete => {
                assert_eq!(result.cursor, LIGHT.len() as u64);
                break (REGISTER_STATUS_COMPLETE, 0, 0);
            }
        }
    };

    RegisterTrace {
        owns,
        carriers,
        counts,
        radiation,
        completion: completion_stream,
        worker_receipts: Vec::new(),
        status,
        old_axis,
        new_axis,
        phase_mask,
        deepest,
        resumed_deposit,
        launches,
    }
}

/// The CUDA shell has ten `(pointer, length)` buffer pairs:
/// standing · registered OWN · carriers · packed bytes · 10-word lanes · counts · params ·
/// radiation · completion aperture · REGISTER statuses (`kind, old_axis, new_axis` per lane).
#[derive(Clone, Copy)]
enum GateScope<'a, 'm> {
    Inline(&'a RegisterScopeKernel<'m>),
    Surface(&'a RegisterScopeSurfaceKernel<'m>),
}

fn cuda_reference(
    ctx: &Context,
    function: GateScope<'_, '_>,
    carrier_rebase: &RegisterCarrierRebaseKernel<'_>,
    census: LaunchCensus,
    interior_installment: usize,
    completion_rows: usize,
) -> Result<RegisterTrace> {
    let cooperative = matches!(function, GateScope::Surface(_));
    let standing_words = STANDING_CELLS * FORM_WORDS;
    let registered_words = own_words();
    let carrier_words = carrier_row_words(DEPTH);
    let radiation_words = LIGHT.len() * RADIATION_WORDS;
    let completion_words = completion_rows * COMPLETION_WORDS;
    let standing = vec![0u32; standing_words];
    let packed = packed_light();
    let mut lane = lane_row().to_vec();
    let mut params: [u32; 10] = [
        STANDING_AXIS as u32,
        STANDING_CELLS as u32,
        1,
        carrier_words as u32,
        0,
        DRIVE,
        RADIATION_WORDS as u32,
        BLOCK,
        interior_installment as u32,
        completion_words as u32,
    ];

    let standing_b: DeviceBuffer<u32> = DeviceBuffer::alloc(standing_words)?;
    standing_b.copy_from_slice(&standing)?;
    let owns_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(registered_words)?;
    let mut carriers_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(carrier_words)?;
    let bytes_b: DeviceBuffer<u32> = DeviceBuffer::alloc(packed.len())?;
    bytes_b.copy_from_slice(&packed)?;
    let mut lanes_b: DeviceBuffer<u32> = DeviceBuffer::alloc(lane.len())?;
    lanes_b.copy_from_slice(&lane)?;
    let counts_b: DeviceBuffer<u64> = DeviceBuffer::alloc_zeroed(4)?;
    let params_b: DeviceBuffer<u32> = DeviceBuffer::alloc(params.len())?;
    params_b.copy_from_slice(&params)?;
    let radiation_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(radiation_words)?;
    let completion_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(completion_words)?;
    let statuses_b = DeviceBuffer::alloc(REGISTER_STATUS_WORDS)?;
    statuses_b.copy_from_slice(&[u32::MAX, 0, 0])?;
    let contact_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(CONTACT_SURFACE_WORDS)?;

    let mut carriers = vec![0u32; carrier_words];
    let mut counts = [0u64; 4];
    let mut status_words = [0u32; REGISTER_STATUS_WORDS];
    let mut phase_mask = 0u32;
    let mut deepest = 0usize;
    let mut resumed_deposit = false;
    let mut launches = 0usize;
    let mut completion_stream = Vec::new();
    let mut completion_words_cpu = vec![0u32; completion_words];

    loop {
        let prior_phase = continuation_face(&carriers).0;
        let prior_counts = counts;
        // Every relaunch must prove that this invocation reached its terminal status store. A
        // shell/layout rejection returns before that store; retaining the preceding launch's zero
        // would misread the rejected attempt as a completed stroke.
        statuses_b.copy_from_slice(&[u32::MAX, 0, 0])?;
        completion_b.zero()?;
        let arguments = RegisterScopeArguments {
            standing: RegisterSpan::whole(&standing_b),
            owns: RegisterSpan::whole(&owns_b),
            carriers: RegisterSpan::whole(&carriers_b),
            bytes: RegisterSpan::whole(&bytes_b),
            lanes: RegisterSpan::whole(&lanes_b),
            counts: RegisterSpan::whole(&counts_b),
            params: RegisterSpan::whole(&params_b),
            radiation: RegisterSpan::whole(&radiation_b),
            completion: RegisterSpan::whole(&completion_b),
            statuses: RegisterSpan::whole(&statuses_b),
        };
        let block = if cooperative { CONTACT_BLOCK } else { BLOCK };
        match function {
            GateScope::Inline(function) => {
                function.launch(Dim3::x(1), Dim3::x(block), arguments)?
            }
            GateScope::Surface(function) => function.launch(
                Dim3::x(1),
                Dim3::x(block),
                RegisterScopeSurfaceArguments {
                    common: arguments,
                    contact_words: RegisterSpan::whole(&contact_b),
                },
            )?,
        }
        ctx.synchronize()?;
        launches += 1;

        carriers_b.copy_to_slice(&mut carriers)?;
        counts_b.copy_to_slice(&mut counts)?;
        statuses_b.copy_to_slice(&mut status_words)?;
        completion_b.copy_to_slice(&mut completion_words_cpu)?;
        append_completion(&completion_words_cpu, &mut completion_stream);
        let emitted = counts
            .iter()
            .zip(prior_counts)
            .any(|(after, before)| *after != before);
        if manifold::continuation_is_efferent(prior_phase) && emitted {
            resumed_deposit = true;
        }
        observe_continuation(&carriers, &mut phase_mask, &mut deepest);
        if status_words[REGISTER_STATUS_KIND] == REGISTER_STATUS_NEEDS_CARRIER_REBASE {
            let rebased = launch_register_carrier_rebase(
                ctx,
                carrier_rebase,
                census,
                RegisterCarrierRebase {
                    old_carriers: &carriers_b,
                    old_lanes: &lanes_b,
                    old_lane_words: &lane,
                    request_words: &status_words,
                    lane_count: 1,
                },
            )?;
            carriers_b = rebased.carriers;
            lanes_b = rebased.lanes;
            lane = rebased.lane_words;
            params[3] = u32::try_from(carriers_b.len()).expect("the bounded gate row fits its ABI");
            params_b.copy_from_slice(&params)?;
            carriers.resize(carriers_b.len(), 0);
            continue;
        }
        if status_words[REGISTER_STATUS_KIND] == REGISTER_STATUS_CONTINUE {
            continue;
        }
        break;
    }

    let mut owns = vec![0u32; registered_words];
    owns_b.copy_to_slice(&mut owns)?;
    let mut radiation = vec![0u32; radiation_words];
    radiation_b.copy_to_slice(&mut radiation)?;
    let mut worker_receipts = if cooperative {
        vec![0u32; body::register::REGISTER as usize]
    } else {
        Vec::new()
    };
    if cooperative {
        contact_b.copy_range_to_slice(CONTACT_RECEIPT_BASE, &mut worker_receipts)?;
    }
    Ok(RegisterTrace {
        owns,
        carriers,
        counts,
        radiation,
        completion: completion_stream,
        worker_receipts,
        status: status_words[REGISTER_STATUS_KIND],
        old_axis: status_words[REGISTER_STATUS_OLD_AXIS],
        new_axis: status_words[REGISTER_STATUS_NEW_AXIS],
        phase_mask,
        deepest,
        resumed_deposit,
        launches,
    })
}

fn report_words(label: &str, card: &[u32], cpu: &[u32]) {
    if let Some(word) = card.iter().zip(cpu).position(|(card, cpu)| card != cpu) {
        eprintln!(
            "  {label} diverges at word {word}: card {} cpu {}",
            card[word], cpu[word]
        );
    }
}

fn compare(
    tag: &str,
    card: &RegisterTrace,
    cpu: &RegisterTrace,
    stepped: bool,
    cooperative: bool,
) -> bool {
    let owns = card.owns == cpu.owns;
    let carriers = card.carriers == cpu.carriers;
    let counts = card.counts == cpu.counts;
    let radiation = card.radiation == cpu.radiation;
    let completion = card.completion == cpu.completion && !card.completion.is_empty();
    let status = card.status == REGISTER_STATUS_COMPLETE
        && cpu.status == REGISTER_STATUS_COMPLETE
        && card.old_axis == 0
        && card.new_axis == 0
        && card.old_axis == cpu.old_axis
        && card.new_axis == cpu.new_axis;
    let canonical = registered_own_row_is_canonical(&card.owns, CAPACITY_CELLS)
        && active_row_is_nonvacuous(&card.owns)
        && validate_radiation(&card.radiation).is_ok()
        && radiation_is_nonvacuous(&card.radiation);
    let terminal = cursor(&card.carriers) == LIGHT.len() as u64;
    let continuation = !stepped
        || (card.phase_mask == 0xff
            && card.deepest + 1 == manifold::carrier_row_depth(card.carriers.len())
            && manifold::carrier_row_depth(card.carriers.len()) > DEPTH
            && card.resumed_deposit
            && card.launches > 1);
    let worker_width = !cooperative
        || card
            .worker_receipts
            .iter()
            .filter(|receipt| **receipt != 0)
            .count()
            > 1;

    println!(
        "  {tag}: registered OWN {} · register {}/{}/{}/{} · carrier/K {} · counts {} {:?} · radiation {} · completion {} ({} rows) · workers {} {:?} · status {} · canonical {} · cursor {}/{} {} · phase {:#04x} · deepest {} · launches {}",
        face(owns),
        active_axis(&card.owns),
        active_occupancy(&card.owns),
        register_releases(&card.owns),
        register_narrows(&card.owns),
        face(carriers),
        face(counts),
        card.counts,
        face(radiation),
        face(completion),
        card.completion.len() / COMPLETION_WORDS,
        face(worker_width),
        card.worker_receipts,
        face(status),
        face(canonical),
        cursor(&card.carriers),
        LIGHT.len(),
        face(terminal),
        card.phase_mask,
        card.deepest,
        card.launches,
    );
    if !owns {
        report_words("registered OWN", &card.owns, &cpu.owns);
    }
    if !carriers {
        report_words("carrier/K", &card.carriers, &cpu.carriers);
    }
    if !radiation {
        report_words("radiation", &card.radiation, &cpu.radiation);
    }
    if !completion {
        report_words("completion", &card.completion, &cpu.completion);
    }
    owns && carriers
        && counts
        && radiation
        && completion
        && worker_width
        && status
        && canonical
        && terminal
        && continuation
}

fn run() -> Result<()> {
    let started = Instant::now();
    let cpu = cpu_reference(WHOLE, PLURAL_COMPLETION_ROWS);
    let cpu_one_row = cpu_reference(WHOLE, 1);
    assert_eq!(
        cpu.status, REGISTER_STATUS_COMPLETE,
        "the declared gate aperture reaches the fixture's true end"
    );
    assert_eq!(cpu.old_axis, 0);
    assert_eq!(cpu.new_axis, 0);
    assert_eq!(cursor(&cpu.carriers), LIGHT.len() as u64);
    assert!(registered_own_row_is_canonical(&cpu.owns, CAPACITY_CELLS));
    assert!(active_row_is_nonvacuous(&cpu.owns));
    assert_eq!(
        active_axis(&cpu.owns),
        STANDING_AXIS,
        "the fixture forces the register through every declared dyadic digit"
    );
    assert_eq!(
        active_live_cells(&cpu.owns),
        Some(active_occupancy(&cpu.owns))
    );
    assert_eq!(validate_radiation(&cpu.radiation), Ok(()));
    assert!(radiation_is_nonvacuous(&cpu.radiation));

    mount::cuda::init()?;
    let count = mount::Device::count()?;
    if count < 1 {
        eprintln!("FAILED: no CUDA device visible (cuDeviceGetCount == 0)");
        std::process::exit(1);
    }
    let device = mount::Device::get(0)?;
    println!("device: {}", device.name);
    let census = device.launch_census()?;
    let ctx = Context::create(&device)?;
    let module = Module::load_ptx(PTX)?;
    let inline_function = module.register_scope()?;
    let surface_function = module.register_scope_surface()?;
    let carrier_rebase = module.register_carrier_rebase()?;

    println!(
        "fixture: {} raw octets · standing axis {} · OWN capacity {} cells · depth {}",
        LIGHT.len(),
        STANDING_AXIS,
        CAPACITY_CELLS,
        DEPTH
    );
    println!("run: inline chronological foil");
    let run_started = Instant::now();
    let inline = cuda_reference(
        &ctx,
        GateScope::Inline(&inline_function),
        &carrier_rebase,
        census,
        WHOLE,
        PLURAL_COMPLETION_ROWS,
    )?;
    let inline_time = run_started.elapsed();
    println!("run: cooperative plural");
    let run_started = Instant::now();
    let surface = cuda_reference(
        &ctx,
        GateScope::Surface(&surface_function),
        &carrier_rebase,
        census,
        WHOLE,
        PLURAL_COMPLETION_ROWS,
    )?;
    let surface_time = run_started.elapsed();
    println!("run: cooperative one-move");
    let run_started = Instant::now();
    let stepped = cuda_reference(
        &ctx,
        GateScope::Surface(&surface_function),
        &carrier_rebase,
        census,
        ONE_MOVE,
        PLURAL_COMPLETION_ROWS,
    )?;
    let stepped_time = run_started.elapsed();
    println!("run: cooperative one-row completion");
    let run_started = Instant::now();
    let one_row = cuda_reference(
        &ctx,
        GateScope::Surface(&surface_function),
        &carrier_rebase,
        census,
        WHOLE,
        1,
    )?;
    let one_row_time = run_started.elapsed();
    println!("run: cooperative fresh repeat");
    let run_started = Instant::now();
    let repeat = cuda_reference(
        &ctx,
        GateScope::Surface(&surface_function),
        &carrier_rebase,
        census,
        WHOLE,
        PLURAL_COMPLETION_ROWS,
    )?;
    let repeat_time = run_started.elapsed();
    println!(
        "timing: inline {:?} · cooperative {:?} · one-move {:?} · one-row {:?} · repeat {:?}",
        inline_time, surface_time, stepped_time, one_row_time, repeat_time,
    );
    let inline_ok = compare("CUDA inline foil", &inline, &cpu, false, false);
    let surface_ok = compare("CUDA cooperative", &surface, &cpu, false, true);
    let stepped_ok = compare("CUDA cooperative one-move", &stepped, &cpu, true, true);
    let one_row_ok = compare(
        "CUDA cooperative one-row completion",
        &one_row,
        &cpu_one_row,
        false,
        true,
    );
    let repeat_ok = compare("CUDA cooperative repeat", &repeat, &cpu, false, true);

    println!("total: {} us", started.elapsed().as_micros());
    if inline_ok && surface_ok && stepped_ok && one_row_ok && repeat_ok {
        println!("mount register gate: EXACT");
        Ok(())
    } else {
        println!("mount register gate: MISMATCH");
        std::process::exit(1);
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("FAILED: {error}");
        std::process::exit(2);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn recast_lane(word_base: u32, capacity_cells: u32) -> [u32; register_abi::LANE_WORDS] {
        [0, 0, 0, 0, 0, 0, word_base, capacity_cells, 0, 1]
    }

    #[test]
    fn registered_cpu_reference_is_canonical_nonvacuous_and_deterministic() {
        let first = cpu_reference(WHOLE, PLURAL_COMPLETION_ROWS);
        let second = cpu_reference(WHOLE, PLURAL_COMPLETION_ROWS);
        assert_eq!(first, second);
        assert_eq!(first.status, REGISTER_STATUS_COMPLETE);
        assert_eq!(first.old_axis, 0);
        assert_eq!(first.new_axis, 0);
        assert_eq!(cursor(&first.carriers), LIGHT.len() as u64);
        assert!(registered_own_row_is_canonical(&first.owns, CAPACITY_CELLS));
        assert!(active_row_is_nonvacuous(&first.owns));
        assert_eq!(active_axis(&first.owns), STANDING_AXIS);
        assert_eq!(
            active_live_cells(&first.owns),
            Some(active_occupancy(&first.owns))
        );
        assert!(first.carriers.iter().any(|word| *word != 0));
        assert!(first.counts.iter().copied().sum::<u64>() != 0);
        assert_eq!(validate_radiation(&first.radiation), Ok(()));
        assert!(radiation_is_nonvacuous(&first.radiation));
    }

    #[test]
    fn registered_cpu_one_move_is_the_uninterrupted_construction() {
        let whole = cpu_reference(WHOLE, PLURAL_COMPLETION_ROWS);
        let stepped = cpu_reference(ONE_MOVE, PLURAL_COMPLETION_ROWS);
        assert_eq!(stepped.owns, whole.owns);
        assert_eq!(stepped.carriers, whole.carriers);
        assert_eq!(stepped.counts, whole.counts);
        assert_eq!(stepped.radiation, whole.radiation);
        assert_eq!(stepped.completion, whole.completion);
        assert_eq!(stepped.status, REGISTER_STATUS_COMPLETE);
        assert_eq!(stepped.old_axis, 0);
        assert_eq!(stepped.new_axis, 0);
        assert_eq!(stepped.phase_mask, 0xff);
        assert_eq!(
            stepped.deepest + 1,
            manifold::carrier_row_depth(stepped.carriers.len())
        );
        assert!(manifold::carrier_row_depth(stepped.carriers.len()) > DEPTH);
        assert!(stepped.resumed_deposit);
        assert!(stepped.launches > 1);
        assert_eq!(cursor(&stepped.carriers), LIGHT.len() as u64);
        assert!(registered_own_row_is_canonical(
            &stepped.owns,
            CAPACITY_CELLS
        ));
    }

    #[test]
    fn register_recast_abi_names_the_exact_out_of_place_mapping() {
        let source = cpu_reference(WHOLE, PLURAL_COMPLETION_ROWS).owns;
        let old_axis = active_axis(&source) as u32;
        let new_axis = old_axis * 2;
        let old_capacity = old_axis as usize * old_axis as usize;
        let new_capacity = new_axis as usize * new_axis as usize;
        let mut fresh =
            vec![0u32; manifold::OWN_REGISTER_WORDS + new_capacity * manifold::OWN_CELL_WORDS];
        assert_eq!(
            body::carriage::recast_registered_own_row(&source, &mut fresh),
            Some((old_axis, new_axis))
        );

        let old_lanes = recast_lane(0, old_capacity as u32);
        let new_lanes = recast_lane(0, new_capacity as u32);
        let request = [REGISTER_STATUS_NEEDS_OWN_RECAST, old_axis, new_axis];
        let completion = [REGISTER_RECAST_INCOMPLETE];
        let params = [1, old_capacity as u32, BLOCK];
        assert_eq!(old_lanes[6], 0);
        assert_eq!(old_lanes[7], params[1]);
        assert_eq!(new_lanes[6], 0);
        assert_eq!(new_lanes[7], new_capacity as u32);
        assert_eq!(request, [1, old_axis, new_axis]);
        assert_eq!(completion, [u32::MAX]);

        assert_eq!(fresh[manifold::OWN_REGISTER_AXIS], new_axis);
        assert_eq!(
            &fresh[manifold::OWN_REGISTER_OCCUPANCY_LO..manifold::OWN_REGISTER_WORDS],
            &source[manifold::OWN_REGISTER_OCCUPANCY_LO..manifold::OWN_REGISTER_WORDS]
        );
        let mut old_grip = 0usize;
        while old_grip < old_capacity {
            let from = manifold::OWN_REGISTER_WORDS + old_grip * manifold::OWN_CELL_WORDS;
            if source[from + manifold::OWN_CELL_LIVE] != 0 {
                let moved =
                    body::chart::zero_extend_grip(old_grip as u32, old_axis, new_axis) as usize;
                let to = manifold::OWN_REGISTER_WORDS + moved * manifold::OWN_CELL_WORDS;
                assert_eq!(
                    &fresh[to..to + manifold::OWN_CELL_WORDS],
                    &source[from..from + manifold::OWN_CELL_WORDS]
                );
            }
            old_grip += 1;
        }
    }

    #[test]
    fn register_recast_abi_carries_complete_siblings_at_their_own_axis() {
        let source = cpu_reference(WHOLE, PLURAL_COMPLETION_ROWS).owns;
        let axis = active_axis(&source) as u32;
        let capacity = axis as usize * axis as usize;
        let widened_axis = axis * 2;
        let widened_capacity = widened_axis as usize * widened_axis as usize;
        let row_words = source.len();
        let generous_words =
            manifold::OWN_REGISTER_WORDS + widened_capacity * manifold::OWN_CELL_WORDS;
        let mut generous = vec![0u32; generous_words];
        generous[..row_words].copy_from_slice(&source);
        let mut old_flat = Vec::with_capacity(row_words + generous_words);
        old_flat.extend_from_slice(&source);
        old_flat.extend_from_slice(&generous);
        let mut widened =
            vec![0u32; manifold::OWN_REGISTER_WORDS + widened_capacity * manifold::OWN_CELL_WORDS];
        assert_eq!(
            body::carriage::recast_registered_own_row(&source, &mut widened),
            Some((axis, widened_axis))
        );
        let old_lanes = [
            recast_lane(0, capacity as u32),
            recast_lane(row_words as u32, widened_capacity as u32),
        ];
        let new_lanes = [
            recast_lane(0, widened_capacity as u32),
            recast_lane(widened.len() as u32, widened_capacity as u32),
        ];
        let statuses = [
            [REGISTER_STATUS_NEEDS_OWN_RECAST, axis, widened_axis],
            [REGISTER_STATUS_COMPLETE, 0, 0],
        ];
        let completion = [REGISTER_RECAST_INCOMPLETE; 2];
        let mut expected = widened;
        expected.extend_from_slice(&generous);

        let params = [2, widened_capacity as u32, BLOCK];
        assert_eq!(params[0] as usize, old_lanes.len());
        assert_eq!(statuses[0], [1, axis, widened_axis]);
        assert_eq!(statuses[1], [0, 0, 0]);
        assert_eq!(completion, [u32::MAX, u32::MAX]);
        assert_eq!(old_lanes[1][6] as usize, row_words);
        assert_eq!(new_lanes[1][6] as usize, expected.len() - generous_words);
        assert_eq!(new_lanes[1][7], old_lanes[1][7]);
        assert_eq!(&old_flat[row_words..], generous.as_slice());
        assert_eq!(
            &expected[expected.len() - generous_words..],
            generous.as_slice()
        );
    }
}

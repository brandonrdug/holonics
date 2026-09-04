//! mount-register-remount-gate — the bounded fresh-context proof for a pending REGISTER deed.
//!
//! The fixed `bdadada` worldline starts from one exact rank-zero cell. Its first caused carry
//! freezes SUB at 1→2. Its second freezes PATH at 2→4 while PATH_EFFERENT stands. The card snapshot
//! at that second boundary is downloaded whole, its CUDA context is explicitly destroyed, and a
//! fresh context receives only that snapshot and the identical current. Two device recast launches
//! move OWN out-of-place before pending-first carriage resumes. No standing read, receiving fold,
//! integration, or render enters this gate.

use body::carriage::{
    carry_register_stroke, recast_registered_own_row, registered_own_row_is_canonical,
    LineageStroke, RegisterStrokeResult, RegisterStrokeStatus, WordSpan,
};
use body::manifold::{self, TermCounts};
use body::medium::FORM_WORDS;
use body::seam::SliceWordSeam;
use mount::cuda::LaunchCensus;
use mount::{
    launch_register_own_recast, Context, CudaError, Device, DeviceBuffer, Module,
    RegisterOwnRecast, RegisterOwnRecastOutput, RegisterRecastFinishKernel, RegisterRecastKernel,
    RegisterScopeArguments, RegisterScopeKernel, RegisterSpan, Result,
};
use soma_abi::register as register_abi;

const PTX: &[u8] = include_bytes!("../../../../accelerators/cuda-kernel/soma_kernel_cuda.ptx");
const LIGHT: &[u8] = b"bdadada";
const STANDING_AXIS: usize = 16;
const STANDING_CELLS: usize = STANDING_AXIS * STANDING_AXIS;
const DEPTH: usize = 4;
const DRIVE: u32 = 137;

const STATUS_COMPLETE: u32 = register_abi::STATUS_COMPLETE;
const STATUS_NEEDS_OWN_RECAST: u32 = register_abi::STATUS_NEEDS_OWN_RECAST;
const STATUS_CONTINUE: u32 = register_abi::STATUS_CONTINUE;
const STATUS_NEEDS_CARRIER_REBASE: u32 = register_abi::STATUS_NEEDS_CARRIER_REBASE;
const STATUS_INVALID: u32 = register_abi::RECAST_INCOMPLETE;
const STATUS_WORDS: usize = register_abi::STATUS_WORDS;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Snapshot {
    owns: Vec<u32>,
    carrier: Vec<u32>,
    counts: [u64; 4],
    radiation: Vec<u32>,
    packed: Vec<u32>,
    lane: [u32; register_abi::LANE_WORDS],
    status: [u32; STATUS_WORDS],
}

impl Snapshot {
    fn capacity(&self) -> usize {
        (self.owns.len() - manifold::OWN_REGISTER_WORDS) / manifold::OWN_CELL_WORDS
    }
}

#[derive(Clone)]
struct CpuState {
    owns: Vec<u32>,
    carrier: Vec<u32>,
    counts: [u64; 4],
    radiation: Vec<u32>,
    packed: Vec<u32>,
}

#[derive(Clone)]
struct CpuProof {
    sub: Snapshot,
    path: Snapshot,
    path_resumed: Snapshot,
    final_state: Snapshot,
    sibling: Snapshot,
}

fn gate_error(context: &'static str, message: impl Into<String>) -> CudaError {
    CudaError {
        code: -1,
        name: String::from("REGISTER_REMOUNT_GATE"),
        message: message.into(),
        context,
    }
}

fn require(condition: bool, context: &'static str, message: impl Into<String>) -> Result<()> {
    if condition {
        Ok(())
    } else {
        Err(gate_error(context, message))
    }
}

fn packed_light() -> Vec<u32> {
    let mut packed = vec![0u32; LIGHT.len().div_ceil(4)];
    for (at, &octet) in LIGHT.iter().enumerate() {
        packed[at >> 2] |= (octet as u32) << ((at & 3) * 8);
    }
    packed
}

fn own_words(capacity: usize) -> usize {
    manifold::OWN_REGISTER_WORDS + capacity * manifold::OWN_CELL_WORDS
}

fn lane_row(capacity: usize) -> [u32; register_abi::LANE_WORDS] {
    [
        0,
        LIGHT.len() as u32,
        LIGHT[0] as u32,
        LIGHT[1] as u32,
        0,
        0,
        0,
        capacity as u32,
        0,
        manifold::carrier_row_words(DEPTH) as u32,
    ]
}

fn stroke(capacity: usize, installment: usize) -> LineageStroke {
    LineageStroke::registered(
        STANDING_AXIS as i64,
        STANDING_CELLS,
        capacity,
        0,
        LIGHT.len(),
        LIGHT[0] as u32,
        LIGHT[1] as u32,
        0,
        0,
        DRIVE,
        manifold::RADIATION_WORDS,
    )
    .with_interior_installment(installment)
}

fn cursor(carrier: &[u32]) -> u64 {
    carrier[manifold::CARRIER_CURSOR_LO] as u64
        | ((carrier[manifold::CARRIER_CURSOR_HI] as u64) << 32)
}

fn phase(carrier: &[u32]) -> u32 {
    carrier[manifold::carrier_continuation_base(DEPTH) + manifold::CARRIER_CONTINUATION_PHASE]
}

fn pending(carrier: &[u32]) -> u32 {
    manifold::carrier_pending_kind(carrier)
}

fn settled(carrier: &[u32]) -> bool {
    cursor(carrier) == LIGHT.len() as u64
        && phase(carrier) == manifold::CONTINUATION_NONE
        && pending(carrier) == manifold::PENDING_NONE
}

fn add_counts(counts: &mut [u64; 4], terms: TermCounts) {
    counts[0] += terms.ride;
    counts[1] += terms.found_this;
    counts[2] += terms.found_that;
    counts[3] += terms.dark;
}

fn status_words(status: RegisterStrokeStatus) -> [u32; STATUS_WORDS] {
    match status {
        RegisterStrokeStatus::Complete => [STATUS_COMPLETE, 0, 0],
        RegisterStrokeStatus::Continue => [STATUS_CONTINUE, 0, 0],
        RegisterStrokeStatus::NeedsOwnRecast { old_axis, new_axis } => {
            [STATUS_NEEDS_OWN_RECAST, old_axis, new_axis]
        }
        RegisterStrokeStatus::NeedsCarrierRebase { required_depth } => [
            STATUS_NEEDS_CARRIER_REBASE,
            required_depth as u32,
            (required_depth >> 32) as u32,
        ],
    }
}

impl CpuState {
    fn born(capacity: usize) -> CpuState {
        CpuState {
            owns: vec![0u32; own_words(capacity)],
            carrier: vec![0u32; manifold::carrier_row_words(DEPTH)],
            counts: [0; 4],
            radiation: vec![0u32; LIGHT.len() * manifold::RADIATION_WORDS],
            packed: packed_light(),
        }
    }

    fn capacity(&self) -> usize {
        (self.owns.len() - manifold::OWN_REGISTER_WORDS) / manifold::OWN_CELL_WORDS
    }

    fn step(&mut self, installment: usize) -> RegisterStrokeResult {
        let capacity = self.capacity();
        let result = carry_register_stroke::<SliceWordSeam>(
            &vec![0u32; STANDING_CELLS * FORM_WORDS],
            &mut self.owns,
            WordSpan::new(0, own_words(capacity)),
            &mut self.carrier,
            WordSpan::new(0, manifold::carrier_row_words(DEPTH)),
            &self.packed,
            &mut self.radiation,
            WordSpan::new(0, LIGHT.len() * manifold::RADIATION_WORDS),
            stroke(capacity, installment),
        )
        .expect("the bounded cpu REGISTER mouth is formed");
        add_counts(&mut self.counts, result.terms);
        result
    }

    fn recast(&mut self, new_axis: u32) {
        let mut fresh = vec![0u32; own_words(new_axis as usize * new_axis as usize)];
        recast_registered_own_row(&self.owns, &mut fresh)
            .expect("the caused cpu REGISTER digit recasts exactly");
        self.owns = fresh;
    }

    fn snapshot(&self, status: RegisterStrokeStatus) -> Snapshot {
        Snapshot {
            owns: self.owns.clone(),
            carrier: self.carrier.clone(),
            counts: self.counts,
            radiation: self.radiation.clone(),
            packed: self.packed.clone(),
            lane: lane_row(self.capacity()),
            status: status_words(status),
        }
    }
}

fn cpu_proof() -> CpuProof {
    let mut exact = CpuState::born(1);
    let first = exact.step(0);
    assert_eq!(
        first.status,
        RegisterStrokeStatus::NeedsOwnRecast {
            old_axis: 1,
            new_axis: 2,
        }
    );
    assert_eq!(cursor(&exact.carrier), 4);
    assert_eq!(phase(&exact.carrier), manifold::CONTINUATION_NONE);
    assert_eq!(pending(&exact.carrier), manifold::PENDING_SUB);
    let sub = exact.snapshot(first.status);

    exact.recast(2);
    let second = exact.step(0);
    assert_eq!(
        second.status,
        RegisterStrokeStatus::NeedsOwnRecast {
            old_axis: 2,
            new_axis: 4,
        }
    );
    assert_eq!(cursor(&exact.carrier), 6);
    assert_eq!(phase(&exact.carrier), manifold::CONTINUATION_PATH_EFFERENT);
    assert_eq!(pending(&exact.carrier), manifold::PENDING_PATH);
    let path = exact.snapshot(second.status);

    exact.recast(4);
    let before_resume = exact.counts;
    let resumed = exact.step(1);
    assert_eq!(resumed.status, RegisterStrokeStatus::Continue);
    assert_eq!(
        [
            exact.counts[0] - before_resume[0],
            exact.counts[1] - before_resume[1],
            exact.counts[2] - before_resume[2],
            exact.counts[3] - before_resume[3],
        ],
        [0, 0, 1, 0]
    );
    assert_eq!(cursor(&exact.carrier), 6);
    assert_eq!(phase(&exact.carrier), manifold::CONTINUATION_PATH_AFFERENT);
    assert_eq!(pending(&exact.carrier), manifold::PENDING_NONE);
    let path_resumed = exact.snapshot(resumed.status);

    while !settled(&exact.carrier) {
        let result = exact.step(1);
        assert!(matches!(
            result.status,
            RegisterStrokeStatus::Continue | RegisterStrokeStatus::Complete
        ));
    }
    let final_state = exact.snapshot(RegisterStrokeStatus::Complete);

    let mut sibling = CpuState::born(16);
    while !settled(&sibling.carrier) {
        let result = sibling.step(1);
        assert!(matches!(
            result.status,
            RegisterStrokeStatus::Continue | RegisterStrokeStatus::Complete
        ));
    }
    let sibling = sibling.snapshot(RegisterStrokeStatus::Complete);
    assert_eq!(final_state, sibling);
    assert!(registered_own_row_is_canonical(
        &final_state.owns,
        final_state.capacity()
    ));

    CpuProof {
        sub,
        path,
        path_resumed,
        final_state,
        sibling,
    }
}

fn launch_scope(
    context: &Context,
    function: &RegisterScopeKernel<'_>,
    census: LaunchCensus,
    standing: &DeviceBuffer<u32>,
    owns: &DeviceBuffer<u32>,
    carrier: &DeviceBuffer<u32>,
    packed: &DeviceBuffer<u32>,
    lane: &DeviceBuffer<u32>,
    counts: &DeviceBuffer<u64>,
    radiation: &DeviceBuffer<u32>,
    status: &DeviceBuffer<u32>,
    capacity: usize,
    installment: usize,
) -> Result<[u32; STATUS_WORDS]> {
    status.copy_from_slice(&[STATUS_INVALID, 0, 0])?;
    let launch = function.linear_launch(census, 1)?;
    let params = [
        STANDING_AXIS as u32,
        STANDING_CELLS as u32,
        1,
        manifold::carrier_row_words(DEPTH) as u32,
        0,
        DRIVE,
        manifold::RADIATION_WORDS as u32,
        launch.x_stride,
        installment as u32,
        0,
    ];
    let params_b = DeviceBuffer::alloc(params.len())?;
    params_b.copy_from_slice(&params)?;

    let completion = DeviceBuffer::<u32>::alloc_zeroed(1)?;
    function.launch(
        launch.grid,
        launch.block,
        RegisterScopeArguments {
            standing: RegisterSpan::whole(standing),
            owns: RegisterSpan::whole(owns),
            carriers: RegisterSpan::whole(carrier),
            bytes: RegisterSpan::whole(packed),
            lanes: RegisterSpan::whole(lane),
            counts: RegisterSpan::whole(counts),
            params: RegisterSpan::whole(&params_b),
            radiation: RegisterSpan::whole(radiation),
            completion: RegisterSpan::whole(&completion),
            statuses: RegisterSpan::whole(status),
        },
    )?;
    context.synchronize()?;

    let mut returned = [0u32; STATUS_WORDS];
    status.copy_to_slice(&mut returned)?;
    require(
        returned[0] != STATUS_INVALID,
        "launch_scope",
        format!("scope did not publish a terminal status at capacity {capacity}"),
    )?;
    Ok(returned)
}

#[allow(clippy::too_many_arguments)]
/// Cross the shared mount transaction while retaining this gate's independent check that the two
/// CUDA entries leave their request rows unchanged.
fn checked_recast(
    context: &Context,
    cells: &RegisterRecastKernel<'_>,
    finish: &RegisterRecastFinishKernel<'_>,
    census: LaunchCensus,
    old_owns: &DeviceBuffer<u32>,
    fresh_own_words: usize,
    old_lane: &DeviceBuffer<u32>,
    new_lane: &DeviceBuffer<u32>,
    requests: &DeviceBuffer<u32>,
    lane_count: usize,
    max_old_capacity: usize,
) -> Result<RegisterOwnRecastOutput> {
    let mut requests_before = vec![0u32; requests.len()];
    requests.copy_to_slice(&mut requests_before)?;
    let output = launch_register_own_recast(
        context,
        cells,
        finish,
        census,
        RegisterOwnRecast {
            old_owns,
            old_lanes: old_lane,
            new_lanes: new_lane,
            requests,
            lane_count,
            max_old_capacity,
            fresh_own_words,
        },
    )?;
    let mut requests_after = vec![0u32; requests.len()];
    requests.copy_to_slice(&mut requests_after)?;
    require(
        requests_after == requests_before,
        "checked_recast",
        "recast mutated immutable request diagnostics",
    )?;
    Ok(output)
}

#[allow(clippy::too_many_arguments)]
fn download_snapshot(
    owns: &DeviceBuffer<u32>,
    carrier: &DeviceBuffer<u32>,
    counts: &DeviceBuffer<u64>,
    radiation: &DeviceBuffer<u32>,
    packed: &DeviceBuffer<u32>,
    lane: &DeviceBuffer<u32>,
    status: &DeviceBuffer<u32>,
) -> Result<Snapshot> {
    let mut snapshot = Snapshot {
        owns: vec![0u32; owns.len()],
        carrier: vec![0u32; carrier.len()],
        counts: [0; 4],
        radiation: vec![0u32; radiation.len()],
        packed: vec![0u32; packed.len()],
        lane: [0; 10],
        status: [0; STATUS_WORDS],
    };
    owns.copy_to_slice(&mut snapshot.owns)?;
    carrier.copy_to_slice(&mut snapshot.carrier)?;
    counts.copy_to_slice(&mut snapshot.counts)?;
    radiation.copy_to_slice(&mut snapshot.radiation)?;
    packed.copy_to_slice(&mut snapshot.packed)?;
    lane.copy_to_slice(&mut snapshot.lane)?;
    status.copy_to_slice(&mut snapshot.status)?;
    Ok(snapshot)
}

fn compare_snapshot(label: &'static str, card: &Snapshot, cpu: &Snapshot) -> Result<()> {
    require(
        card == cpu,
        "compare_snapshot",
        format!("{label} card construction differs from the cpu construction"),
    )
}

fn upload<T: Copy>(words: &[T]) -> Result<DeviceBuffer<T>> {
    let buffer = DeviceBuffer::alloc(words.len())?;
    buffer.copy_from_slice(words)?;
    Ok(buffer)
}

fn recast_lane(word_base: usize, capacity: usize) -> [u32; register_abi::LANE_WORDS] {
    let mut lane = lane_row(capacity);
    lane[6] = word_base as u32;
    lane
}

fn flatten_lanes(rows: &[[u32; register_abi::LANE_WORDS]]) -> Vec<u32> {
    rows.iter().flat_map(|row| row.iter().copied()).collect()
}

fn card_mixed_recast(device: &Device, census: LaunchCensus, cpu: &CpuProof) -> Result<()> {
    let requested_old = &cpu.sub.owns;
    let mut requested_new = vec![0u32; own_words(4)];
    require(
        recast_registered_own_row(requested_old, &mut requested_new) == Some((1, 2)),
        "card_mixed_recast:cpu_request",
        "cpu failed to form the requested mixed-lane row",
    )?;

    let sibling_active = &cpu.final_state.owns;
    let sibling_capacity = 64usize;
    let mut sibling_generous = vec![0u32; own_words(sibling_capacity)];
    sibling_generous[..sibling_active.len()].copy_from_slice(sibling_active);
    require(
        registered_own_row_is_canonical(&sibling_generous, sibling_capacity),
        "card_mixed_recast:cpu_sibling",
        "the generous completed sibling is not canonical",
    )?;

    let mut old_flat = Vec::with_capacity(requested_old.len() + sibling_generous.len());
    old_flat.extend_from_slice(requested_old);
    old_flat.extend_from_slice(&sibling_generous);
    let mut expected = Vec::with_capacity(requested_new.len() + sibling_generous.len());
    expected.extend_from_slice(&requested_new);
    expected.extend_from_slice(&sibling_generous);
    let old_lanes = flatten_lanes(&[
        recast_lane(0, 1),
        recast_lane(requested_old.len(), sibling_capacity),
    ]);
    let new_lanes = flatten_lanes(&[
        recast_lane(0, 4),
        recast_lane(requested_new.len(), sibling_capacity),
    ]);
    let requests = [STATUS_NEEDS_OWN_RECAST, 1, 2, STATUS_COMPLETE, 0, 0];

    let context = Context::create(device)?;
    let copied = {
        let module = Module::load_ptx(PTX)?;
        let recast = module.register_recast()?;
        let finish = module.register_recast_finish()?;
        let old = upload(&old_flat)?;
        let old_lanes = upload(&old_lanes)?;
        let new_lanes = upload(&new_lanes)?;
        let requests = upload(&requests)?;
        let recast = checked_recast(
            &context,
            &recast,
            &finish,
            census,
            &old,
            expected.len(),
            &old_lanes,
            &new_lanes,
            &requests,
            2,
            sibling_capacity,
        )?;
        require(
            recast.completion == [STATUS_COMPLETE, STATUS_COMPLETE],
            "card_mixed_recast:completion",
            format!(
                "mixed recast left an incomplete lane: {:?}",
                recast.completion
            ),
        )?;
        let mut copied = vec![0u32; expected.len()];
        recast.owns.copy_to_slice(&mut copied)?;
        copied
    };
    context.destroy()?;
    require(
        copied == expected,
        "card_mixed_recast:words",
        "mixed recast fresh OWN differs from cpu at one or more words",
    )
}

fn card_proof(cpu: &CpuProof) -> Result<Snapshot> {
    mount::cuda::init()?;
    let device = Device::get(0)?;
    let census = device.launch_census()?;
    card_mixed_recast(&device, census, cpu)?;

    let path_snapshot = {
        let context = Context::create(&device)?;
        let snapshot = {
            let module = Module::load_ptx(PTX)?;
            let scope = module.register_scope()?;
            let recast = module.register_recast()?;
            let recast_finish = module.register_recast_finish()?;
            let standing = DeviceBuffer::<u32>::alloc_zeroed(STANDING_CELLS * FORM_WORDS)?;
            let mut owns = DeviceBuffer::<u32>::alloc_zeroed(own_words(1))?;
            let carrier = DeviceBuffer::<u32>::alloc_zeroed(manifold::carrier_row_words(DEPTH))?;
            let packed = upload(&packed_light())?;
            let mut lane = upload(&lane_row(1))?;
            let counts = DeviceBuffer::<u64>::alloc_zeroed(4)?;
            let radiation =
                DeviceBuffer::<u32>::alloc_zeroed(LIGHT.len() * manifold::RADIATION_WORDS)?;
            let status = DeviceBuffer::<u32>::alloc(STATUS_WORDS)?;

            let first_status = launch_scope(
                &context, &scope, census, &standing, &owns, &carrier, &packed, &lane, &counts,
                &radiation, &status, 1, 0,
            )?;
            require(
                first_status == [STATUS_NEEDS_OWN_RECAST, 1, 2],
                "card_proof:first",
                format!("expected SUB 1→2 request, got {first_status:?}"),
            )?;
            let sub = download_snapshot(
                &owns, &carrier, &counts, &radiation, &packed, &lane, &status,
            )?;
            compare_snapshot("SUB suspension", &sub, &cpu.sub)?;

            let new_lane = upload(&lane_row(4))?;
            let recast_output = checked_recast(
                &context,
                &recast,
                &recast_finish,
                census,
                &owns,
                own_words(4),
                &lane,
                &new_lane,
                &status,
                1,
                1,
            )?;
            require(
                recast_output.completion == [STATUS_COMPLETE],
                "card_proof:first_recast",
                format!(
                    "first recast completion changed: {:?}",
                    recast_output.completion
                ),
            )?;
            owns = recast_output.owns;
            lane = new_lane;

            let second_status = launch_scope(
                &context, &scope, census, &standing, &owns, &carrier, &packed, &lane, &counts,
                &radiation, &status, 4, 0,
            )?;
            require(
                second_status == [STATUS_NEEDS_OWN_RECAST, 2, 4],
                "card_proof:second",
                format!("expected PATH 2→4 request, got {second_status:?}"),
            )?;
            let path = download_snapshot(
                &owns, &carrier, &counts, &radiation, &packed, &lane, &status,
            )?;
            compare_snapshot("PATH suspension", &path, &cpu.path)?;
            require(
                cursor(&path.carrier) == 6
                    && phase(&path.carrier) == manifold::CONTINUATION_PATH_EFFERENT
                    && pending(&path.carrier) == manifold::PENDING_PATH,
                "card_proof:path_face",
                "the classified PATH suspension face changed",
            )?;
            path
        };
        context.destroy()?;
        snapshot
    };

    let context = Context::create(&device)?;
    let final_snapshot = {
        let module = Module::load_ptx(PTX)?;
        let scope = module.register_scope()?;
        let recast = module.register_recast()?;
        let recast_finish = module.register_recast_finish()?;
        let standing = DeviceBuffer::<u32>::alloc_zeroed(STANDING_CELLS * FORM_WORDS)?;
        let mut owns = upload(&path_snapshot.owns)?;
        let carrier = upload(&path_snapshot.carrier)?;
        let packed = upload(&path_snapshot.packed)?;
        let mut lane = upload(&path_snapshot.lane)?;
        let counts = upload(&path_snapshot.counts)?;
        let radiation = upload(&path_snapshot.radiation)?;
        let status = upload(&path_snapshot.status)?;
        let uploaded = download_snapshot(
            &owns, &carrier, &counts, &radiation, &packed, &lane, &status,
        )?;
        compare_snapshot("fresh-context frozen upload", &uploaded, &path_snapshot)?;

        let new_lane = upload(&lane_row(16))?;
        let recast_output = checked_recast(
            &context,
            &recast,
            &recast_finish,
            census,
            &owns,
            own_words(16),
            &lane,
            &new_lane,
            &status,
            1,
            4,
        )?;
        require(
            recast_output.completion == [STATUS_COMPLETE],
            "card_proof:fresh_recast",
            format!(
                "fresh-context recast completion changed: {:?}",
                recast_output.completion
            ),
        )?;
        owns = recast_output.owns;
        lane = new_lane;

        let before_resume = path_snapshot.counts;
        let resumed_status = launch_scope(
            &context, &scope, census, &standing, &owns, &carrier, &packed, &lane, &counts,
            &radiation, &status, 16, 1,
        )?;
        require(
            resumed_status == [STATUS_CONTINUE, 0, 0],
            "card_proof:path_resume_status",
            format!("PATH resume did not complete one installment: {resumed_status:?}"),
        )?;
        let resumed = download_snapshot(
            &owns, &carrier, &counts, &radiation, &packed, &lane, &status,
        )?;
        compare_snapshot("pending-first PATH resume", &resumed, &cpu.path_resumed)?;
        require(
            [
                resumed.counts[0] - before_resume[0],
                resumed.counts[1] - before_resume[1],
                resumed.counts[2] - before_resume[2],
                resumed.counts[3] - before_resume[3],
            ] == [0, 0, 1, 0]
                && cursor(&resumed.carrier) == 6
                && phase(&resumed.carrier) == manifold::CONTINUATION_PATH_AFFERENT
                && pending(&resumed.carrier) == manifold::PENDING_NONE,
            "card_proof:path_resume_face",
            "pending-first PATH did not emit one found_that and enter PATH_AFFERENT",
        )?;

        let mut current = resumed;
        while !settled(&current.carrier) {
            let returned = launch_scope(
                &context, &scope, census, &standing, &owns, &carrier, &packed, &lane, &counts,
                &radiation, &status, 16, 1,
            )?;
            require(
                (returned[0] == STATUS_CONTINUE || returned[0] == STATUS_COMPLETE)
                    && returned[1..] == [0, 0],
                "card_proof:final_carriage",
                format!("unexpected later recast request {returned:?}"),
            )?;
            current = download_snapshot(
                &owns, &carrier, &counts, &radiation, &packed, &lane, &status,
            )?;
        }
        compare_snapshot("final exact conductor", &current, &cpu.final_state)?;
        compare_snapshot("already-afforded sibling", &current, &cpu.sibling)?;
        current
    };
    context.destroy()?;
    Ok(final_snapshot)
}

fn run() -> Result<()> {
    let cpu = cpu_proof();
    println!(
        "cpu: SUB 1→2 cursor {} · PATH 2→4 cursor {} phase {} · final axis {} counts {:?}",
        cursor(&cpu.sub.carrier),
        cursor(&cpu.path.carrier),
        phase(&cpu.path.carrier),
        cpu.final_state.owns[manifold::OWN_REGISTER_AXIS],
        cpu.final_state.counts,
    );
    let card = card_proof(&cpu)?;
    println!(
        "fresh-context REGISTER remount: EXACT · cursor {} · axis {} · counts {:?}",
        cursor(&card.carrier),
        card.owns[manifold::OWN_REGISTER_AXIS],
        card.counts,
    );
    Ok(())
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

    #[test]
    fn bdadada_pins_sub_then_path_and_resumes_pending_first() {
        let proof = cpu_proof();
        assert_eq!(proof.sub.status, [1, 1, 2]);
        assert_eq!(proof.path.status, [1, 2, 4]);
        assert_eq!(cursor(&proof.path.carrier), 6);
        assert_eq!(
            phase(&proof.path.carrier),
            manifold::CONTINUATION_PATH_EFFERENT
        );
        assert_eq!(proof.path_resumed.status, [STATUS_CONTINUE, 0, 0]);
        assert_eq!(
            phase(&proof.path_resumed.carrier),
            manifold::CONTINUATION_PATH_AFFERENT
        );
        assert_eq!(proof.final_state, proof.sibling);
    }
}

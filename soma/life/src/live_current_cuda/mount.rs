use super::*;

pub(super) fn substrate(error: ::mount::CudaError) -> LiveCurrentError {
    LiveCurrentError::Substrate(error.code)
}

// `ptxas` reports a 5,992-byte `lineage_event` frame and a 520-byte recursive
// `thicken_branch` frame. The driver reports only the entry's local allocation, not the
// unresolved recursive live path. Scalar ingress has a measured 16-KiB floor; an already-complete
// higher-grain constituent has a measured 32-KiB floor. Beyond that floor the reservation follows
// the actually mounted enclosure depth, one physical KiB at a time. This is live apparatus growth,
// not a semantic depth limit or a world-sized worst-case reservation.
pub(super) const LIVE_EVENT_STACK_MIN_BYTES: usize = 16 * 1024;
pub(super) const LIVE_COMPLEX_STACK_MIN_BYTES: usize = 32 * 1024;
const LIVE_EVENT_STACK_PER_ENCLOSURE_BYTES: usize = 1024;

pub(super) fn checked_mul(left: usize, right: usize) -> Result<usize, LiveCurrentError> {
    left.checked_mul(right)
        .ok_or(LiveCurrentError::ResourceReservation)
}

pub(super) fn add_words(counter: &mut u64, words: usize) -> Result<(), LiveCurrentError> {
    *counter = counter
        .checked_add(u64::try_from(words).map_err(|_| LiveCurrentError::ResourceReservation)?)
        .ok_or(LiveCurrentError::ResourceReservation)?;
    Ok(())
}

pub(super) fn upload<T: Copy>(values: &[T]) -> Result<DeviceBuffer<T>, LiveCurrentError> {
    if values.is_empty() {
        return Err(LiveCurrentError::ResourceReservation);
    }
    let buffer = DeviceBuffer::alloc(values.len()).map_err(substrate)?;
    buffer.copy_from_slice(values).map_err(substrate)?;
    Ok(buffer)
}

pub(super) fn next_capacity(current: usize, required: usize) -> Result<usize, LiveCurrentError> {
    let doubled = current
        .checked_mul(2)
        .ok_or(LiveCurrentError::ResourceReservation)?;
    Ok(doubled.max(required).max(current.saturating_add(1)))
}

fn standing_words(standing: &SparseStandingSurface) -> Result<(u32, Vec<u32>), LiveCurrentError> {
    let axis = standing
        .flat_axis()
        .ok_or(LiveCurrentError::UnsupportedStandingRank(standing.rank()))?;
    let cells = standing
        .flat_cells()
        .ok_or(LiveCurrentError::UnsupportedStandingRank(standing.rank()))?;
    let extent = cuda::STANDING_HEADER_WORDS
        .checked_add(checked_mul(cells.len(), cuda::STANDING_ROW_WORDS)?)
        .ok_or(LiveCurrentError::ResourceReservation)?;
    let mut words = Vec::new();
    words
        .try_reserve_exact(extent)
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    words.resize(extent, 0);
    words[cuda::STANDING_CELLS] =
        u32::try_from(cells.len()).map_err(|_| LiveCurrentError::ResourceReservation)?;
    for (row, cell) in cells.iter().copied().enumerate() {
        let at = cuda::STANDING_HEADER_WORDS + row * cuda::STANDING_ROW_WORDS;
        words[at + cuda::STANDING_ROW_GRIP] = cell.grip();
        cell.form().pack(&mut words, at + cuda::STANDING_ROW_FORM);
    }
    debug_assert_eq!(cuda::STANDING_ROW_WORDS, 1 + FORM_WORDS);
    Ok((axis, words))
}

pub(super) fn put_prior_carrier(
    request: CurrentExecutionRequest<'_>,
    max_depth: usize,
    overflow_capacity: usize,
    carrier_words: &mut [u32],
    overflow_words: &mut [u32],
    overflow_counts: &mut [u32],
) -> Result<(), LiveCurrentError> {
    let carrier = request.mount().carrier();
    let depth = carrier.depth();
    let words = depth
        .checked_mul(ENCLOSURE_WORDS)
        .ok_or(LiveCurrentError::ResourceReservation)?;
    carrier_words[..words].copy_from_slice(carrier.words());
    for row in 0..depth {
        let overflow = carrier
            .co_present_overflow(row)
            .ok_or(LiveCurrentError::ExecutionMismatch(request.lineage()))?;
        if overflow.len() > overflow_capacity || row >= max_depth {
            return Err(LiveCurrentError::ResourceReservation);
        }
        overflow_counts[row] =
            u32::try_from(overflow.len()).map_err(|_| LiveCurrentError::ResourceReservation)?;
        for (ordinal, node) in overflow.iter().copied().enumerate() {
            let at = (row * overflow_capacity + ordinal) * NODE_WORDS;
            for word in 0..NODE_WORDS {
                overflow_words[at + word] = node_packed_word(node, word);
            }
        }
    }
    Ok(())
}

pub(super) fn carrier_witness(
    header: Option<LiveBodyHeader>,
    carrier: &GrowingCarrier,
) -> Result<Vec<u32>, LiveCurrentError> {
    let mut overflow_nodes = 0usize;
    for row in 0..carrier.depth() {
        overflow_nodes = overflow_nodes
            .checked_add(
                carrier
                    .co_present_overflow(row)
                    .ok_or(LiveCurrentError::ResourceReservation)?
                    .len(),
            )
            .ok_or(LiveCurrentError::ResourceReservation)?;
    }
    let row_headers = checked_mul(carrier.depth(), 2)?;
    let node_words = checked_mul(overflow_nodes, NODE_WORDS)?;
    let extent = 1usize
        .checked_add(CARRIER_HEADER_WORDS)
        .and_then(|value| value.checked_add(4))
        .and_then(|value| value.checked_add(carrier.words().len()))
        .and_then(|value| value.checked_add(row_headers))
        .and_then(|value| value.checked_add(node_words))
        .ok_or(LiveCurrentError::ResourceReservation)?;
    let mut words = Vec::new();
    words
        .try_reserve_exact(extent)
        .map_err(|_| LiveCurrentError::ResourceReservation)?;
    words.push(header.is_some() as u32);
    match header {
        Some(header) => words.extend_from_slice(header.words()),
        None => words.resize(1 + CARRIER_HEADER_WORDS, 0),
    }
    let depth =
        u64::try_from(carrier.depth()).map_err(|_| LiveCurrentError::ResourceReservation)?;
    words.extend_from_slice(&[depth as u32, (depth >> 32) as u32]);
    let carrier_extent =
        u64::try_from(carrier.words().len()).map_err(|_| LiveCurrentError::ResourceReservation)?;
    words.extend_from_slice(&[carrier_extent as u32, (carrier_extent >> 32) as u32]);
    words.extend_from_slice(carrier.words());
    for row in 0..carrier.depth() {
        let overflow = carrier
            .co_present_overflow(row)
            .ok_or(LiveCurrentError::ResourceReservation)?;
        let count =
            u64::try_from(overflow.len()).map_err(|_| LiveCurrentError::ResourceReservation)?;
        words.extend_from_slice(&[count as u32, (count >> 32) as u32]);
        for node in overflow.iter().copied() {
            for word in 0..NODE_WORDS {
                words.push(node_packed_word(node, word));
            }
        }
    }
    debug_assert_eq!(words.len(), extent);
    Ok(words)
}

pub(super) struct ResidentStanding {
    pub(super) axis: u32,
    pub(super) logical: SparseStandingSurface,
    pub(super) words: usize,
    pub(super) device: DeviceBuffer<u32>,
}

pub(super) struct ResidentCarrier {
    pub(super) witness: Vec<u32>,
    pub(super) depth: usize,
    pub(super) max_depth: usize,
    pub(super) own_capacity: usize,
    pub(super) emission_capacity: usize,
    pub(super) overflow_capacity: usize,
    pub(super) overflow_counts: Vec<usize>,
    pub(super) carrier: DeviceBuffer<u32>,
    pub(super) overflow: DeviceBuffer<u32>,
    pub(super) counts: DeviceBuffer<u32>,
}

pub(super) enum StagedCarrier {
    Continuing(ResidentCarrier),
    Departed,
}

pub(super) struct StagedEvent {
    pub(super) body_key: usize,
    pub(super) revision: u64,
    pub(super) lineages: BTreeMap<CurrentLineage, StagedCarrier>,
}

impl CudaLiveCurrentExecutor {
    pub(super) fn ensure_live_event_stack(
        &mut self,
        source_grain: u32,
        max_depth: usize,
    ) -> Result<(), LiveCurrentError> {
        let floor = if source_grain > 1 {
            LIVE_COMPLEX_STACK_MIN_BYTES
        } else {
            LIVE_EVENT_STACK_MIN_BYTES
        };
        let reached_depth = max_depth.saturating_sub(1);
        let required = reached_depth
            .checked_mul(LIVE_EVENT_STACK_PER_ENCLOSURE_BYTES)
            .and_then(|growth| floor.checked_add(growth))
            .ok_or(LiveCurrentError::ResourceReservation)?;
        if required <= self.stack_limit_bytes {
            return Ok(());
        }
        let before = self.stack_limit_bytes;
        self.stack_limit_bytes = self
            .context
            .ensure_stack_limit_bytes(required)
            .map_err(substrate)?;
        if self.stack_limit_bytes > before {
            self.stack_growths = self
                .stack_growths
                .checked_add(1)
                .ok_or(LiveCurrentError::ResourceReservation)?;
        }
        Ok(())
    }

    pub(super) fn mount_standing(
        &mut self,
        standing: &SparseStandingSurface,
    ) -> Result<ResidentStanding, LiveCurrentError> {
        let (axis, host) = standing_words(standing)?;
        let device = upload(&host)?;
        self.standing_full_mounts = self
            .standing_full_mounts
            .checked_add(1)
            .ok_or(LiveCurrentError::ResourceReservation)?;
        add_words(&mut self.standing_host_words, host.len())?;
        Ok(ResidentStanding {
            axis,
            logical: standing.clone(),
            words: host.len(),
            device,
        })
    }

    pub(super) fn prepare_standing_successor(
        &mut self,
        before: &ResidentStanding,
        successor: &SparseStandingSurface,
    ) -> Result<ResidentStanding, LiveCurrentError> {
        if &before.logical == successor {
            return Err(LiveCurrentError::Standing(
                soma_membrane::SparseStandingError::StandingChanged,
            ));
        }
        let (axis, host) = standing_words(successor)?;
        if axis != before.axis || successor.rank() != before.logical.rank() {
            return self.mount_standing(successor);
        }
        let before_cells =
            before
                .logical
                .flat_cells()
                .ok_or(LiveCurrentError::UnsupportedStandingRank(
                    before.logical.rank(),
                ))?;
        let after_cells = successor
            .flat_cells()
            .ok_or(LiveCurrentError::UnsupportedStandingRank(successor.rank()))?;
        let expected_before = cuda::STANDING_HEADER_WORDS
            .checked_add(checked_mul(before_cells.len(), cuda::STANDING_ROW_WORDS)?)
            .ok_or(LiveCurrentError::ResourceReservation)?;
        if expected_before != before.words {
            return Err(LiveCurrentError::ResourceReservation);
        }

        let device = DeviceBuffer::alloc_zeroed(host.len()).map_err(substrate)?;
        device
            .copy_range_from_slice(0, &host[..cuda::STANDING_HEADER_WORDS])
            .map_err(substrate)?;
        let mut host_words = cuda::STANDING_HEADER_WORDS;
        let mut device_words = 0usize;
        let mut before_at = 0usize;
        for (after_at, after) in after_cells.iter().copied().enumerate() {
            while before_at < before_cells.len() && before_cells[before_at].grip() < after.grip() {
                before_at += 1;
            }
            let destination = cuda::STANDING_HEADER_WORDS + after_at * cuda::STANDING_ROW_WORDS;
            if before_at < before_cells.len()
                && before_cells[before_at].grip() == after.grip()
                && before_cells[before_at].form() == after.form()
            {
                let source = cuda::STANDING_HEADER_WORDS + before_at * cuda::STANDING_ROW_WORDS;
                device
                    .copy_range_from_buffer(
                        destination,
                        &before.device,
                        source,
                        cuda::STANDING_ROW_WORDS,
                    )
                    .map_err(substrate)?;
                device_words = device_words
                    .checked_add(cuda::STANDING_ROW_WORDS)
                    .ok_or(LiveCurrentError::ResourceReservation)?;
            } else {
                device
                    .copy_range_from_slice(
                        destination,
                        &host[destination..destination + cuda::STANDING_ROW_WORDS],
                    )
                    .map_err(substrate)?;
                host_words = host_words
                    .checked_add(cuda::STANDING_ROW_WORDS)
                    .ok_or(LiveCurrentError::ResourceReservation)?;
            }
        }
        add_words(&mut self.standing_host_words, host_words)?;
        add_words(&mut self.standing_device_words, device_words)?;
        Ok(ResidentStanding {
            axis,
            logical: successor.clone(),
            words: host.len(),
            device,
        })
    }
}

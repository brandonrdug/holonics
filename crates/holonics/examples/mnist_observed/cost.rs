//! Observational computation/length readings for the shared MNIST runner.
//!
//! Port `ExactWork` and ring receipts are counted by the native owners. These totals preserve
//! those coordinates, report operator/API call counts separately, and never stand in for machine
//! instructions or allocated memory.
use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

use holonics::hnn::encoding::PortCell;
use holonics::hnn::field::Field;
use holonics::hnn::port::{PortReceipt, ReceiptDetail};
use holonics::hnn::word::work::WorkRead;
use holonics::ratio::Rat;
use holonics::ratio::work::ExactWork;

#[derive(Default)]
pub(super) struct CostLedger {
    runner_events: BTreeMap<&'static str, u128>,
    port_calls: BTreeMap<&'static str, u128>,
    work: BTreeMap<&'static str, ExactWork>,
    ring_ticks: Vec<Rat>,
    source_symbols: BigUint,
    source_fixed_width_bits: BigUint,
    raw_raster_bits: BigUint,
    encoded_cell_payload_bits: BigUint,
    ingested_cells: BigUint,
    source_first_occurrences: BigUint,
    offset_pair_occurrences: BTreeMap<usize, BigUint>,
    code_enclosure_endpoint_bits: BigUint,
    code_enclosure_endpoint_peak_bits: u64,
    native_word_owner_events: WorkRead,
}

impl CostLedger {
    /// Count one exterior operation invocation or an exact number of sub-operations.
    pub(super) fn exterior(&mut self, operation: &'static str, count: u128) {
        *self.runner_events.entry(operation).or_default() += count;
    }

    /// Add the named native Word-owner events recorded on the calling thread during a measured
    /// interval. These are actual owner-call counters, not an estimate of arithmetic or device
    /// instructions. A failed delta is marked overflowed rather than treated as zero work.
    pub(super) fn native_word_work_since(&mut self, before: WorkRead) {
        let after = holonics::hnn::word::work::read();
        match after.since(before) {
            Some(delta) => add_word_work(&mut self.native_word_owner_events, delta),
            None => self.native_word_owner_events.overflowed = true,
        }
    }

    /// Count the actual raster and encoded passage volumes at the exterior boundary. The fixed
    /// width figure is a logical alphabet code length; the PortCell figure is its in-memory
    /// element payload by `size_of`, not a Vec capacity or allocator/RSS reading.
    pub(super) fn encoded_passage(&mut self, symbols: usize, pixels: usize, alphabet: usize) {
        self.exterior("raster_boundary_construct", 1);
        self.exterior("source_chart_encode", 1);
        self.exterior("source_chart_roundtrip_decode", 1);
        self.exterior("paired_source_encode", 1);
        self.source_symbols += BigUint::from(symbols);
        let width = if alphabet <= 1 {
            0
        } else {
            usize::BITS - (alphabet - 1).leading_zeros()
        };
        self.source_fixed_width_bits += BigUint::from(symbols) * BigUint::from(width);
        self.raw_raster_bits += BigUint::from(pixels) * 8u32;
        self.encoded_cell_payload_bits +=
            BigUint::from(symbols) * BigUint::from(std::mem::size_of::<PortCell>()) * 8u32;
    }

    pub(super) fn score_read(&mut self, scores: &super::ClassScores) {
        self.exterior("exact_code_lengths_bulk_call", 1);
        self.exterior(
            "class_code_length_intervals_emitted",
            scores.code_lengths.len() as u128,
        );
        self.exterior("exact_face_mass_maximizer", 1);
        for interval in &scores.code_lengths {
            for endpoint in [&interval.lower, &interval.upper] {
                let width = endpoint.numer().bits() + endpoint.denom().bits();
                self.code_enclosure_endpoint_bits += BigUint::from(width);
                self.code_enclosure_endpoint_peak_bits =
                    self.code_enclosure_endpoint_peak_bits.max(width);
            }
        }
    }

    /// Count the port invocation and merge the exact work/tick readings that the native method
    /// itself returned. For ingest, also count the receipt's actual cells and the source moment's
    /// first/offset occurrence totals implied by its validated count law.
    pub(super) fn port(&mut self, method: &'static str, receipt: &PortReceipt, field: &Field) {
        *self.port_calls.entry(method).or_default() += 1;
        let work = self.work.entry(method).or_default();
        add_work(work, &receipt.work);

        if self.ring_ticks.len() < receipt.rings.regions() {
            self.ring_ticks.resize_with(receipt.rings.regions(), zero);
        }
        for (total, reading) in self.ring_ticks.iter_mut().zip(receipt.rings.readings()) {
            *total = total.clone() + reading;
        }

        if let ReceiptDetail::Ingest { cells, .. } = &receipt.detail {
            let cells = *cells;
            let before = self.ingested_cells.clone();
            let after = &before + BigUint::from(cells);
            let source_count = BigUint::from(field.sources().len());
            self.source_first_occurrences += BigUint::from(cells) * &source_count;
            for &offset in field.offsets() {
                // A carry can split one image across multiple ingest calls, but the moment's
                // offset window continues across those calls. Count the exact increase in the
                // prefix law max(0, n - offset), rather than restarting the window per chunk.
                let offset_value = BigUint::from(offset);
                let before_pairs = if before > offset_value {
                    &before - &offset_value
                } else {
                    BigUint::default()
                };
                let after_pairs = if after > offset_value {
                    &after - &offset_value
                } else {
                    BigUint::default()
                };
                let occurrences = after_pairs - before_pairs;
                *self.offset_pair_occurrences.entry(offset).or_default() +=
                    occurrences * &source_count;
            }
            self.ingested_cells = after;
        }
    }

    pub(super) fn merge(&mut self, other: &Self) {
        for (&name, &count) in &other.runner_events {
            *self.runner_events.entry(name).or_default() += count;
        }
        for (&name, &count) in &other.port_calls {
            *self.port_calls.entry(name).or_default() += count;
        }
        for (&name, value) in &other.work {
            add_work(self.work.entry(name).or_default(), value);
        }
        if self.ring_ticks.len() < other.ring_ticks.len() {
            self.ring_ticks.resize_with(other.ring_ticks.len(), zero);
        }
        for (total, value) in self.ring_ticks.iter_mut().zip(&other.ring_ticks) {
            *total = total.clone() + value;
        }
        self.source_symbols += &other.source_symbols;
        self.source_fixed_width_bits += &other.source_fixed_width_bits;
        self.raw_raster_bits += &other.raw_raster_bits;
        self.encoded_cell_payload_bits += &other.encoded_cell_payload_bits;
        self.ingested_cells += &other.ingested_cells;
        self.source_first_occurrences += &other.source_first_occurrences;
        for (&offset, count) in &other.offset_pair_occurrences {
            *self.offset_pair_occurrences.entry(offset).or_default() += count;
        }
        self.code_enclosure_endpoint_bits += &other.code_enclosure_endpoint_bits;
        self.code_enclosure_endpoint_peak_bits = self
            .code_enclosure_endpoint_peak_bits
            .max(other.code_enclosure_endpoint_peak_bits);
        add_word_work(
            &mut self.native_word_owner_events,
            other.native_word_owner_events,
        );
    }

    pub(super) fn summary(&self, role: &str, image: Option<usize>) -> String {
        let work = self
            .work
            .iter()
            .map(|(&method, value)| {
                let resident_entries = if value.resident_entries.is_zero() {
                    "unreported".to_owned()
                } else {
                    value.resident_entries.to_string()
                };
                (
                    method,
                    format!(
                        "add={} mul={} div={} entries={} cumulative_bits={} peak_bits={} resident_entries={} dependency_span={} width_weighted_rational_ops={}",
                        value.additions,
                        value.multiplications,
                        value.divisions,
                        value.entries_written,
                        value.cumulative_bits,
                        value.peak_bits,
                        resident_entries,
                        value.dependency_span,
                        value.width_weighted_operations(),
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let ring_step_sum = self
            .ring_ticks
            .iter()
            .fold(zero(), |sum, ticks| sum + ticks);
        format!(
            "computation_cost role={role} image={image:?} runner_event_counts={:?} execution_port_calls={:?} exact_work_by_method={work:?} returned_ring_ticks_by_ring={:?} returned_ring_tick_sum={ring_step_sum:?}_sum_of_receipt_coordinates_not_unique_elapsed_ticks native_word_owner_events={:?} source_symbols={} logical_fixed_width_source_bits={} raw_raster_bits={} encoded_PortCell_payload_bits_not_allocation={} ingested_cells={} source_first_count_occurrences={} offset_pair_occurrences={:?} code_enclosure_endpoint_rational_bits={} code_enclosure_endpoint_peak_rational_bits={} exact_work_scope=receipt_producer_counts_are_partial zero_add_mul_div_or_resident_entries_means_not_counted_for_that_method_not_no_underlying_work entries_written_and_bits_cover_only_values_explicitly_passed_to_wrote_all dependency_span_is_method_specific release_close_aeon_discard_producers_return_zero_vector not_a_claim_of_no_underlying_work width_weighted_rational_ops_is_derived_from_recorded_counts_only_not_hardware_instruction_count native_word_owner_scope=calling_thread_named_word_owner_events_only_excludes_device_kernels_and_uninstrumented_arithmetic",
            self.runner_events,
            self.port_calls,
            self.ring_ticks,
            self.native_word_owner_events,
            self.source_symbols,
            self.source_fixed_width_bits,
            self.raw_raster_bits,
            self.encoded_cell_payload_bits,
            self.ingested_cells,
            self.source_first_occurrences,
            self.offset_pair_occurrences,
            self.code_enclosure_endpoint_bits,
            self.code_enclosure_endpoint_peak_bits,
        )
    }
}

fn add_word_work(total: &mut WorkRead, next: WorkRead) {
    macro_rules! add_count {
        ($field:ident) => {
            match total.$field.checked_add(next.$field) {
                Some(value) => total.$field = value,
                None => total.overflowed = true,
            }
        };
    }
    add_count!(material_cut_attempts);
    add_count!(material_cuts);
    add_count!(word_open_attempts);
    add_count!(words_opened);
    add_count!(junction_attempts);
    add_count!(junctions);
    add_count!(full_ticks);
    add_count!(return_attempts);
    add_count!(returns);
    total.overflowed |= next.overflowed;
}

fn add_work(total: &mut ExactWork, next: &ExactWork) {
    total.additions += &next.additions;
    total.multiplications += &next.multiplications;
    total.divisions += &next.divisions;
    total.entries_written += &next.entries_written;
    total.cumulative_bits += &next.cumulative_bits;
    total.peak_bits = total.peak_bits.clone().max(next.peak_bits.clone());
    total.resident_entries = total
        .resident_entries
        .clone()
        .max(next.resident_entries.clone());
    total.dependency_span += &next.dependency_span;
}

pub(super) fn exact_state_summary(
    phase: &str,
    resident: &impl holonics::hnn::reference::ExposedResident,
) -> String {
    let coordinate_storage = resident.constitution().chart_coordinate_storage();
    let coordinate_storage_by_locus = resident.constitution().chart_coordinate_storage_by_locus();
    format!(
        "logical_state phase={phase} resident_state_bits={} resident_state_without_collapse_bits={} retained_constitution_exact_bits={} current_lift={:?} current_lift_component_magnitude_bits={:?} chart_coordinate_storage={coordinate_storage:?} chart_coordinate_storage_by_locus={coordinate_storage_by_locus:?} accounting=logical_state_bits_are_library_defined_and_distinct_from_chart_coordinate_storage; chart_coordinates_are_stored_BigInt_payload_and_vec_descriptors_not_allocator_RAM_RSS_or_device_allocation",
        resident.state_bits(),
        resident.state_bits_without_collapse(),
        resident.constitution().exact_bits(),
        resident.current().lift(),
        resident
            .current()
            .lift()
            .iter()
            .map(|x| x.bits())
            .collect::<Vec<_>>(),
    )
}

pub(super) fn native_word_owner_delta(role: &str, before: WorkRead) -> String {
    let delta = holonics::hnn::word::work::read().since(before);
    format!(
        "native_word_owner_delta role={role} events={delta:?} scope=calling_thread_named_HNN_Word_owner_events_only excludes_device_kernels_and_uninstrumented_arithmetic"
    )
}

pub(super) fn input_storage_summary(
    train_images: &Vec<u8>,
    train_labels: &Vec<u8>,
    test_images: &Vec<u8>,
    test_labels: &Vec<u8>,
) -> String {
    let files = [train_images, train_labels, test_images, test_labels];
    let lengths = files
        .iter()
        .map(|file| file.len() as u128)
        .collect::<Vec<_>>();
    let capacities = [
        train_images.capacity(),
        train_labels.capacity(),
        test_images.capacity(),
        test_labels.capacity(),
    ];
    let disk_octets = lengths.iter().sum::<u128>();
    let host_capacity_octets = capacities.iter().map(|&x| x as u128).sum::<u128>();
    format!(
        "input_volume file_length_octets={lengths:?} file_length_bits={} total_file_length_octets={disk_octets} host_input_Vec_capacity_octets={capacities:?} total_host_input_Vec_capacity_octets={host_capacity_octets} model_checkpoint_serialized_bytes=optional_at_handle_clean_post_training_boundary filesystem_allocated_blocks_allocator_overhead_and_process_RSS=not_measured",
        disk_octets * 8,
    )
}

fn zero() -> Rat {
    Rat::from_integer(BigInt::from(0))
}

#include "r6_artifact.hpp"

#include <cstddef>
#include <ostream>

namespace holonics::tests {
namespace {

void write_snapshot(std::ostream& output,
    const char* kind,
    std::size_t case_slot,
    std::size_t variant,
    const current::weave_snapshot& value) noexcept {
  output << kind << '=' << case_slot << ':' << variant
         << ",head=" << value.head.value()
         << ",incidence=" << value.incidence.value()
         << ",lineage_order=" << value.lineage_order.value()
         << ",logical_used=" << value.logical.used.value()
         << ",logical_capacity=" << value.logical.capacity.value()
         << ",obstruction=" << static_cast<unsigned>(value.obstruction)
         << ",cells=" << value.cell_count << ",events=" << value.event_count << '\n';
  for (std::size_t cell = 0; cell < value.cell_count; ++cell) {
    const auto& item = value.cells[cell];
    output << "cell=" << case_slot << ':' << variant << ':' << cell
           << ",identity=" << item.identity.value()
           << ",value=" << item.value.value()
           << ",morphology=" << item.morphology.value()
           << ",current=" << item.current.value()
           << ",lineage=" << item.lineage.value()
           << ",placement=" << item.placement
           << ",aperture=" << item.aperture << '\n';
  }
  for (std::size_t event = 0; event < value.event_count; ++event) {
    output << "event_return=" << case_slot << ':' << variant << ':' << event
           << ",consequence=" << value.emitted[event].value()
           << ",reservation=" << value.logical.reservations[event].value() << '\n';
  }
}

void write_certificates(std::ostream& output,
    std::size_t case_slot,
    const current::weave_semantic_observation& value) noexcept {
  output << "serial=" << case_slot
         << ",predecessor=" << value.serial.common_predecessor.value()
         << ",first=" << value.serial.first_event.value()
         << ",second=" << value.serial.second_event.value()
         << ",boundary=" << value.serial.retained_boundary.value()
         << ",port_typed=" << value.serial.port_typed
         << ",lineage=" << value.serial.lineage_retained
         << ",chronology=" << value.serial.chronology_retained << '\n'
         << "interchange=" << case_slot
         << ",predecessor=" << value.parallel.common_predecessor.value()
         << ",identity=" << value.parallel.identity_equal
         << ",causal_order=" << value.parallel.causal_order_equal
         << ",incidence=" << value.parallel.incidence_equal
         << ",morphology=" << value.parallel.morphology_equal
         << ",current=" << value.parallel.current_equal
         << ",consequence=" << value.parallel.consequence_equal
         << ",obstruction=" << value.parallel.obstruction_equal
         << ",resource=" << value.parallel.logical_resource_equal
         << ",complete=" << value.parallel.complete_successor_equal << '\n'
         << "coherence=" << case_slot
         << ",adjacent=" << value.coherence.adjacent_interchanges
         << ",braid=" << value.coherence.braid_equal
         << ",complete=" << value.coherence.complete_successors_equal << '\n'
         << "interaction=" << case_slot
         << ",support=" << value.interaction.overlap_support.value()
         << ",law=" << value.interaction.interaction.value()
         << ",combined_value=" << value.interaction.combined_value_delta.value()
         << ",combined_current=" << value.interaction.combined_current.value()
         << ",compatible=" << value.interaction.compatible
         << ",equalized=" << value.interaction.equalized << '\n'
         << "recurrence=" << case_slot
         << ",support=" << value.recurrence.first_support.value()
         << ",repeated=" << value.recurrence.repeated_support
         << ",complete_state=" << value.recurrence.complete_state_recurrence << '\n'
         << "unproved_overlap=" << case_slot
         << ",support=" << value.unproved_overlap.overlap.value()
         << ",interaction=" << value.unproved_overlap.interaction_declared
         << ",ordered=" << value.unproved_overlap.remained_ordered
         << ",obstruction=" << static_cast<unsigned>(value.unproved_overlap.obstruction) << '\n';
}

}  // namespace

void write_r6_artifact(std::ostream& output,
    const apparatus::weave_executor_receipt& execution,
    const apparatus::weave_batch_observation& observation,
    std::size_t failures) noexcept {
  output << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness\n"
         << "program=r6_resident_many_current_weave.sm_89\n"
         << "device_compute_capability=" << execution.device_major << '.'
         << execution.device_minor << '\n'
         << "kernel_launches=" << execution.kernel_launches.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "resident_bytes=" << execution.resident_bytes.value() << '\n'
         << "host_semantic_events=" << execution.host_semantic_events.value() << '\n'
         << "unchanged_retries=" << execution.unchanged_retries.value() << '\n'
         << "case_count=" << observation.count << '\n'
         << "verification_failures=" << failures << '\n';
  for (std::size_t case_slot = 0; case_slot < observation.count; ++case_slot) {
    const auto& value = observation.cases[case_slot];
    output << "case=" << case_slot
           << ",program=" << value.semantic.program_identity.value()
           << ",layers=" << value.semantic.committed_layers
           << ",deltas=" << value.semantic.delta_count
           << ",canonical=" << value.semantic.canonical_commit
           << ",partitions_equal=" << value.partition_successors_equal
           << ",orders_equal=" << value.completion_successors_equal << '\n';
    write_snapshot(output, "predecessor", case_slot, 0, value.semantic.predecessor);
    write_snapshot(output, "successor", case_slot, 0, value.semantic.successor);
    for (std::size_t delta = 0; delta < value.semantic.delta_count; ++delta) {
      const auto& item = value.semantic.deltas[delta];
      output << "delta=" << case_slot << ':' << delta
             << ",predecessor=" << item.predecessor.value()
             << ",event=" << item.event.value()
             << ",input=" << item.input_port.value()
             << ",output=" << item.output_port.value()
             << ",read=" << item.read_support.value()
             << ",change=" << item.change_support.value()
             << ",value=" << item.value_delta.value()
             << ",morphology=" << item.admitted_tally_delta.value()
             << ",current=" << item.successor_current.value()
             << ",consequence=" << item.consequence.value()
             << ",resource=" << item.logical_resource.value()
             << ",lineage=" << item.lineage.value()
             << ",interaction=" << item.interaction.value() << '\n';
    }
    write_certificates(output, case_slot, value.semantic);
    const auto& resource = value.semantic.resource;
    output << "resource_return=" << case_slot
           << ",predecessor=" << resource.predecessor_head.value()
           << ",successor=" << resource.successor_head.value()
           << ",partition=" << resource.partition_before << ':' << resource.partition_after
           << ",aperture=" << resource.aperture_before << ':' << resource.aperture_after
           << ",pressure=" << resource.pressure_returned
           << ",changed=" << resource.morphology_changed
           << ",open=" << resource.remained_open
           << ",retry=" << resource.retry_count
           << ",obstruction=" << static_cast<unsigned>(resource.obstruction) << '\n';
    for (std::size_t variant = 0; variant < current::weave_variant_capacity; ++variant) {
      const auto& item = value.variants[variant];
      output << "realization=" << case_slot << ':' << variant
             << ",partitions=" << item.partition_count
             << ",completion_order=" << item.completion_order
             << ",non_resumable=" << item.non_resumable << '\n';
      write_snapshot(output, "variant_successor", case_slot, variant, item.successor);
    }
  }
}

}  // namespace holonics::tests

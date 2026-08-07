#include "r5_artifact.hpp"

#include <ostream>

namespace holonics::tests {

void write_r5_artifact(std::ostream& output,
    const apparatus::causal_current_executor_receipt& execution,
    const current::current_batch_observation& observation,
    const apparatus::causal_current_executor_receipt& unavailable,
    std::size_t failures) noexcept {
  std::uint64_t total_fronts = 0;
  std::uint64_t total_deltas = 0;
  std::uint64_t detached = 0;
  for (std::size_t slot = 0; slot < observation.count; ++slot) {
    total_fronts += observation.cases[slot].front_count;
    total_deltas += observation.cases[slot].delta_count;
    detached += observation.cases[slot].source_detached ? 1U : 0U;
  }
  output << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness\n"
         << "program=r5_resident_causal_current.sm_89\n"
         << "device_compute_capability=" << execution.device_major << '.'
         << execution.device_minor << '\n'
         << "kernel_launches=" << execution.kernel_launches.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "resident_body_bytes=" << execution.resident_body_bytes.value() << '\n'
         << "case_count=" << observation.count << '\n'
         << "front_count=" << total_fronts << '\n'
         << "delta_count=" << total_deltas << '\n'
         << "source_detached_cases=" << detached << '\n'
         << "serial_state=" << static_cast<unsigned>(observation.cases[0].state) << '\n'
         << "serial_fronts=" << observation.cases[0].front_count << '\n'
         << "serial_successor=" << observation.cases[0].successor.value() << '\n'
         << "serial_quiescent=" << observation.cases[0].compositional_quiescence << '\n'
         << "parallel_state=" << static_cast<unsigned>(observation.cases[1].state) << '\n'
         << "parallel_fronts=" << observation.cases[1].front_count << '\n'
         << "parallel_quiescent=" << observation.cases[1].compositional_quiescence << '\n'
         << "open_state=" << static_cast<unsigned>(observation.cases[2].state) << '\n'
         << "open_front_count=" << observation.cases[2].final_current_count << '\n'
         << "open_current_value=" << observation.cases[2].final_currents[0].local_state.value()
         << '\n'
         << "refusal_state=" << static_cast<unsigned>(observation.cases[3].state) << '\n'
         << "refusal_obstruction=" << static_cast<unsigned>(observation.cases[3].obstruction)
         << '\n'
         << "refusal_predecessor_preserved="
         << (observation.cases[3].predecessor == observation.cases[3].successor) << '\n'
         << "host_semantic_candidates=" << execution.host_semantic_candidates.value() << '\n'
         << "host_oracle_replays=" << execution.host_oracle_replays.value() << '\n'
         << "device_unavailable_state=" << static_cast<unsigned>(unavailable.state) << '\n'
         << "device_unavailable_kernel_launches=" << unavailable.kernel_launches.value() << '\n'
         << "verification_failures=" << failures << '\n';
  for (std::size_t case_slot = 0; case_slot < observation.count; ++case_slot) {
    const auto& value = observation.cases[case_slot];
    output << "case=" << case_slot << ",program=" << value.program_identity.value()
           << ",state=" << static_cast<unsigned>(value.state)
           << ",obstruction=" << static_cast<unsigned>(value.obstruction)
           << ",predecessor=" << value.predecessor.value()
           << ",successor=" << value.successor.value()
           << ",receiver_support=" << value.receiver_support.value()
           << ",touched_support=" << value.touched_support.value()
           << ",fronts=" << value.front_count
           << ",currents=" << value.final_current_count
           << ",deltas=" << value.delta_count
           << ",quiescent=" << value.compositional_quiescence << '\n';
    for (std::size_t front_slot = 0; front_slot < value.front_count; ++front_slot) {
      const auto& front = value.fronts[front_slot];
      output << "front=" << case_slot << ':' << front_slot
             << ",predecessor=" << front.predecessor.value()
             << ",successor=" << front.successor.value()
             << ",event_first=" << front.event_first.value()
             << ",read=" << front.read_support.value()
             << ",change=" << front.change_support.value()
             << ",input=" << front.input_count << ",output=" << front.output_count
             << ",reservations=" << front.reservations
             << ",pending_before=" << front.pending_before
             << ",pending_after=" << front.pending_after << '\n';
    }
    for (std::size_t current_slot = 0;
         current_slot < value.final_current_count; ++current_slot) {
      const auto& active = value.final_currents[current_slot];
      output << "current=" << case_slot << ':' << current_slot
             << ",occurrence=" << active.occurrence.value()
             << ",lineage=" << active.lineage.value()
             << ",site=" << active.site << ",phase=" << active.phase
             << ",state=" << active.local_state.value()
             << ",support=" << active.caused_support.value()
             << ",component=" << static_cast<unsigned>(active.component)
             << ",open=" << active.open << '\n';
    }
    for (std::size_t delta_slot = 0; delta_slot < value.delta_count; ++delta_slot) {
      const auto& delta = value.deltas[delta_slot];
      output << "delta=" << case_slot << ':' << delta_slot
             << ",predecessor=" << delta.predecessor.value()
             << ",event=" << delta.input_event.value()
             << ",read=" << delta.read_support.value()
             << ",change=" << delta.change_support.value()
             << ",incidence=" << delta.incidence_delta
             << ",current=" << delta.successor_current.value()
             << ",return=" << delta.returned_consequence.value()
             << ",stress=" << delta.stress.value()
             << ",obstruction=" << delta.obstruction.value()
             << ",resource=" << delta.logical_resource.value()
             << ",lineage=" << delta.lineage.value() << '\n';
    }
  }
}

}  // namespace holonics::tests

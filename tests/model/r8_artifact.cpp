#include "r8_artifact.hpp"

#include <cstddef>
#include <ostream>

namespace holonics::tests {
namespace {
void write_snapshot(std::ostream& output,
    const char* label,
    std::size_t history,
    const receiver::condensed_snapshot& value) noexcept {
  output << label << '=' << history << ",head=" << value.head.value()
         << ",incidence=" << value.incidence.value()
         << ",current=" << value.current.value()
         << ",lineage=" << value.lineage.value()
         << ",resource=" << value.logical_resource.value()
         << ",alternatives=" << value.alternatives.value()
         << ",obstruction=" << static_cast<unsigned>(value.obstruction)
         << ",source=";
  for (std::size_t slot = 0; slot < value.source_count; ++slot) {
    output << (slot == 0 ? "" : ":") << value.source_identities[slot].value()
           << '/' << value.source_values[slot].value();
  }
  output << '\n';
}

}  // namespace

void write_r8_artifact(std::ostream& output,
    const apparatus::boundary_condensation_executor_receipt& execution,
    const apparatus::boundary_condensation_observation& observation,
    std::size_t failures) noexcept {
  const auto& value = observation.semantic;
  output << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness\n"
         << "program=r8_stateful_boundary_condensation.sm_89\n"
         << "device_compute_capability=" << execution.device_major << '.'
         << execution.device_minor << '\n'
         << "kernel_launches=" << execution.kernel_launches.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "resident_bytes=" << execution.resident_bytes.value() << '\n'
         << "host_semantic_events=" << execution.host_semantic_events.value() << '\n'
         << "program_identity=" << value.program_identity.value() << '\n'
         << "history_count=" << value.history_count << '\n'
         << "factorized_boundary=" << value.factorized_boundary << '\n'
         << "stateful_bisimulation=" << value.stateful_bisimulation << '\n'
         << "source_fiber_retained=" << value.source_fiber_retained << '\n'
         << "non_resumable=" << value.non_resumable << '\n'
         << "verification_failures=" << failures << '\n';
  write_snapshot(output, "predecessor", 0, value.predecessor);
  for (std::size_t slot = 0; slot < value.history_count; ++slot) {
    const auto& step = value.history[slot];
    output << "history=" << slot << ",input=" << step.input_occurrence.value()
           << ",port=" << step.input_port.value()
           << ",predecessor=" << step.common_predecessor.value()
           << ",family=" << step.response.family.value()
           << ",version=" << step.response.version.value()
           << ",query=" << step.response.query.value()
           << ",language=" << step.direct_input_language.value() << ':'
           << step.condensed_input_language.value()
           << ",response=" << step.response.direct.value() << ':'
           << step.response.factorized.value()
           << ",factors=" << step.response.factor_count
           << ",exact=" << step.response.exact
           << ",complete=" << step.complete_successor_equal << '\n';
    write_snapshot(output, "direct_successor", slot, step.direct_successor);
    write_snapshot(output, "condensed_successor", slot, step.condensed_successor);
  }
  const auto& refinement = value.refinement;
  output << "refinement=occurrence:" << refinement.occurrence.value()
         << ",head=" << refinement.predecessor.value() << ':'
         << refinement.successor.value() << ",family="
         << refinement.old_family.value() << '/' << refinement.old_version.value() << ':'
         << refinement.new_family.value() << '/' << refinement.new_version.value()
         << ",groups=" << refinement.old_group_count << ':' << refinement.new_group_count
         << ",capability=" << refinement.reconstruction_capability.value()
         << ",grew=" << refinement.family_grew
         << ",reopened=" << refinement.source_reopened
         << ",reconstructed=" << refinement.exact_reconstruction
         << ",fiber=" << refinement.retained_fiber << '\n';
  write_snapshot(output, "successor", value.history_count, value.successor);
}

}  // namespace holonics::tests

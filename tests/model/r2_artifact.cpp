#include "r2_artifact.hpp"

#include <cstdint>
#include <ostream>
#include <string_view>

namespace holonics::tests {
namespace {

[[nodiscard]] std::string_view status_name(structure::structure_status state) noexcept {
  using structure::structure_status;
  switch (state) {
    case structure_status::exact: return "exact";
    case structure_status::capacity_refused: return "capacity_refused";
    case structure_status::identity_refused: return "identity_refused";
    case structure_status::invalid_incidence: return "invalid_incidence";
    case structure_status::invalid_traversal_seed: return "invalid_traversal_seed";
    case structure_status::path_capacity_refused: return "path_capacity_refused";
    case structure_status::departure_blocked: return "departure_blocked";
    case structure_status::invalid_departure: return "invalid_departure";
  }
  return "unknown";
}

}  // namespace

void write_r2_artifact(
    std::ostream& stream,
    const apparatus::structure_executor_receipt& execution,
    const r2_output_batch& outputs,
    std::size_t verification_failures) {
  stream << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness\n"
         << "program=r2_admit_complex_kernel+r2_continue_complex_kernel.sm_89\n"
         << "case_aperture=" << outputs.size() << '\n'
         << "device_compute_capability=" << execution.device_major << '.'
         << execution.device_minor << '\n'
         << "kernel_launches=" << execution.kernel_launches.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "resident_structure_bytes=" << execution.resident_structure_bytes.value() << '\n'
         << "verification_failures=" << verification_failures << '\n';
  for (const auto& output : outputs) {
    stream << "case=" << output.case_identity
           << " admission=" << status_name(output.admission.state)
           << " admitted=" << output.admission.admitted_cells << '/'
           << output.admission.admitted_incidences
           << " boundary=" << output.boundary_checks << '/'
           << output.boundary_failures << '/' << output.boundary_terms_touched
           << " traversal=" << status_name(output.traversal.state) << '/'
           << output.traversal.reachable_cells << '/'
           << output.traversal.touched_cells << '/'
           << output.traversal.touched_incidences << '/'
           << output.traversal.persistent_path_nodes << '/'
           << output.traversal.terminal_path_depth
           << " support_hash=" << output.traversal.support_hash.value() << '/'
           << output.traversal.terminal_path_hash.value()
           << " append=" << status_name(output.delta.append_state) << '/'
           << output.delta.added_cells
           << " departure=" << status_name(output.delta.departure_state) << '/'
           << output.delta.removed_cells << '/' << output.delta.removed_incidences
           << " active=" << output.active_cells_before << '/' << output.active_cells_after
           << " standing=" << output.predecessor_hash.value() << '/'
           << output.successor_hash.value()
           << " mint=" << output.occurrence_mint_before.value() << '/'
           << output.occurrence_mint_after.value() << " visited=";
    for (const std::uint64_t identity : output.visited_identities) {
      stream << identity << ',';
    }
    stream << '\n';
  }
}

}  // namespace holonics::tests

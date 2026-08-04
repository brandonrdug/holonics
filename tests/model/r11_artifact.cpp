#include "r11_artifact.hpp"

#include <cstddef>
#include <ostream>

namespace holonics::tests {
namespace {

void write_neighborhood(std::ostream& output, const char* label,
    const organ::mathematical_neighborhood_receipt& value) noexcept {
  output << label << "=question:" << value.question.identity.value()
         << ",head=" << value.body_head.value()
         << ",environment=" << value.environment.value()
         << ",type=" << value.intersection_type.value()
         << ",declarations=" << value.declaration_count
         << ",dependencies=" << value.dependency_count
         << ",joins=" << value.dependency_joins
         << ",alternatives=" << value.transport_alternatives
         << ",substitutions=" << value.substitutions
         << ",unknowns=" << value.unknown_count
         << ",global_scans=" << value.global_declaration_scans
         << ",proof=" << value.proof_term.value()
         << ",closed=" << value.proof_structurally_closed
         << ",inherited=" << value.inherited_checked_example
         << ",goal_open=" << value.goal_open
         << ",source_detached=" << value.source_detached
         << ",text_answer=" << value.theorem_text_used_as_answer
         << ",obstruction=" << static_cast<unsigned>(value.obstruction) << '\n';
}

}  // namespace

void write_r11_artifact(std::ostream& output,
    const apparatus::mathematical_ecology_executor_receipt& execution,
    const apparatus::mathematical_ecology_observation& value,
    const apparatus::mathematical_source_receipt& original,
    const apparatus::mathematical_source_receipt& relocated,
    bool exact_material,
    bool sources_detached,
    std::size_t failures) noexcept {
  output << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness\n"
         << "program=r11_mathematical_occurrence_ecology.sm_89\n"
         << "device_compute_capability=" << execution.device_major << '.' << execution.device_minor << '\n'
         << "kernel_launches=" << execution.kernel_launches.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "resident_bytes=" << execution.resident_bytes.value() << '\n'
         << "source_bytes_after_mount=" << execution.source_bytes_after_mount.value() << '\n'
         << "host_semantic_events=" << execution.host_semantic_events.value() << '\n'
         << "verification_failures=" << failures << '\n'
         << "sources=original_bytes:" << original.byte_count
         << ",relocated_bytes=" << relocated.byte_count
         << ",original_chunks=" << original.chunk_count
         << ",relocated_chunks=" << relocated.chunk_count
         << ",material=" << original.material_testimony
         << ':' << relocated.material_testimony
         << ",paths=" << original.path_testimony << ':' << relocated.path_testimony
         << ",recognized=" << original.recognized_declarations
         << ",exact_material=" << exact_material
         << ",detached=" << sources_detached << '\n';
  write_neighborhood(output, "held_out", value.canonical);
  write_neighborhood(output, "reordered", value.reordered);
  write_neighborhood(output, "mismatch", value.mismatch);
  write_neighborhood(output, "unsolved", value.unsolved);
  output << "ecology=storage_invariant:" << value.storage_order_invariant
         << ",material_invariant=" << value.exact_material_comparison
         << ",local_incidence=" << value.local_incidence_only
         << ",continuations=" << value.final_continuations_valid << '\n'
         << "declaration_ids=";
  for (std::size_t slot = 0; slot < value.canonical.declaration_count; ++slot) {
    if (slot != 0) { output << ','; }
    output << value.canonical.declaration_ids[slot].value();
  }
  output << '\n';
}

}  // namespace holonics::tests

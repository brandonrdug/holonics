#include "r13_artifact.hpp"

#include <ostream>

namespace holonics::tests {

void write_r13_artifact(std::ostream& output,
    const apparatus::lean_checker_executor_receipt& execution,
    const event::checker_observation& value,
    std::size_t failures) noexcept {
  const auto& process = execution.process;
  const auto& environment = process.environment;
  const auto& raw = value.raw;
  const auto& typed = value.typed;
  const auto& morphology = value.morphology;
  output << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness\n"
         << "program=r13_lean_exterior_checker.sm_89\n"
         << "device_compute_capability=" << execution.device_major << '.'
         << execution.device_minor << '\n'
         << "kernel_launches=" << execution.kernel_launches.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "resident_bytes=" << execution.resident_bytes.value() << '\n'
         << "host_semantic_events=" << execution.host_semantic_events.value() << '\n'
         << "verification_failures=" << failures << '\n'
         << "environment=toolchain_fold:" << environment.toolchain_fold
         << ",manifest_fold=" << environment.lake_manifest_fold
         << ",lake_fold=" << environment.lake_executable_fold
         << ",lean_fold=" << environment.lean_executable_fold
         << ",lean_4_27=" << environment.pinned_lean_4_27
         << ",mathlib_revision=" << environment.pinned_mathlib_revision << '\n'
         << "invocation=identity:" << process.invocation.value()
         << ",name=lake env lean -o <artifact> <source>"
         << ",calls=" << process.exterior_process_calls.value()
         << ",source_bytes=" << process.source_bytes.value()
         << ",stdout_bytes=" << process.stdout_bytes.value()
         << ",stderr_bytes=" << process.stderr_bytes.value()
         << ",produced_bytes=" << process.produced_artifact_bytes.value() << '\n'
         << "pending=predecessor:" << value.outbound.predecessor.value()
         << ",event=" << value.outbound.event.value()
         << ",occurrence=" << value.outbound.occurrence.value()
         << ",passage=" << value.outbound.passage.value()
         << ",before=" << value.pending_before_process
         << ",after=" << value.pending_after_return << '\n'
         << "raw=exit:" << raw.exit_status << ",launched=" << raw.launched
         << ",exited=" << raw.exited << ",source_fold=" << raw.source_fold
         << ",produced_fold=" << raw.produced_artifact_fold << '\n'
         << "typed=state:" << static_cast<unsigned>(typed.state)
         << ",declarations=" << typed.produced_declarations
         << ",remaining_goals=" << typed.remaining_goal_count
         << ",span=" << typed.source_span_begin << ':' << typed.source_span_end
         << ",elaborator=" << typed.elaborator_boundary_crossed
         << ",kernel=" << typed.kernel_boundary_crossed << '\n'
         << "morphology=mathematical:" << morphology.mathematical_before << ':'
         << morphology.mathematical_after << ",codec=" << morphology.codec_before << ':'
         << morphology.codec_after << ",body=" << morphology.commit.admitted_tally_before << ':'
         << morphology.commit.admitted_tally_after
         << ",applied=" << morphology.returned_difference_applied << '\n'
         << "checker_source_begin\n";
  output.write(value.checker_face.bytes, value.checker_face.byte_count);
  output << "checker_source_end\nstdout_begin\n";
  output.write(raw.standard_output, raw.stdout_bytes);
  output << "stdout_end\nstderr_begin\n";
  output.write(raw.standard_error, raw.stderr_bytes);
  output << "stderr_end\n";
}

}  // namespace holonics::tests

#include "r13_verify.hpp"

namespace holonics::tests {

std::size_t r13_verification_failures(
    const apparatus::lean_checker_executor_receipt& execution,
    const event::checker_observation& actual) noexcept {
  std::size_t failures = 0;
  failures += !execution.returned() || execution.kernel_launches != exact::word{3} ||
      execution.launched_threads != exact::word{3} ||
      execution.host_semantic_events != exact::word{0} ||
      execution.logical.reservations_consumed != exact::word{1};
  const auto& process = execution.process;
  failures += !process.returned() || process.invocation != exact::word{160'105} ||
      process.exterior_process_calls != exact::word{1} ||
      process.host_semantic_events != exact::word{0} || !process.named_lake_env_lean ||
      !process.raw_bytes_returned || !process.environment.pinned_lean_4_27 ||
      !process.environment.pinned_mathlib_revision ||
      process.environment.toolchain_bytes == 0 || process.environment.lake_manifest_bytes == 0 ||
      process.environment.lake_executable_bytes == 0 ||
      process.environment.lean_executable_bytes == 0;
  failures += actual.stage != event::checker_stage_status::exact ||
      !actual.pending_before_process || actual.pending_after_return || !actual.passage_preserved ||
      actual.outbound.passage != exact::word{150'100} ||
      actual.checker_face.passage != exact::word{150'100} ||
      actual.checker_face.generated_source != exact::word{123'001};
  const auto& raw = actual.raw;
  failures += !raw.launched || !raw.exited || raw.exit_status != 0 ||
      raw.passage != exact::word{150'100} || raw.source != exact::word{123'001} ||
      raw.stdout_bytes == 0 || raw.stderr_bytes != 0 || raw.produced_artifact_bytes == 0 ||
      raw.source_fold == 0 || raw.produced_artifact_fold == 0;
  const auto& typed = actual.typed;
  failures += typed.state != event::checker_return_status::accepted ||
      typed.passage != exact::word{150'100} || typed.source != exact::word{123'001} ||
      typed.produced_declarations != 1 || typed.remaining_goal_count != 0 ||
      typed.source_span_begin >= typed.source_span_end || !typed.elaborator_boundary_crossed ||
      !typed.kernel_boundary_crossed;
  const auto& morphology = actual.morphology;
  failures += morphology.mathematical_before != 40 || morphology.mathematical_after != 43 ||
      morphology.codec_before != 30 || morphology.codec_after != 32 ||
      morphology.commit.state != body::body_change_status::committed ||
      morphology.commit.predecessor != exact::word{13'001'000} ||
      morphology.commit.successor != exact::word{13'001'001} ||
      morphology.commit.morphology_before != 123 ||
      morphology.commit.morphology_after != 128 ||
      !morphology.returned_difference_applied;
  return failures;
}

}  // namespace holonics::tests

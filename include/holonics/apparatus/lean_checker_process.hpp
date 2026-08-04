#pragma once

#include <cstdint>

#include <holonics/event/checker_return_schema.hpp>

namespace holonics::apparatus {

enum class lean_process_status : std::uint8_t {
  returned,
  invalid_aperture,
  environment_refused,
  source_refused,
  process_refused,
  capture_refused,
  capacity_refused
};

struct lean_environment_manifest final {
  std::uint64_t toolchain_fold{};
  std::uint64_t lake_manifest_fold{};
  std::uint64_t lake_executable_fold{};
  std::uint64_t lean_executable_fold{};
  std::uint32_t toolchain_bytes{};
  std::uint32_t lake_manifest_bytes{};
  std::uint32_t lake_executable_bytes{};
  std::uint32_t lean_executable_bytes{};
  bool pinned_lean_4_27{};
  bool pinned_mathlib_revision{};
};

struct lean_process_configuration final {
  const char* working_directory{};
  const char* toolchain_path{};
  const char* lake_manifest_path{};
  const char* source_path{};
  const char* produced_artifact_path{};
  const char* stdout_path{};
  const char* stderr_path{};
  const char* source_root{};
};

struct lean_source_view final {
  exact::word passage{};
  exact::word generated_source{};
  const char* bytes{};
  std::uint32_t byte_count{};
};

struct lean_process_receipt final {
  lean_process_status state{lean_process_status::invalid_aperture};
  lean_environment_manifest environment{};
  exact::word invocation{};
  exact::word source_bytes{};
  exact::word stdout_bytes{};
  exact::word stderr_bytes{};
  exact::word produced_artifact_bytes{};
  exact::word exterior_process_calls{};
  exact::word host_semantic_events{};
  bool named_lake_env_lean{};
  bool raw_bytes_returned{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == lean_process_status::returned;
  }
};

[[nodiscard]] lean_process_receipt run_lean_checker_process(
    const codec::formal_checker_face& face,
    const event::checker_outbound_occurrence& outbound,
    const lean_process_configuration& configuration,
    event::checker_raw_return& returned) noexcept;

[[nodiscard]] lean_process_receipt run_lean_checker_source(
    const lean_source_view& source,
    const event::checker_outbound_occurrence& outbound,
    const lean_process_configuration& configuration,
    event::checker_raw_return& returned) noexcept;

}  // namespace holonics::apparatus

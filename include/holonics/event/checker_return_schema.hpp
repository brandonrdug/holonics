#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/body/continuing_body.hpp>
#include <holonics/codec/formal_checker_face.hpp>

namespace holonics::event {

inline constexpr std::size_t checker_message_capacity = 4096;

enum class checker_return_status : std::uint8_t {
  accepted,
  rejected,
  remaining_goals,
  process_refused,
  passage_mismatch
};

enum class checker_stage_status : std::uint8_t {
  exact,
  invalid_source,
  continuation_unavailable,
  already_pending
};

struct checker_outbound_occurrence final {
  exact::word predecessor{};
  exact::word event{};
  exact::word occurrence{};
  exact::word outbound_port{};
  exact::word expected_return_port{};
  exact::word lineage{};
  exact::word passage{};
  exact::word source{};
};

struct checker_raw_return final {
  exact::word predecessor{};
  exact::word event{};
  exact::word port{};
  exact::word lineage{};
  exact::word passage{};
  exact::word source{};
  std::int32_t exit_status{-1};
  std::uint16_t stdout_bytes{};
  std::uint16_t stderr_bytes{};
  std::uint32_t produced_artifact_bytes{};
  std::uint64_t source_fold{};
  std::uint64_t produced_artifact_fold{};
  char standard_output[checker_message_capacity]{};
  char standard_error[checker_message_capacity]{};
  bool launched{};
  bool exited{};
};

struct checker_typed_return final {
  checker_return_status state{checker_return_status::process_refused};
  exact::word passage{};
  exact::word source{};
  std::uint16_t produced_declarations{};
  std::uint16_t remaining_goal_count{};
  std::uint16_t message_bytes{};
  std::uint32_t source_span_begin{};
  std::uint32_t source_span_end{};
  bool elaborator_boundary_crossed{};
  bool kernel_boundary_crossed{};
};

struct checker_morphology_return final {
  std::uint64_t mathematical_before{};
  std::uint64_t mathematical_after{};
  std::uint64_t codec_before{};
  std::uint64_t codec_after{};
  body::body_change_receipt commit{};
  /// True only when the exterior return was **accepted** and the commit landed.
  ///
  /// Until 2026-08-06 this read `commit.state == committed` alone, while the
  /// commit fired unconditionally with `delta = accepted ? N : M`. A rejected
  /// return therefore advanced the head, consumed the continuation, and set this
  /// flag exactly as an accepted one did: **the field named "the returned
  /// difference was applied" was insensitive to the returned difference.**
  bool returned_difference_applied{};
};

struct checker_observation final {
  checker_stage_status stage{checker_stage_status::invalid_source};
  checker_outbound_occurrence outbound{};
  codec::formal_checker_face checker_face{};
  checker_raw_return raw{};
  checker_typed_return typed{};
  checker_morphology_return morphology{};
  bool pending_before_process{};
  bool pending_after_return{};
  bool passage_preserved{};
};

} // namespace holonics::event

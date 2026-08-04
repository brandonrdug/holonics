#pragma once

#include <holonics/event/checker_return_schema.hpp>

namespace holonics::event {
namespace checker_normalization_detail {

template<std::size_t Capacity, std::size_t Pattern>
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t count_pattern(
    const char (&bytes)[Capacity], std::uint16_t used, const char (&pattern)[Pattern]) noexcept {
  constexpr std::size_t payload = Pattern - 1U;
  std::uint16_t count = 0;
  if (payload == 0 || used < payload) { return count; }
  for (std::size_t start = 0; start + payload <= used; ++start) {
    bool same = true;
    for (std::size_t slot = 0; slot < payload; ++slot) {
      same = same && bytes[start + slot] == pattern[slot];
    }
    if (same) { ++count; }
  }
  return count;
}

template<std::size_t Capacity, std::size_t Pattern>
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t first_pattern(
    const char (&bytes)[Capacity], std::uint16_t used, const char (&pattern)[Pattern]) noexcept {
  constexpr std::size_t payload = Pattern - 1U;
  if (payload == 0 || used < payload) { return used; }
  for (std::size_t start = 0; start + payload <= used; ++start) {
    bool same = true;
    for (std::size_t slot = 0; slot < payload; ++slot) {
      same = same && bytes[start + slot] == pattern[slot];
    }
    if (same) { return static_cast<std::uint16_t>(start); }
  }
  return used;
}

template<std::size_t Declaration, std::size_t Source>
HOLONICS_CALLABLE constexpr void normalize_named_checker_return(
    const checker_raw_return& raw, const codec::formal_checker_face& face,
    const char (&declaration)[Declaration], const char (&source)[Source],
    checker_typed_return& typed) noexcept {
  constexpr char unsolved[] = "unsolved goals";
  typed.produced_declarations = count_pattern(
      raw.standard_output, raw.stdout_bytes, declaration);
  typed.remaining_goal_count = count_pattern(raw.standard_error, raw.stderr_bytes, unsolved);
  typed.message_bytes = static_cast<std::uint16_t>(raw.stdout_bytes + raw.stderr_bytes);
  typed.source_span_begin = first_pattern(face.bytes, face.byte_count, source);
  typed.source_span_end = typed.source_span_begin == face.byte_count ? face.byte_count :
      static_cast<std::uint16_t>(typed.source_span_begin + Source - 1U);
  typed.elaborator_boundary_crossed = raw.launched && raw.exited;
  typed.kernel_boundary_crossed = raw.exit_status == 0 &&
      typed.remaining_goal_count == 0 && typed.produced_declarations == 1 &&
      raw.produced_artifact_bytes != 0;
  if (!raw.launched || !raw.exited) { typed.state = checker_return_status::process_refused; }
  else if (typed.remaining_goal_count != 0) { typed.state = checker_return_status::remaining_goals; }
  else if (typed.kernel_boundary_crossed) { typed.state = checker_return_status::accepted; }
  else { typed.state = checker_return_status::rejected; }
}

}  // namespace checker_normalization_detail

HOLONICS_CALLABLE constexpr void normalize_checker_return(
    const checker_raw_return& raw, const codec::formal_checker_face& face,
    checker_typed_return& typed) noexcept {
  if (face.declaration_form == codec::formal_declaration_form::reverse_rebase) {
    constexpr char declaration[] = "theorem Soma.Holonics.generated_semantics_rebase_reverse";
    constexpr char source[] = "theorem generated_semantics_rebase_reverse";
    checker_normalization_detail::normalize_named_checker_return(
        raw, face, declaration, source, typed);
    return;
  }
  if (face.declaration_form == codec::formal_declaration_form::composed_trace_rebase) {
    constexpr char declaration[] =
        "theorem Soma.Holonics.generated_trace_rebase_transports_composition";
    constexpr char source[] = "theorem generated_trace_rebase_transports_composition";
    checker_normalization_detail::normalize_named_checker_return(
        raw, face, declaration, source, typed);
    return;
  }
  constexpr char declaration[] =
      "theorem Soma.Holonics.generated_trace_rebase_transports_three";
  constexpr char source[] = "theorem generated_trace_rebase_transports_three";
  checker_normalization_detail::normalize_named_checker_return(
      raw, face, declaration, source, typed);
}

}  // namespace holonics::event

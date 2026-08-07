#pragma once

#include <holonics/codec/geometry_theory_face.hpp>
#include <holonics/event/checker_return_schema.hpp>

namespace holonics::event {
namespace geometry_checker_detail {

template<std::size_t Capacity, std::size_t Pattern>
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t count(
    const char (&bytes)[Capacity], std::uint16_t used, const char (&pattern)[Pattern]) noexcept {
  constexpr std::size_t payload = Pattern - 1U;
  std::uint16_t result = 0;
  for (std::size_t start = 0; payload != 0 && start + payload <= used; ++start) {
    bool same = true;
    for (std::size_t slot = 0; slot < payload; ++slot) {
      same = same && bytes[start + slot] == pattern[slot];
    }
    if (same) { ++result; }
  }
  return result;
}

template<std::size_t Capacity, class Count, std::size_t Pattern>
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t first(
    const char (&bytes)[Capacity], Count used, const char (&pattern)[Pattern]) noexcept {
  constexpr std::size_t payload = Pattern - 1U;
  for (std::size_t start = 0; payload != 0 && start + payload <= used; ++start) {
    bool same = true;
    for (std::size_t slot = 0; slot < payload; ++slot) {
      same = same && bytes[start + slot] == pattern[slot];
    }
    if (same) { return static_cast<std::uint16_t>(start); }
  }
  return static_cast<std::uint16_t>(used);
}

}  // namespace geometry_checker_detail

HOLONICS_CALLABLE constexpr void normalize_geometry_checker_return(
    const checker_raw_return& raw, const codec::geometry_theory_face& face,
    checker_typed_return& typed) noexcept {
  constexpr char declaration[] = "Soma.Holonics.R17.generated_crossRatio_mobius";
  constexpr char source[] = "theorem generated_crossRatio_mobius";
  constexpr char unsolved[] = "unsolved goals";
  typed.produced_declarations = geometry_checker_detail::count(
      raw.standard_output, raw.stdout_bytes, declaration);
  typed.remaining_goal_count = geometry_checker_detail::count(
      raw.standard_error, raw.stderr_bytes, unsolved);
  typed.message_bytes = static_cast<std::uint16_t>(raw.stdout_bytes + raw.stderr_bytes);
  typed.source_span_begin = geometry_checker_detail::first(
      face.bytes, face.byte_count, source);
  typed.source_span_end = static_cast<std::uint16_t>(typed.source_span_begin + sizeof(source) - 1U);
  typed.elaborator_boundary_crossed = raw.launched && raw.exited;
  typed.kernel_boundary_crossed = raw.exit_status == 0 && typed.remaining_goal_count == 0 &&
      typed.produced_declarations == 1 && raw.produced_artifact_bytes != 0;
  if (!raw.launched || !raw.exited) { typed.state = checker_return_status::process_refused; }
  else if (typed.remaining_goal_count != 0) { typed.state = checker_return_status::remaining_goals; }
  else if (typed.kernel_boundary_crossed) { typed.state = checker_return_status::accepted; }
  else { typed.state = checker_return_status::rejected; }
}

}  // namespace holonics::event

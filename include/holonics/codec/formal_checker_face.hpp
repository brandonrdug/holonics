#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/codec/generated_math_face.hpp>

namespace holonics::codec {

inline constexpr std::size_t formal_checker_face_capacity = 1536;

struct formal_checker_face final {
  exact::word identity{};
  exact::word passage{};
  exact::word generated_source{};
  std::uint16_t byte_count{};
  char bytes[formal_checker_face_capacity]{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_formal_checker_face(
    const formal_math_face& source, formal_checker_face& output) noexcept {
  if (source.identity.value() == 0 || source.passage.value() == 0 ||
      source.byte_count == 0 || source.byte_count > formal_math_face_capacity) {
    return false;
  }
  output.identity = exact::word{123'101};
  output.passage = source.passage;
  output.generated_source = source.identity;
  for (std::size_t slot = 0; slot < source.byte_count; ++slot) {
    output.bytes[output.byte_count++] = source.bytes[slot];
  }
  return append_face(output.bytes, output.byte_count,
      "\n#print Soma.Holonics.generated_semantics_rebase_reverse\n") &&
      append_face(output.bytes, output.byte_count,
      "#print axioms Soma.Holonics.generated_semantics_rebase_reverse\n");
}

}  // namespace holonics::codec

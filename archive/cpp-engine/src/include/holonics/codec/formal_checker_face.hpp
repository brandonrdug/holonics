#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/codec/generated_math_face.hpp>

namespace holonics::codec {

inline constexpr std::size_t formal_checker_face_capacity = 1536;

enum class formal_declaration_form : std::uint8_t {
  reverse_rebase = 1,
  composed_trace_rebase = 2,
  returned_fiber_extension = 3
};

struct formal_checker_face final {
  exact::word identity{};
  exact::word passage{};
  exact::word generated_source{};
  formal_declaration_form declaration_form{formal_declaration_form::reverse_rebase};
  std::uint16_t byte_count{};
  char bytes[formal_checker_face_capacity]{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_formal_checker_face(
    const formal_math_face& source, formal_declaration_form declaration_form,
    formal_checker_face& output) noexcept {
  if (source.identity.value() == 0 || source.passage.value() == 0 ||
      source.byte_count == 0 || source.byte_count > formal_math_face_capacity) {
    return false;
  }
  output.identity = exact::word{123'100 + static_cast<std::uint64_t>(declaration_form)};
  output.passage = source.passage;
  output.generated_source = source.identity;
  output.declaration_form = declaration_form;
  for (std::size_t slot = 0; slot < source.byte_count; ++slot) {
    output.bytes[output.byte_count++] = source.bytes[slot];
  }
  if (declaration_form == formal_declaration_form::reverse_rebase) {
    return append_face(output.bytes, output.byte_count,
        "\n#print Soma.Holonics.generated_semantics_rebase_reverse\n") &&
        append_face(output.bytes, output.byte_count,
        "#print axioms Soma.Holonics.generated_semantics_rebase_reverse\n");
  }
  if (declaration_form == formal_declaration_form::composed_trace_rebase) {
    return append_face(output.bytes, output.byte_count,
        "\n#print Soma.Holonics.generated_trace_rebase_transports_composition\n") &&
        append_face(output.bytes, output.byte_count,
        "#print axioms Soma.Holonics.generated_trace_rebase_transports_composition\n");
  }
  if (declaration_form == formal_declaration_form::returned_fiber_extension) {
    return append_face(output.bytes, output.byte_count,
        "\n#print Soma.Holonics.generated_trace_rebase_transports_three\n") &&
        append_face(output.bytes, output.byte_count,
        "#print axioms Soma.Holonics.generated_trace_rebase_transports_three\n");
  }
  return false;
}

}  // namespace holonics::codec

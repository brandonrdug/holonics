#pragma once

#include <holonics/codec/elementary_calculus_face.hpp>
#include <holonics/codec/rederivation_renderer_atoms.hpp>

namespace holonics::codec::elementary_render_detail {

template<class Writer>
HOLONICS_CALLABLE inline bool boolean(Writer &out, bool value) noexcept {
  return out.text(value ? "true" : "false");
}

template<class Writer>
HOLONICS_CALLABLE inline bool integer_list(Writer &out, const std::int64_t *values,
    std::uint8_t count) noexcept {
  if (!out.text("[")) return false;
  for (std::uint8_t i = 0; i < count; ++i) {
    if (i != 0 && !out.text(", ")) return false;
    if (!out.integer(values[i])) return false;
  }
  return out.text("]");
}

template<class Writer>
HOLONICS_CALLABLE inline bool matrix(Writer &out,
    const elementary_matrix2_surface &value) noexcept {
  return out.text("{") && out.text("a := ") && out.integer(value.value[0]) &&
      out.text(", b := ") && out.integer(value.value[1]) &&
      out.text(", c := ") && out.integer(value.value[2]) &&
      out.text(", d := ") && out.integer(value.value[3]) && out.text("}");
}

template<class Writer>
HOLONICS_CALLABLE inline bool rational(Writer &out, exact::small_rational value) noexcept {
  return out.text("((") && out.integer(value.numerator) && out.text(" : ℚ) / ") &&
      out.integer(value.denominator) && out.text(")");
}

template<class Writer>
HOLONICS_CALLABLE inline bool occurrence(Writer &out, const std::uint64_t *fields) noexcept {
  return out.text("{") && out.text("owner := ") && out.natural(fields[0]) &&
      out.text(", predecessor := ") && out.natural(fields[1]) &&
      out.text(", event := ") && out.natural(fields[2]) &&
      out.text(", port := ") && out.natural(fields[3]) &&
      out.text(", lineage := ") && out.natural(fields[4]) && out.text("}");
}

}  // namespace holonics::codec::elementary_render_detail

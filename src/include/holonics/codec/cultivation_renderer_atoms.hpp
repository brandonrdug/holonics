#pragma once

#include <holonics/codec/rederivation_renderer_atoms.hpp>

namespace holonics::codec::cultivation_render_detail {

template<class Writer>
HOLONICS_CALLABLE inline bool rational(Writer &out,
                                       exact::small_rational value) noexcept {
  return out.text("((") && out.integer(value.numerator) &&
      out.text(" : ℚ) / ") && out.integer(value.denominator) && out.text(")");
}

template<class Writer>
HOLONICS_CALLABLE inline bool kernel_list(
    Writer &out, const cultivated_kernel_surface &organ) noexcept {
  if (!out.text("[")) return false;
  for (std::uint8_t i = 0; i < organ.features; ++i) {
    if (i != 0 && !out.text(", ")) return false;
    if (!out.integer(organ.coefficients[i])) return false;
  }
  return out.text("]");
}

}  // namespace holonics::codec::cultivation_render_detail

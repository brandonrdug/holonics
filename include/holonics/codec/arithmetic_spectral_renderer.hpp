#pragma once

#include <holonics/codec/arithmetic_spectral_renderer_bundle.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE inline bool render_arithmetic_spectral(
    const arithmetic_spectral_surface& source, arithmetic_formal_face& out) noexcept {
  return arithmetic_render_detail::render_arithmetic_bundle(source, out);
}

}  // namespace holonics::codec

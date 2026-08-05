#pragma once

#include <holonics/codec/hodge_realization_renderer_bundle.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_hodge_realization(
    const hodge_realization_surface& source, hodge_formal_face& out) noexcept {
  return hodge_render_detail::render_hodge_bundle(source, out);
}

}  // namespace holonics::codec

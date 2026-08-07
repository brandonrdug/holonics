#pragma once

#include <holonics/codec/trace_rebase_renderer_atoms.hpp>

namespace holonics::codec {
namespace heldout_trace_rebase_render_detail {
template <class Writer>
HOLONICS_CALLABLE inline bool chart(Writer &out, const std::int64_t *values) noexcept {
  constexpr const char *field[7]{"a", "b", "c", "d", "e", "f", "t"};
  if (!out.text("{"))
    return false;
  for (std::uint8_t i = 0; i < 7; ++i) {
    if (i != 0 && !out.text(","))
      return false;
    if (!out.text(field[i]) || !out.text(":=") || !out.integer(values[i]))
      return false;
  }
  return out.text("}");
}
} // namespace heldout_trace_rebase_render_detail

HOLONICS_CALLABLE inline bool render_heldout_trace_rebase(
    const heldout_trace_rebase_surface &surface,
    trace_rebase_formal_face &face) noexcept {
  using rederivation_render_detail::writer;
  using heldout_trace_rebase_render_detail::chart;
  writer out{face};
  face.identity = exact::word{202'411};
  face.passage = surface.passage;
  if (!surface.exact || !surface.prediction_before_comparison ||
      !out.text("import R35_TRACE_CHARACTER_REBASES\n\nnamespace Soma.Holonics.R35\n\n"
                "def held0 : TraceChart := ") ||
      !chart(out, surface.predicted[0]) || !out.text("\n"))
    return false;
  for (std::uint8_t step = 0; step < surface.path_length; ++step) {
    if (!out.text("def held") || !out.natural(step + 1U) ||
        !out.text(" : TraceChart := applyRebase") ||
        !out.natural(surface.moves[step]) || !out.text(" held") ||
        !out.natural(step) || !out.text("\n"))
      return false;
  }
  if (!out.text("def heldSource : TraceChart := ") ||
      !chart(out, surface.source[surface.path_length]) ||
      !out.text("\n\ntheorem heldoutTraceRebaseTransport : held") ||
      !out.natural(surface.path_length) ||
      !out.text(" = heldSource := by\n  norm_num [heldSource, held0"))
    return false;
  for (std::uint8_t step = 1; step <= surface.path_length; ++step)
    if (!out.text(", held") || !out.natural(step))
      return false;
  if (!out.text(", applyRebase0, applyRebase1, applyRebase2, applyRebase3, "
                "applyRebase4"))
    return false;
  for (std::uint8_t move = 0; move < 5; ++move)
    for (std::uint8_t target = 0; target < 7; ++target)
      if (!out.text(", r35m") || !out.natural(move) || !out.text("c") ||
          !out.natural(target))
        return false;
  return out.text("]\n\ntheorem generated_heldout_trace_rebase : held") &&
         out.natural(surface.path_length) &&
         out.text(" = heldSource := heldoutTraceRebaseTransport\n\n"
                  "end Soma.Holonics.R35\n\n"
                  "#check Soma.Holonics.R35.generated_heldout_trace_rebase\n");
}

} // namespace holonics::codec

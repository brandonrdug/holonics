#pragma once

#include <holonics/organ/characteristic_matrix_law.hpp>
#include <holonics/organ/trace_rebase_receipt.hpp>

namespace holonics::organ::trace_rebase_matrix_detail {
using elementary_matrix_detail::determinant;
using elementary_matrix_detail::inverse;
using elementary_matrix_detail::multiply;

[[nodiscard]] HOLONICS_CALLABLE constexpr trace_rebase_move
inverse_move(trace_rebase_move move) noexcept {
  if (move == trace_rebase_move::shear12_positive)
    return trace_rebase_move::shear12_negative;
  if (move == trace_rebase_move::shear12_negative)
    return trace_rebase_move::shear12_positive;
  return move;
}
[[nodiscard]] HOLONICS_CALLABLE inline trace_rebase_move
nth_allowed(trace_rebase_move previous, std::uint8_t ordinal) noexcept {
  const auto forbidden = inverse_move(previous);
  for (std::uint8_t candidate = 0; candidate < trace_rebase_move_count;
       ++candidate) {
    const auto move = static_cast<trace_rebase_move>(candidate);
    if (move == forbidden)
      continue;
    if (ordinal == 0)
      return move;
    --ordinal;
  }
  return trace_rebase_move::swap12;
}
HOLONICS_CALLABLE inline void apply(trace_rebase_move move,
                                    const exact_matrix2 (&source)[3],
                                    exact_matrix2 (&target)[3]) noexcept {
  target[0] = source[0];
  target[1] = source[1];
  target[2] = source[2];
  if (move == trace_rebase_move::swap12) {
    target[0] = source[1];
    target[1] = source[0];
  } else if (move == trace_rebase_move::swap23) {
    target[1] = source[2];
    target[2] = source[1];
  } else if (move == trace_rebase_move::invert1) {
    target[0] = inverse(source[0]);
  } else if (move == trace_rebase_move::shear12_positive) {
    target[0] = multiply(source[0], source[1]);
  } else {
    target[0] = multiply(source[0], inverse(source[1]));
  }
}
HOLONICS_CALLABLE inline void coordinates(
    const exact_matrix2 (&matrices)[3],
    std::int64_t (&out)[trace_rebase_coordinate_count]) noexcept {
  const auto ab = multiply(matrices[0], matrices[1]);
  const auto ac = multiply(matrices[0], matrices[2]);
  const auto bc = multiply(matrices[1], matrices[2]);
  out[0] = characteristic_matrix_detail::trace(matrices[0]);
  out[1] = characteristic_matrix_detail::trace(matrices[1]);
  out[2] = characteristic_matrix_detail::trace(matrices[2]);
  out[3] = characteristic_matrix_detail::trace(ab);
  out[4] = characteristic_matrix_detail::trace(ac);
  out[5] = characteristic_matrix_detail::trace(bc);
  out[6] = characteristic_matrix_detail::trace(multiply(ab, matrices[2]));
}
[[nodiscard]] HOLONICS_CALLABLE inline bool branch(
    const exact_matrix2 (&matrices)[3], std::int64_t oriented) noexcept {
  const auto ac = multiply(matrices[0], matrices[2]);
  return oriented ==
         characteristic_matrix_detail::trace(multiply(ac, matrices[1]));
}
[[nodiscard]] HOLONICS_CALLABLE inline bool valid(
    const exact_matrix2 (&matrices)[3]) noexcept {
  return determinant(matrices[0]) == 1 && determinant(matrices[1]) == 1 &&
         determinant(matrices[2]) == 1;
}
HOLONICS_CALLABLE inline void decode(std::uint16_t local,
                                     trace_rebase_state &out) noexcept {
  if (local == 0)
    return;
  if (local <= 5) {
    out.depth = 1;
    out.path[0] = static_cast<trace_rebase_move>(local - 1U);
    return;
  }
  if (local <= 25) {
    const auto code = static_cast<std::uint8_t>(local - 6U);
    out.depth = 2;
    out.path[0] = static_cast<trace_rebase_move>(code / 4U);
    out.path[1] = nth_allowed(out.path[0], code % 4U);
    return;
  }
  const auto code = static_cast<std::uint8_t>(local - 26U);
  out.depth = 3;
  out.path[0] = static_cast<trace_rebase_move>(code / 16U);
  out.path[1] = nth_allowed(out.path[0], (code % 16U) / 4U);
  out.path[2] = nth_allowed(out.path[1], code % 4U);
}
HOLONICS_CALLABLE inline void form_state(
    const trace_rebase_source_card &card, std::uint8_t source,
    std::uint8_t seed, std::uint16_t local,
    trace_rebase_state &out) noexcept {
  out = {};
  out.source = source;
  out.seed = seed;
  out.ordinal = static_cast<std::uint16_t>(
      (source * trace_rebase_seed_count + seed) *
          trace_rebase_states_per_seed +
      local);
  out.lineage = exact::word{card.metadata.lineage.value() + out.ordinal + 1U};
  decode(local, out);
  for (std::uint8_t i = 0; i < 3; ++i)
    out.matrices[i] = card.seeds[seed][i];
  for (std::uint8_t i = 0; i < out.depth; ++i) {
    exact_matrix2 changed[3]{};
    apply(out.path[i], out.matrices, changed);
    for (std::uint8_t j = 0; j < 3; ++j)
      out.matrices[j] = changed[j];
  }
  coordinates(out.matrices, out.coordinates);
  out.branch = branch(out.matrices, out.coordinates[6]);
  out.valid = card.metadata.parsed && valid(out.matrices);
}
HOLONICS_CALLABLE inline void form_edge(const trace_rebase_state &state,
                                        trace_rebase_move move,
                                        trace_rebase_edge &out) noexcept {
  out = {};
  out.state = state.ordinal;
  out.move = move;
  apply(move, state.matrices, out.target_matrices);
  coordinates(out.target_matrices, out.target);
  out.source_branch = state.branch;
  out.target_branch = branch(out.target_matrices, out.target[6]);
  out.valid = state.valid && valid(out.target_matrices);
}

} // namespace holonics::organ::trace_rebase_matrix_detail

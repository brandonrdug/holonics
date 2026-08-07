#pragma once

#include <holonics/organ/characteristic_hypergeometry_receipt.hpp>
#include <holonics/organ/elementary_matrix_law.hpp>

namespace holonics::organ::characteristic_matrix_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t
trace(const exact_matrix2 &value) noexcept {
  return value.value[0] + value.value[3];
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int8_t
stratum(std::int64_t discriminant) noexcept {
  return discriminant < 0 ? -1 : (discriminant == 0 ? 0 : 1);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t
fixed_rank(const exact_matrix2 &value) noexcept {
  const exact_matrix2 shifted{
      {value.value[0] - 1, value.value[1], value.value[2], value.value[3] - 1}};
  if (elementary_matrix_detail::zero(shifted))
    return 2;
  return elementary_matrix_detail::determinant(shifted) == 0 ? 1 : 0;
}

HOLONICS_CALLABLE inline void append_word(transition_word_population &out,
                                          const exact_matrix2 &matrix,
                                          const std::uint8_t *letters,
                                          std::uint8_t length) noexcept {
  if (out.count >= characteristic_word_capacity) {
    out.complete = false;
    return;
  }
  auto &word = out.words[out.count];
  word.matrix = matrix;
  word.length = length;
  for (std::uint8_t i = 0; i < length; ++i)
    word.letters[i] = letters[i];
  word.ordinal = out.count;
  word.lineage = exact::word{out.lineage.value() + out.count + 1U};
  word.valid = true;
  ++out.count;
}

HOLONICS_CALLABLE inline void
form_words(const transition_source_card &card,
           transition_word_population &out) noexcept {
  using namespace elementary_matrix_detail;
  out = {};
  out.lineage = card.metadata.lineage;
  out.complete = true;
  exact_matrix2 generators[characteristic_generator_capacity]{};
  const auto pinverse = inverse(card.rechart);
  for (std::uint8_t i = 0; i < card.alphabet_size; ++i)
    generators[i] =
        card.recharted
            ? multiply(multiply(card.rechart, card.generators[i]), pinverse)
            : card.generators[i];
  std::uint8_t letters[characteristic_word_length]{};
  for (std::uint8_t a = 0; a < card.alphabet_size; ++a) {
    letters[0] = a;
    const auto ma = generators[a];
    append_word(out, ma, letters, 1);
    if (card.maximum_length < 2)
      continue;
    for (std::uint8_t b = 0; b < card.alphabet_size; ++b) {
      if (card.inverse_letter[a] == b)
        continue;
      letters[1] = b;
      const auto mb = multiply(ma, generators[b]);
      append_word(out, mb, letters, 2);
      if (card.maximum_length < 3)
        continue;
      for (std::uint8_t c = 0; c < card.alphabet_size; ++c) {
        if (card.inverse_letter[b] == c)
          continue;
        letters[2] = c;
        const auto mc = multiply(mb, generators[c]);
        append_word(out, mc, letters, 3);
        if (card.maximum_length < 4)
          continue;
        for (std::uint8_t d = 0; d < card.alphabet_size; ++d) {
          if (card.inverse_letter[c] == d)
            continue;
          letters[3] = d;
          append_word(out, multiply(mc, generators[d]), letters, 4);
        }
      }
    }
  }
}

HOLONICS_CALLABLE inline void
form_pair(const reduced_transition_word &left,
          const reduced_transition_word &right, std::uint8_t source,
          characteristic_pair_receipt &out) noexcept {
  using namespace elementary_matrix_detail;
  out = {};
  out.first = left.matrix;
  out.second = right.matrix;
  out.product = multiply(out.first, out.second);
  out.closed =
      multiply(multiply(out.product, inverse(out.first)), inverse(out.second));
  const std::int64_t traces[4]{trace(out.first), trace(out.second),
                               trace(out.product), trace(out.closed)};
  out.trace_first = traces[0];
  out.trace_second = traces[1];
  out.trace_product = traces[2];
  out.trace_closed = traces[3];
  const exact_matrix2 matrices[4]{out.first, out.second, out.product,
                                  out.closed};
  for (std::uint8_t i = 0; i < 4; ++i) {
    out.discriminants[i] = traces[i] * traces[i] - 4;
    out.strata[i] = stratum(out.discriminants[i]);
    out.fixed_ranks[i] = fixed_rank(matrices[i]);
  }
  out.left_word = left.ordinal;
  out.right_word = right.ordinal;
  out.source = source;
  out.valid = true;
}

HOLONICS_CALLABLE inline void
heldout_faces(const heldout_local_system_card &card,
              heldout_characteristic_receipt &out) noexcept {
  using namespace elementary_matrix_detail;
  out.first = identity();
  out.second = identity();
  for (std::uint8_t i = 0; i < card.split; ++i)
    out.first = multiply(out.first, card.edges[i]);
  for (std::uint8_t i = card.split; i < card.edge_count; ++i)
    out.second = multiply(out.second, card.edges[i]);
  out.product = multiply(out.first, out.second);
  out.closed =
      multiply(multiply(out.product, inverse(out.first)), inverse(out.second));
  out.visible[0] = trace(out.first);
  out.visible[1] = trace(out.second);
  out.visible[2] = trace(out.product);
  out.source_trace = trace(out.closed);
}

} // namespace holonics::organ::characteristic_matrix_detail

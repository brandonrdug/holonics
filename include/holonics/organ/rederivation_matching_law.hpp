#pragma once

#include <holonics/exact/integer_division.hpp>
#include <holonics/organ/rederivation_matching_alternative_law.hpp>
#include <holonics/organ/rederivation_matching_injection_law.hpp>
#include <holonics/organ/rederivation_receipt.hpp>

namespace holonics::organ::rederivation_matching_detail {

[[nodiscard]] HOLONICS_CALLABLE inline std::uint8_t
population(std::uint8_t bits) noexcept {
  std::uint8_t out = 0;
  for (; bits != 0; bits >>= 1U) {
    out += static_cast<std::uint8_t>(bits & 1U);
  }
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t
power(std::int64_t base, std::uint8_t exponent) noexcept {
  std::int64_t out = 1;
  while (exponent != 0) {
    if ((exponent & 1U) != 0) {
      out *= base;
    }
    exponent >>= 1U;
    if (exponent != 0) {
      base *= base;
    }
  }
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t
factorial(std::uint8_t value) noexcept {
  std::int64_t out = 1;
  for (std::uint8_t slot = 2; slot <= value; ++slot) {
    out *= slot;
  }
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t
falling(std::uint8_t value, std::uint8_t count) noexcept {
  std::int64_t out = 1;
  for (std::uint8_t slot = 0; slot < count; ++slot) {
    out *= value - slot;
  }
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t
row_factor(std::uint8_t p_size, std::uint8_t q_size) noexcept {
  const auto total = static_cast<std::uint8_t>(p_size + q_size);
  return factorial(static_cast<std::uint8_t>(6U - total)) *
         falling(static_cast<std::uint8_t>(6U - p_size), q_size) *
         falling(static_cast<std::uint8_t>(6U - q_size), p_size);
}

[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t
injection_sum(std::uint8_t subset,
              const std::int16_t (&values)[rederivation_external_count],
              std::uint8_t forbidden) noexcept {
  std::uint8_t indices[3]{};
  std::uint8_t count = 0;
  for (std::uint8_t bit = 0; bit < 3; ++bit)
    if ((subset & (1U << bit)) != 0) {
      indices[count++] = bit;
    }
  if (count == 0) {
    return 1;
  }
  std::int64_t sum = 0;
  for (std::uint8_t a = 0; a < 7; ++a) {
    if (a == forbidden) {
      continue;
    }
    const auto wa =
        power(values[a], static_cast<std::uint8_t>(1U << indices[0]));
    if (count == 1) {
      sum += wa;
      continue;
    }
    for (std::uint8_t b = 0; b < 7; ++b) {
      if (b == forbidden || b == a) {
        continue;
      }
      const auto wb =
          power(values[b], static_cast<std::uint8_t>(1U << indices[1]));
      if (count == 2) {
        sum += wa * wb;
        continue;
      }
      for (std::uint8_t c = 0; c < 7; ++c) {
        if (c == forbidden || c == a || c == b) {
          continue;
        }
        sum += wa * wb *
               power(values[c], static_cast<std::uint8_t>(1U << indices[2]));
      }
    }
  }
  return sum;
}

HOLONICS_CALLABLE inline void derive_entry(const matching_problem_card &card,
                                           std::uint32_t linear,
                                           jacobian_receipt &out) noexcept {
  const auto row_div = exact::divide_unsigned(linear, 49U);
  const auto alpha_div = exact::divide_unsigned(row_div.quotient, 7U);
  const auto column_div = exact::divide_unsigned(row_div.remainder, 7U);
  out.alpha = static_cast<std::uint8_t>(alpha_div.quotient);
  out.beta = static_cast<std::uint8_t>(alpha_div.remainder);
  out.row = static_cast<std::uint8_t>(column_div.quotient);
  out.column = static_cast<std::uint8_t>(column_div.remainder);
  out.p_size = population(out.alpha);
  out.q_size = population(out.beta);
  out.p_evaluation = injection_sum(out.alpha, card.p, out.column);
  out.q_evaluation = injection_sum(out.beta, card.q, out.row);
  out.row_factor = row_factor(out.p_size, out.q_size);
  out.value = out.row_factor * out.p_evaluation * out.q_evaluation;
  out.lineage = exact::word{card.metadata.lineage.value() + 10'000U + linear};
}

HOLONICS_CALLABLE inline void
close(const matching_problem_card &card, rederivation_workspace &workspace,
      matching_rederivation_receipt &out) noexcept {
  out.injection_count[0] = rederivation_matching_injection_detail::retain(
      0, card, workspace.injections[0]);
  out.injection_count[1] = rederivation_matching_injection_detail::retain(
      1, card, workspace.injections[1]);
  bool factor_exact = true;
  for (std::uint8_t alpha = 0; alpha < 7; ++alpha)
    for (std::uint8_t beta = 0; beta < 7; ++beta) {
      const auto slot = static_cast<std::uint8_t>(alpha * 7U + beta);
      const auto ps = population(alpha);
      const auto qs = population(beta);
      const auto pl = static_cast<std::int16_t>(
          (ps & 1U) == 0 ? factorial(ps) : -factorial(ps));
      const auto ql = static_cast<std::int16_t>(
          (qs & 1U) == 0 ? factorial(qs) : -factorial(qs));
      workspace.factors[slot] = {
          alpha,
          beta,
          ps,
          qs,
          pl,
          ql,
          row_factor(ps, qs),
          pl != 0 && ql != 0 && row_factor(ps, qs) != 0,
          exact::word{card.metadata.lineage.value() + 30'000U + slot}};
      for (std::uint8_t a = 0; a < 7; ++a)
        for (std::uint8_t b = 0; b < 7; ++b) {
          const auto linear =
              static_cast<std::uint32_t>(slot) * 49U + a * 7U + b;
          const auto &entry = workspace.jacobian[linear];
          factor_exact = factor_exact && entry.value == entry.row_factor *
                                                            entry.p_evaluation *
                                                            entry.q_evaluation;
        }
    }
  bool distinct = true;
  for (std::uint8_t i = 0; i < 7; ++i)
    for (std::uint8_t j = i + 1; j < 7; ++j) {
      distinct = distinct && card.p[i] != card.p[j] && card.q[i] != card.q[j];
    }
  out.coefficient_count = 49;
  out.jacobian_entries = 2'401;
  out.kronecker_exact = factor_exact;
  rederivation_matching_alternative_detail::derive(card, out);
  out.vandermonde_nonzero =
      distinct && out.p_vandermonde != 0 && out.q_vandermonde != 0;
  out.determinant_factored = factor_exact && distinct;
  out.independence_supported = out.determinant_factored;
  out.identity = exact::word{197'300};
  out.lineage = exact::word{card.metadata.lineage.value() + 39'999U};
}

} // namespace holonics::organ::rederivation_matching_detail

#pragma once

#include <holonics/organ/variation_connection_law.hpp>

namespace holonics::organ::variation_invariant_detail {

namespace rational = exact::small_rational_law;
namespace polynomial = variation_polynomial_detail;
namespace connection = variation_connection_detail;

HOLONICS_CALLABLE constexpr void form_residual(const global_connection_receipt& source,
    exact::small_rational parameter, const std::int64_t form[2][2],
    exact::small_rational residual[2][2]) noexcept {
  exact::small_rational numerator[2][2]{};
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      numerator[row][column] = connection::affine_value(
          source.numerator[row][column], parameter);
      residual[row][column] = rational::make(0);
    }
  }
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      for (std::uint8_t inner = 0; inner < 2; ++inner) {
        residual[row][column] = rational::add(residual[row][column], rational::add(
            rational::multiply(numerator[inner][row], rational::make(form[inner][column])),
            rational::multiply(rational::make(form[row][inner]),
                numerator[inner][column])));
      }
    }
  }
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool zero(
    const exact::small_rational residual[2][2]) noexcept {
  return residual[0][0].numerator == 0 && residual[0][1].numerator == 0 &&
      residual[1][0].numerator == 0 && residual[1][1].numerator == 0;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool primitive(
    const std::int64_t form[2][2]) noexcept {
  std::int64_t divisor = 0;
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      divisor = divisor == 0 ? rational::absolute(form[row][column]) :
          rational::gcd(divisor, form[row][column]);
    }
  }
  return divisor == 1;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr invariant_form_candidate test_candidate(
    const algebraic_variation_receipt& out, const std::int64_t form[2][2]) noexcept {
  invariant_form_candidate candidate{}; candidate.primitive = primitive(form);
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      candidate.form[row][column] = form[row][column];
    }
  }
  candidate.discovery_exact = candidate.primitive;
  candidate.holdout_exact = candidate.primitive;
  bool residual_retained = false;
  for (std::uint8_t sample = 0; sample < out.mounted.sample_count; ++sample) {
    exact::small_rational residual[2][2]{};
    form_residual(out.connection, out.samples[sample].parameter, form, residual);
    const bool exact = zero(residual);
    if (sample < out.mounted.discovery_count) {
      candidate.discovery_exact = candidate.discovery_exact && exact;
    } else {
      candidate.holdout_exact = candidate.holdout_exact && exact;
    }
    if (!exact && !residual_retained) {
      candidate.first_failed_sample = sample;
      for (std::uint8_t row = 0; row < 2; ++row) {
        for (std::uint8_t column = 0; column < 2; ++column) {
          candidate.residual[row][column] = residual[row][column];
        }
      }
      residual_retained = true;
    }
  }
  return candidate;
}

HOLONICS_CALLABLE constexpr void retain_candidate(invariant_form_receipt& receipt,
    invariant_form_candidate candidate, std::uint64_t lineage) noexcept {
  if (receipt.retained_count == variation_candidate_capacity) { return; }
  candidate.identity = exact::word{191'520U + receipt.retained_count};
  candidate.lineage = exact::word{lineage + receipt.retained_count};
  receipt.candidates[receipt.retained_count] = candidate; ++receipt.retained_count;
}

HOLONICS_CALLABLE constexpr void derive_invariant(algebraic_variation_receipt& out) noexcept {
  if (!out.connection.exact) { out.obstruction = variation_obstruction::invariant_refused; return; }
  bool local_retained = false;
  for (std::int64_t q00 = out.mounted.form_min; q00 <= out.mounted.form_max; ++q00) {
    for (std::int64_t q01 = out.mounted.form_min; q01 <= out.mounted.form_max; ++q01) {
      for (std::int64_t q10 = out.mounted.form_min; q10 <= out.mounted.form_max; ++q10) {
        for (std::int64_t q11 = out.mounted.form_min; q11 <= out.mounted.form_max; ++q11) {
          const std::int64_t form[2][2]{{q00,q01},{q10,q11}};
          if (!primitive(form)) { continue; }
          ++out.invariant.enumerated;
          auto candidate = test_candidate(out, form);
          if (candidate.discovery_exact) {
            ++out.invariant.discovery_survivors;
            if (candidate.holdout_exact) {
              candidate.orientation_selected = q01 > 0 && q10 < 0;
              retain_candidate(out.invariant, candidate, out.mounted.lineage.value() + 128U);
              if (candidate.orientation_selected) {
                for (std::uint8_t row = 0; row < 2; ++row) {
                  for (std::uint8_t column = 0; column < 2; ++column) {
                    out.invariant.selected[row][column] = form[row][column];
                  }
                }
                out.invariant.orientation_founded = true;
              }
            }
          } else if (!local_retained) {
            for (std::uint8_t sample = 0; sample < out.mounted.discovery_count; ++sample) {
              exact::small_rational local_residual[2][2]{};
              form_residual(out.connection, out.samples[sample].parameter, form, local_residual);
              if (zero(local_residual)) {
                retain_candidate(out.invariant, candidate, out.mounted.lineage.value() + 128U);
                local_retained = true; break;
              }
            }
          }
        }
      }
    }
  }
  const std::int64_t euclidean[2][2]{{1,0},{0,1}};
  const std::int64_t symmetric[2][2]{{0,1},{1,0}};
  const std::int64_t degenerate[2][2]{{1,0},{0,0}};
  auto euclidean_candidate = test_candidate(out, euclidean);
  auto symmetric_candidate = test_candidate(out, symmetric);
  auto degenerate_candidate = test_candidate(out, degenerate);
  retain_candidate(out.invariant, euclidean_candidate, out.mounted.lineage.value() + 128U);
  retain_candidate(out.invariant, symmetric_candidate, out.mounted.lineage.value() + 128U);
  retain_candidate(out.invariant, degenerate_candidate, out.mounted.lineage.value() + 128U);
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      out.foils.euclidean_residual[row][column] = euclidean_candidate.residual[row][column];
      out.foils.symmetric_residual[row][column] = symmetric_candidate.residual[row][column];
      out.foils.degenerate_residual[row][column] = degenerate_candidate.residual[row][column];
    }
  }
  out.foils.local_only_form_rejected = local_retained;
  out.foils.euclidean_form_rejected = !euclidean_candidate.discovery_exact;
  out.foils.symmetric_form_rejected = !symmetric_candidate.discovery_exact;
  out.foils.degenerate_form_rejected = !degenerate_candidate.discovery_exact;
  out.invariant.identity = exact::word{191'510};
  out.invariant.lineage = exact::word{out.mounted.lineage.value() + 127U};
  out.invariant.exact = out.invariant.orientation_founded &&
      out.invariant.discovery_survivors == 2 && out.foils.local_only_form_rejected;
  if (!out.invariant.exact) { out.obstruction = variation_obstruction::invariant_refused; }
}

}  // namespace holonics::organ::variation_invariant_detail

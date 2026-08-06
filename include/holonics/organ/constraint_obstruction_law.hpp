#pragma once

#include <cstdint>

#include <holonics/organ/arithmetic_field_law.hpp>

namespace holonics::organ {

inline constexpr std::uint8_t constraint_degree = 5;

/// The factor degrees of a constraint reduced at one prime.
///
/// By Dedekind's theorem this multiset **is** the cycle type of a Frobenius
/// element in the constraint's own group, whenever the reduction stays
/// squarefree. It is a local reading of a global object: the chart varies with
/// the prime, the group does not.
struct cycle_type final {
  std::uint8_t degrees[constraint_degree]{};
  std::uint8_t used{};
  std::uint16_t prime{};
  std::uint16_t linear_factors{};
  std::uint16_t quadratic_factors{};
  bool squarefree{};
  bool product_agrees{};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool admitted() const noexcept {
    return squarefree && product_agrees && used != 0;
  }
};

/// Why the unknown is not determined in the present chart. **None of these is a
/// failure.** Each is an exact statement about which pathway is missing.
enum class chart_obstruction : std::uint8_t {
  none,
  reduction_degenerate,
  group_not_solvable,
  witnesses_insufficient
};

/// What the body has proved about the constraint's group from local readings.
struct obstruction_witness final {
  std::uint16_t transitive_prime{};
  std::uint16_t transposition_prime{};
  cycle_type transitive_type{};
  cycle_type transposition_type{};
  bool transitive{};
  bool carries_transposition{};

  /// A transitive subgroup of the symmetric group on a prime number of points
  /// that carries a transposition is the whole symmetric group. For five points
  /// that group is not solvable, so **no tower of cyclic charts reaches the
  /// root** — the unknown is unreachable by radicals, and this is the proof of
  /// it rather than a report of difficulty.
  [[nodiscard]] HOLONICS_CALLABLE constexpr chart_obstruction verdict() const noexcept {
    return transitive && carries_transposition ? chart_obstruction::group_not_solvable
                                               : chart_obstruction::witnesses_insufficient;
  }
};

namespace constraint_law {

using arithmetic_field_detail::reduced;

/// Does a monic divisor divide this constraint?
///
/// **This is not the borrowed `polynomial_divides`.** That organ declares a
/// degree-four aperture and sizes its remainder for it; a quintic exceeds it.
/// Using an organ past its declared aperture is a defect even when it appears
/// to return, so the quintic carries its own remainder here.
[[nodiscard]] HOLONICS_CALLABLE inline bool divides(
    const std::uint16_t* source,
    std::uint8_t source_degree,
    const std::uint16_t* divisor,
    std::uint8_t divisor_degree,
    std::uint16_t prime) noexcept {
  if (source_degree > constraint_degree || divisor_degree > source_degree) {
    return false;
  }
  std::uint16_t remainder[constraint_degree + 1]{};
  for (std::uint8_t slot = 0; slot <= source_degree; ++slot) {
    remainder[slot] = source[slot];
  }
  for (std::int8_t top = static_cast<std::int8_t>(source_degree);
       top >= static_cast<std::int8_t>(divisor_degree); --top) {
    const auto coefficient = remainder[static_cast<std::uint8_t>(top)];
    if (coefficient == 0) {
      continue;
    }
    const auto shift = static_cast<std::uint8_t>(
        static_cast<std::uint8_t>(top) - divisor_degree);
    for (std::uint8_t slot = 0; slot <= divisor_degree; ++slot) {
      const auto target = static_cast<std::uint8_t>(slot + shift);
      remainder[target] = reduced(static_cast<std::int64_t>(remainder[target]) -
          static_cast<std::int64_t>(coefficient) * divisor[slot], prime);
    }
  }
  for (std::uint8_t slot = 0; slot < divisor_degree; ++slot) {
    if (remainder[slot] != 0) {
      return false;
    }
  }
  return true;
}

/// Reduce a monic integer constraint at one prime, low coefficient first.
HOLONICS_CALLABLE inline void reduce_at(
    const std::int64_t* coefficients,
    std::uint16_t prime,
    std::uint16_t* out) noexcept {
  for (std::uint8_t slot = 0; slot <= constraint_degree; ++slot) {
    out[slot] = reduced(coefficients[slot], prime);
  }
}

/// Is this monic quadratic irreducible over the prime field? A reducible one
/// would recount the linear factors it is built from twice.
[[nodiscard]] HOLONICS_CALLABLE inline bool irreducible_quadratic(
    const std::uint16_t* divisor,
    std::uint16_t prime) noexcept {
  for (std::uint16_t root = 0; root < prime; ++root) {
    const auto value = reduced(static_cast<std::int64_t>(root) * root +
        static_cast<std::int64_t>(divisor[1]) * root + divisor[0], prime);
    if (value == 0) {
      return false;
    }
  }
  return true;
}

/// Divide `source` by a monic `divisor`, leaving the quotient. The remainder is
/// zero by construction wherever this is called, and it is checked.
[[nodiscard]] HOLONICS_CALLABLE inline bool divide_out(
    std::uint16_t* source,
    std::uint8_t& source_degree,
    const std::uint16_t* divisor,
    std::uint8_t divisor_degree,
    std::uint16_t prime) noexcept {
  std::uint16_t quotient[constraint_degree + 1]{};
  for (std::int8_t top = static_cast<std::int8_t>(source_degree);
       top >= static_cast<std::int8_t>(divisor_degree); --top) {
    const auto coefficient = source[static_cast<std::uint8_t>(top)];
    if (coefficient == 0) {
      continue;
    }
    const auto shift = static_cast<std::uint8_t>(
        static_cast<std::uint8_t>(top) - divisor_degree);
    quotient[shift] = coefficient;
    for (std::uint8_t slot = 0; slot <= divisor_degree; ++slot) {
      const auto target = static_cast<std::uint8_t>(slot + shift);
      source[target] = reduced(static_cast<std::int64_t>(source[target]) -
          static_cast<std::int64_t>(coefficient) * divisor[slot], prime);
    }
  }
  for (std::uint8_t slot = 0; slot < divisor_degree; ++slot) {
    if (source[slot] != 0) {
      return false;
    }
  }
  source_degree = static_cast<std::uint8_t>(source_degree - divisor_degree);
  for (std::uint8_t slot = 0; slot <= source_degree; ++slot) {
    source[slot] = quotient[slot];
  }
  return true;
}

/// Multiply the found factors and compare against the reduction. This is an
/// independent confirmation of the factor degrees: the enumeration says which
/// divisors stand, and this says they account for the whole constraint.
[[nodiscard]] HOLONICS_CALLABLE inline bool product_agrees(
    const std::uint16_t* reduction,
    const std::uint16_t* factors,
    const std::uint8_t* degrees,
    std::uint8_t count,
    std::uint16_t prime) noexcept {
  std::uint16_t accumulated[constraint_degree + 1]{};
  accumulated[0] = 1;
  std::uint8_t degree = 0;
  for (std::uint8_t held = 0; held < count; ++held) {
    const std::uint16_t* factor = factors + (held * (constraint_degree + 1));
    std::uint16_t product[(constraint_degree * 2) + 2]{};
    for (std::uint8_t left = 0; left <= degree; ++left) {
      for (std::uint8_t right = 0; right <= degrees[held]; ++right) {
        const auto slot = static_cast<std::uint8_t>(left + right);
        product[slot] = reduced(static_cast<std::int64_t>(product[slot]) +
            static_cast<std::int64_t>(accumulated[left]) * factor[right], prime);
      }
    }
    degree = static_cast<std::uint8_t>(degree + degrees[held]);
    if (degree > constraint_degree) {
      return false;
    }
    for (std::uint8_t slot = 0; slot <= degree; ++slot) {
      accumulated[slot] = product[slot];
    }
  }
  if (degree != constraint_degree) {
    return false;
  }
  for (std::uint8_t slot = 0; slot <= constraint_degree; ++slot) {
    if (accumulated[slot] != reduction[slot]) {
      return false;
    }
  }
  return true;
}

}  // namespace constraint_law

}  // namespace holonics::organ

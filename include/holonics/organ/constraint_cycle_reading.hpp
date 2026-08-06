#pragma once

#include <cstdint>

#include <holonics/organ/constraint_obstruction_law.hpp>

namespace holonics::organ::constraint_law {

/// Read the cycle type at one prime.
///
/// Linear and irreducible quadratic divisors are enumerated exhaustively and
/// divided out as they are found; for a quintic whatever remains then carries no
/// divisor of degree one or two and is therefore a **single irreducible factor**
/// of the remaining degree. A repeated factor is detected by testing the square,
/// and it means the prime lies on the discriminant locus, where Dedekind's
/// reading does not hold and the body must say so rather than read anyway.
[[nodiscard]] HOLONICS_CALLABLE inline cycle_type read_cycle_type(
    const std::int64_t* coefficients,
    std::uint16_t prime,
    std::uint16_t* factors_out) noexcept {
  cycle_type found{};
  found.prime = prime;
  std::uint16_t reduction[constraint_degree + 1]{};
  reduce_at(coefficients, prime, reduction);
  if (reduction[constraint_degree] != 1) {
    return found;
  }
  std::uint16_t remaining[constraint_degree + 1]{};
  for (std::uint8_t slot = 0; slot <= constraint_degree; ++slot) {
    remaining[slot] = reduction[slot];
  }
  std::uint8_t remaining_degree = constraint_degree;
  std::uint8_t degrees[constraint_degree]{};
  std::uint8_t count = 0;
  found.squarefree = true;

  for (std::uint16_t root = 0; root < prime; ++root) {
    std::uint16_t divisor[constraint_degree + 1]{};
    divisor[0] = reduced(-static_cast<std::int64_t>(root), prime);
    divisor[1] = 1;
    while (remaining_degree >= 1 &&
        divides(remaining, remaining_degree, divisor, 1, prime)) {
      if (count != 0 && degrees[count - 1U] == 1 &&
          factors_out[((count - 1U) * (constraint_degree + 1))] == divisor[0]) {
        found.squarefree = false;
        return found;
      }
      for (std::uint8_t slot = 0; slot <= constraint_degree; ++slot) {
        factors_out[(count * (constraint_degree + 1)) + slot] = divisor[slot];
      }
      degrees[count] = 1;
      count = static_cast<std::uint8_t>(count + 1U);
      found.linear_factors = static_cast<std::uint16_t>(found.linear_factors + 1U);
      if (!divide_out(remaining, remaining_degree, divisor, 1, prime)) {
        return found;
      }
      if (divides(remaining, remaining_degree, divisor, 1, prime)) {
        found.squarefree = false;
        return found;
      }
      break;
    }
  }

  for (std::uint32_t low = 0; low < prime && remaining_degree >= 2; ++low) {
    for (std::uint32_t mid = 0; mid < prime && remaining_degree >= 2; ++mid) {
      std::uint16_t divisor[constraint_degree + 1]{};
      divisor[0] = static_cast<std::uint16_t>(low);
      divisor[1] = static_cast<std::uint16_t>(mid);
      divisor[2] = 1;
      if (!irreducible_quadratic(divisor, prime) ||
          !divides(remaining, remaining_degree, divisor, 2, prime)) {
        continue;
      }
      for (std::uint8_t slot = 0; slot <= constraint_degree; ++slot) {
        factors_out[(count * (constraint_degree + 1)) + slot] = divisor[slot];
      }
      degrees[count] = 2;
      count = static_cast<std::uint8_t>(count + 1U);
      found.quadratic_factors = static_cast<std::uint16_t>(found.quadratic_factors + 1U);
      if (!divide_out(remaining, remaining_degree, divisor, 2, prime)) {
        return found;
      }
      if (remaining_degree >= 2 &&
          divides(remaining, remaining_degree, divisor, 2, prime)) {
        found.squarefree = false;
        return found;
      }
    }
  }

  if (remaining_degree != 0) {
    for (std::uint8_t slot = 0; slot <= constraint_degree; ++slot) {
      factors_out[(count * (constraint_degree + 1)) + slot] =
          slot <= remaining_degree ? remaining[slot] : 0;
    }
    degrees[count] = remaining_degree;
    count = static_cast<std::uint8_t>(count + 1U);
  }
  for (std::uint8_t held = 0; held < count; ++held) {
    found.degrees[held] = degrees[held];
  }
  found.used = count;
  found.product_agrees = product_agrees(reduction, factors_out, degrees, count, prime);
  return found;
}

/// Does this cycle type carry a transposition in one of its powers? Exactly one
/// even degree, and that degree two, with every other degree odd. For five
/// points that is `(2,3)` and `(2,1,1,1)` and nothing else — `(2,2,1)` has two
/// even degrees and `(4,1)` has the wrong one.
[[nodiscard]] HOLONICS_CALLABLE inline bool carries_transposition(
    const cycle_type& type) noexcept {
  std::uint8_t evens = 0;
  bool two_present = false;
  for (std::uint8_t slot = 0; slot < type.used; ++slot) {
    if ((type.degrees[slot] & 1U) == 0) {
      evens = static_cast<std::uint8_t>(evens + 1U);
      two_present = two_present || type.degrees[slot] == 2;
    }
  }
  return evens == 1 && two_present;
}

/// Is the constraint irreducible here? Then it is irreducible over the integers
/// and its group acts transitively on the roots.
[[nodiscard]] HOLONICS_CALLABLE inline bool witnesses_transitivity(
    const cycle_type& type) noexcept {
  return type.used == 1 && type.degrees[0] == constraint_degree;
}

/// Do the roots at this prime form a coset of the fifth roots of unity? That is
/// the **radical structure witnessed locally**: every root is one root times a
/// unit, which is exactly what a radical tower asserts globally.
[[nodiscard]] HOLONICS_CALLABLE inline bool roots_form_radical_coset(
    const std::int64_t* coefficients,
    std::uint16_t prime,
    std::uint16_t* roots_out,
    std::uint8_t& root_count) noexcept {
  std::uint16_t reduction[constraint_degree + 1]{};
  reduce_at(coefficients, prime, reduction);
  root_count = 0;
  for (std::uint16_t candidate = 0; candidate < prime; ++candidate) {
    std::int64_t value = 0;
    for (std::int8_t slot = constraint_degree; slot >= 0; --slot) {
      value = static_cast<std::int64_t>(reduced(
          value * candidate + reduction[static_cast<std::uint8_t>(slot)], prime));
    }
    if (value == 0 && root_count < constraint_degree) {
      roots_out[root_count] = candidate;
      root_count = static_cast<std::uint8_t>(root_count + 1U);
    }
  }
  if (root_count != constraint_degree || roots_out[0] == 0) {
    return false;
  }
  for (std::uint16_t unit = 1; unit < prime; ++unit) {
    std::uint16_t power = 1;
    for (std::uint8_t step = 0; step < constraint_degree; ++step) {
      power = reduced(static_cast<std::int64_t>(power) * unit, prime);
    }
    if (power != 1 || unit == 1) {
      continue;
    }
    std::uint8_t matched = 0;
    std::uint16_t walk = roots_out[0];
    for (std::uint8_t step = 0; step < constraint_degree; ++step) {
      for (std::uint8_t held = 0; held < root_count; ++held) {
        matched = static_cast<std::uint8_t>(
            matched + (roots_out[held] == walk ? 1U : 0U));
      }
      walk = reduced(static_cast<std::int64_t>(walk) * unit, prime);
    }
    if (matched == constraint_degree && walk == roots_out[0]) {
      return true;
    }
  }
  return false;
}

}  // namespace holonics::organ::constraint_law

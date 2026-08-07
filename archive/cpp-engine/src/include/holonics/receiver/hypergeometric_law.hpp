#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/receiver/geometry_exact.hpp>

namespace holonics::receiver {

[[nodiscard]] HOLONICS_CALLABLE constexpr hypergeometric_receipt carry_gauss_solution(
    const hypergeometric_program& program) noexcept {
  hypergeometric_receipt result{};
  result.parameters[0] = program.a;
  result.parameters[1] = program.b;
  result.parameters[2] = program.c;
  result.singular_locus[0] = exact::word{0};
  result.singular_locus[1] = exact::word{1};
  result.singular_locus[2] = exact::word{~std::uint64_t{0}};
  result.branch = program.branch;
  result.path = program.path;
  result.lineage = program.lineage;
  result.family = program.family;
  result.term_count = program.term_count;
  for (std::size_t slot = 0; slot < 4; ++slot) { result.monodromy[slot] = program.monodromy[slot]; }
  if (program.family != solution_family::gauss || program.term_count == 0 ||
      program.term_count > hypergeometric_term_capacity ||
      program.initial_coefficient.second.value() == 0) {
    return result;
  }
  result.coefficients[0] = program.initial_coefficient;
  result.recurrence_exact = true;
  for (std::size_t term = 0; term + 1 < program.term_count; ++term) {
    const std::uint64_t index = term;
    std::uint64_t a_term = 0;
    std::uint64_t b_term = 0;
    std::uint64_t c_term = 0;
    std::uint64_t numerator = 0;
    std::uint64_t denominator = 0;
    std::uint64_t next_numerator = 0;
    std::uint64_t next_denominator = 0;
    if (!geometry_add(program.a.value(), index, a_term) ||
        !geometry_add(program.b.value(), index, b_term) ||
        !geometry_add(program.c.value(), index, c_term) ||
        !geometry_multiply(a_term, b_term, numerator) ||
        !geometry_multiply(result.coefficients[term].first.value(),
            numerator, next_numerator) ||
        !geometry_multiply(c_term, index + 1U, denominator) ||
        !geometry_multiply(result.coefficients[term].second.value(),
            denominator, next_denominator)) {
      result.recurrence_exact = false;
      return result;
    }
    result.coefficients[term + 1] =
        {exact::word{next_numerator}, exact::word{next_denominator}};
  }
  result.singular_locus_retained = true;
  result.branch_retained = program.branch.value() != 0 && program.path.value() != 0;
  result.confluent_distinct = program.family != solution_family::confluent;
  result.generalized_distinct = program.family != solution_family::generalized;
  return result;
}

}  // namespace holonics::receiver

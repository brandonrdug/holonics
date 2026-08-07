#pragma once

#include <cstddef>

#include <holonics/exact/signed_magnitude.hpp>
#include <holonics/structure/resident_complex_law.hpp>

namespace holonics::structure {

HOLONICS_CALLABLE inline void verify_boundary_squared(
    const resident_complex& complex,
    structure_output& output) noexcept {
  using coefficient = exact::signed_magnitude<2>;
  for (std::size_t top_slot = 0; top_slot < complex.cell_count(); ++top_slot) {
    const resident_cell* top = complex.cell(top_slot);
    if (!top->active() || top->dimension() < 2) {
      continue;
    }
    ++output.boundary_checks;
    coefficient accumulated[resident_cell_capacity]{};
    bool exact_return = true;
    for (std::size_t first_offset = 0; first_offset < top->outgoing_count(); ++first_offset) {
      const resident_incidence* first = complex.incidence(
          static_cast<std::size_t>(top->outgoing_begin()) + first_offset);
      const resident_cell* middle = complex.cell(first->lower_slot());
      for (std::size_t second_offset = 0;
           first->active() && second_offset < middle->outgoing_count();
           ++second_offset) {
        const resident_incidence* second = complex.incidence(
            static_cast<std::size_t>(middle->outgoing_begin()) + second_offset);
        ++output.boundary_terms_touched;
        const coefficient first_value{
            first->orientation() < 0,
            exact::unsigned_integer<2>::from_word(first->multiplicity().value())};
        const coefficient second_value{
            second->orientation() < 0,
            exact::unsigned_integer<2>::from_word(second->multiplicity().value())};
        const auto product = exact::multiply(first_value, second_value);
        if (!product.accepted()) {
          exact_return = false;
          break;
        }
        const auto sum = exact::add(accumulated[second->lower_slot()], product.value);
        if (!sum.accepted()) {
          exact_return = false;
          break;
        }
        accumulated[second->lower_slot()] = sum.value;
      }
      if (!exact_return) {
        break;
      }
    }
    for (std::size_t slot = 0; exact_return && slot < complex.cell_count(); ++slot) {
      if (!accumulated[slot].magnitude().is_zero()) {
        exact_return = false;
      }
    }
    if (!exact_return) {
      ++output.boundary_failures;
    }
  }
}

}  // namespace holonics::structure

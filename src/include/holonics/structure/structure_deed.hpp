#pragma once

#include <holonics/structure/boundary_law.hpp>
#include <holonics/structure/traversal.hpp>

namespace holonics::structure {

HOLONICS_CALLABLE inline void admit_structure_case(
    resident_complex& complex,
    const structure_case& input,
    structure_output& output) noexcept {
  output = structure_output{};
  static_cast<void>(complex.admit(input, output));
}

HOLONICS_CALLABLE inline void continue_structure_case(
    resident_complex& complex,
    const structure_case& input,
    structure_output& output) noexcept {
  if (output.admission.state != structure_status::exact) {
    return;
  }
  verify_boundary_squared(complex, output);
  traverse_boundary_support(complex, input.traversal_seed, output);
  complex.append_isolated(input.append_isolated_count, output.delta);
  complex.depart(input.departure_slot, output.delta);
  output.active_cells_after = static_cast<std::uint16_t>(complex.active_cell_count());
  output.successor_hash = complex.standing_hash();
  output.occurrence_mint_after = complex.occurrence_mint_cursor();
}

}  // namespace holonics::structure

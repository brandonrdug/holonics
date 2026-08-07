#pragma once

#include <cstddef>

#include <holonics/structure/rebase_law.hpp>

namespace holonics::structure {

/// Reduce one grade's incidence by rebasing, and return what survives.
///
/// The loop is the one move. Pick a lower cell that still stands; among the
/// higher cells meeting it take the one carrying the smallest magnitude as the
/// pivot; carry that pivot out of every other cell meeting the same lower cell.
/// A cell whose coefficient clears has RIDDEN the pivot. A cell left with a
/// remainder has FOUNDED a smaller pivot, and the next pass rides that one.
///
/// When the star closes, the pivot and its lower cell leave the working set
/// together and the magnitude that could not be carried away is one invariant
/// factor. **A factor of one is a rebase that succeeded completely; a factor
/// above one is winding that no change of basis removes.**
namespace invariant_factor_law {

using rebase_law::coefficient;

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE inline rebase_return reduce(
    rebase_entry (&entries)[Capacity],
    std::size_t used) noexcept {
  rebase_return out{};
  out.exact = true;
  bool retired_cell[resident_cell_capacity]{};
  bool retired_face[resident_cell_capacity]{};

  for (std::size_t pivot_pass = 0; pivot_pass <= Capacity; ++pivot_pass) {
    // Find a face that still stands and the smallest cell meeting it.
    std::uint16_t chosen_face = 0;
    std::uint16_t chosen_cell = 0;
    coefficient chosen{};
    bool standing = false;
    for (std::size_t slot = 0; slot < used && out.exact; ++slot) {
      const auto& entry = entries[slot];
      if (!entry.live || retired_face[entry.lower] || retired_cell[entry.higher]) {
        continue;
      }
      const coefficient value =
          rebase_law::meeting(entries, used, entry.higher, entry.lower, out.exact);
      if (value.magnitude().is_zero()) {
        continue;
      }
      if (!standing ||
          exact::compare(value.magnitude(), chosen.magnitude()) < 0) {
        standing = true;
        chosen = value;
        chosen_face = entry.lower;
        chosen_cell = entry.higher;
      }
    }
    if (!standing || !out.exact) {
      break;
    }

    // Carry the pivot out of every other cell meeting the same face.
    bool remainder_stands = false;
    for (std::size_t slot = 0; slot < used && out.exact; ++slot) {
      const auto& entry = entries[slot];
      if (!entry.live || entry.lower != chosen_face ||
          entry.higher == chosen_cell || retired_cell[entry.higher]) {
        continue;
      }
      const std::uint16_t other = entry.higher;
      const coefficient value =
          rebase_law::meeting(entries, used, other, chosen_face, out.exact);
      if (value.magnitude().is_zero()) {
        continue;
      }
      const auto split = exact::divide(value.magnitude(), chosen.magnitude());
      if (!split.accepted()) {
        out.exact = false;
        break;
      }
      const coefficient factor{value.negative() != chosen.negative(), split.quotient};
      if (!rebase_law::carry(entries, used, chosen_cell, other, factor)) {
        out.exact = false;
        break;
      }
      if (split.remainder.is_zero()) {
        out.rides = out.rides + 1U;
      } else {
        out.foundings = out.foundings + 1U;
        remainder_stands = true;
      }
    }
    if (!out.exact) {
      break;
    }
    if (remainder_stands) {
      continue;  // a smaller pivot was founded; ride it on the next pass
    }

    // The star has closed. What is left is an invariant factor.
    retired_cell[chosen_cell] = true;
    retired_face[chosen_face] = true;
    out.rank = out.rank + 1U;
    if (out.divisor_count < 16U) {
      out.divisors[out.divisor_count] = exact::word{chosen.magnitude().limb(0)};
      out.divisor_count = out.divisor_count + 1U;
    }
    const auto one = exact::unsigned_integer<2>::from_word(1);
    if (exact::compare(chosen.magnitude(), one) > 0) {
      out.torsion_count = out.torsion_count + 1U;
    }
  }
  return out;
}

}  // namespace invariant_factor_law
}  // namespace holonics::structure

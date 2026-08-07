#pragma once

#include <cstddef>

#include <holonics/exact/signed_magnitude.hpp>
#include <holonics/structure/resident_complex.hpp>

namespace holonics::structure {

/// The invariant factors of a boundary map, read by rebasing its incidence.
///
/// **This is the Swing run over incidence, and the identification is exact.**
/// Two cells meeting the same lower cell is a MEETING; the pivot incidence being
/// carried is the FLYWHEEL; the ratio of their multiplicities is the TEST; a
/// multiple that divides exactly clears the incidence and is a RIDE; a remainder
/// that stands becomes the next pivot and is a FOUND. What no rebase can clear
/// is the divisor, and a divisor above one is **retained winding**.
///
/// A column operation is a rebase of the chain group's basis — replacing one
/// cell by that cell plus another, `chi' = G chi G^-1`. The invariant factors are
/// therefore *what survives every rebase*, which is why they are invariants at
/// all and why torsion is not an artifact of the order of reduction.
///
/// **No matrix is assembled and no order is scheduled.** Classical reductions
/// scan the whole remaining block for the smallest magnitude; that scan is a
/// stability heuristic for inexact arithmetic and buys nothing here, because
/// with exact coefficients any pivot order returns the same factors. The working
/// set is one lower cell's star, and information moves along the incidence
/// chains the complex already carries.
struct rebase_entry final {
  std::uint16_t higher{};
  std::uint16_t lower{};
  exact::signed_magnitude<2> coefficient{};
  bool live{};
};

struct rebase_return final {
  std::uint32_t rank{};
  std::uint32_t divisor_count{};
  std::uint32_t torsion_count{};
  exact::word divisors[16]{};
  std::uint32_t rides{};
  std::uint32_t foundings{};
  bool exact{};
};

namespace rebase_law {

using coefficient = exact::signed_magnitude<2>;

[[nodiscard]] HOLONICS_CALLABLE constexpr coefficient negate(
    const coefficient& value) noexcept {
  return coefficient{!value.negative(), value.magnitude()};
}

/// Mount one grade's incidence as a rebasable working set.
///
/// The rested complex is untouched: the standing stands and the current rebases.
/// The working set is bounded by the incidence population, never by the product
/// of the cell populations.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE inline std::size_t mount_grade(
    const resident_complex& complex,
    std::uint8_t grade,
    rebase_entry (&into)[Capacity]) noexcept {
  std::size_t used = 0;
  for (std::size_t slot = 0; slot < complex.incidence_count(); ++slot) {
    const resident_incidence* relation = complex.incidence(slot);
    if (relation == nullptr || !relation->active() || used >= Capacity) {
      continue;
    }
    const resident_cell* higher = complex.cell(relation->higher_slot());
    if (higher == nullptr || higher->dimension() != grade) {
      continue;
    }
    into[used] = rebase_entry{
        relation->higher_slot(), relation->lower_slot(),
        coefficient{relation->orientation() < 0,
            exact::unsigned_integer<2>::from_word(relation->multiplicity().value())},
        true};
    used = used + 1U;
  }
  return used;
}

/// The coefficient carrying one higher cell to one lower cell, summed over the
/// working set. Repeated meeting adds; opposed hands cancel to nothing.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE inline coefficient meeting(
    const rebase_entry (&entries)[Capacity],
    std::size_t used,
    std::uint16_t higher,
    std::uint16_t lower,
    bool& exact) noexcept {
  coefficient total{};
  for (std::size_t slot = 0; slot < used; ++slot) {
    if (!entries[slot].live || entries[slot].higher != higher ||
        entries[slot].lower != lower) {
      continue;
    }
    const auto sum = exact::add(total, entries[slot].coefficient);
    if (!sum.accepted()) {
      exact = false;
      return total;
    }
    total = sum.value;
  }
  return total;
}

/// One rebase: carry `factor` times the pivot cell out of the other cell.
///
/// Every entry of the other cell is displaced, which is what makes this a change
/// of basis rather than a local erasure. The entries live in the working set, so
/// the displacement costs the two cells' own chains and nothing else.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE inline bool carry(
    rebase_entry (&entries)[Capacity],
    std::size_t& used,
    std::uint16_t pivot,
    std::uint16_t other,
    const coefficient& factor) noexcept {
  const std::size_t before = used;
  for (std::size_t slot = 0; slot < before; ++slot) {
    if (!entries[slot].live || entries[slot].higher != pivot) {
      continue;
    }
    const auto scaled = exact::multiply(entries[slot].coefficient, factor);
    if (!scaled.accepted() || used >= Capacity) {
      return false;
    }
    entries[used] = rebase_entry{other, entries[slot].lower,
        negate(scaled.value), true};
    used = used + 1U;
  }
  return true;
}

}  // namespace rebase_law
}  // namespace holonics::structure

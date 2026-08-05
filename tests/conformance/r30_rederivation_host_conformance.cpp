#include <memory>

#include <holonics/organ/rederivation_cover_law.hpp>
#include <holonics/organ/rederivation_geometry_law.hpp>
#include <holonics/organ/rederivation_matching_law.hpp>
#include <holonics/organ/rederivation_potential_law.hpp>
#include <holonics/organ/rederivation_realization_law.hpp>

#include "r30_cases.hpp"
#include "r30_reference.hpp"

int main() {
  const auto foundation = holonics::tests::r30_host_foundation();
  auto workspace = std::make_unique<holonics::organ::rederivation_workspace>();
  holonics::organ::rederivation_receipt r{};
  r.matching_card = foundation.matching;
  r.lattice_card = foundation.lattice;
  r.cover_card = foundation.cover;
  for (std::uint32_t i = 0; i < holonics::organ::rederivation_jacobian_count;
       ++i)
    holonics::organ::rederivation_matching_detail::derive_entry(
        r.matching_card, i, workspace->jacobian[i]);
  holonics::organ::rederivation_matching_detail::close(r.matching_card,
                                                       *workspace, r.matching);
  for (std::uint8_t p = 0; p < 4; ++p)
    holonics::organ::rederivation_geometry_detail::derive_polygon(
        p, r.lattice_card, *workspace, r.polygons[p]);
  holonics::organ::rederivation_cover_detail::derive(r.cover_card, *workspace,
                                                     r.cover);
  holonics::organ::rederivation_potential_detail::derive(
      r.lattice_card, r.polygons[1], *workspace, r.potential);
  holonics::organ::rederivation_realization_detail::close(r);
  const auto ref = holonics::tests::r30_reference();
  if (!r.all_exact || !ref.exact || r.matching.injection_count[0] != 763 ||
      r.matching.injection_count[1] != 763)
    return 1;
  for (std::uint8_t a = 0; a < 7; ++a)
    for (std::uint8_t b = 0; b < 7; ++b)
      for (std::uint8_t row = 0; row < 7; ++row)
        for (std::uint8_t col = 0; col < 7; ++col) {
          const auto slot =
              static_cast<std::size_t>(a * 7U + b) * 49U + row * 7U + col;
          if (workspace->jacobian[slot].value !=
              holonics::tests::r30_reference_jacobian(a, b, row, col))
            return 2;
        }
  for (std::uint8_t p = 0; p < 4; ++p)
    for (std::uint8_t n = 0; n < 5; ++n)
      if (r.polygons[p].lattice_count[n] != ref.counts[p][n])
        return 3;
  return 0;
}

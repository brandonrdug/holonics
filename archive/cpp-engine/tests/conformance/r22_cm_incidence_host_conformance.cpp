#include "r22_cases.hpp"

namespace {

[[nodiscard]] int verify_return(
    const holonics::organ::cm_incidence_receipt& receipt) noexcept {
  using namespace holonics;
  int failures = receipt.returned_translations != 5 || receipt.periodic.edge_count != 40 ||
      receipt.window.edge_count != 33 || receipt.projection.unit_pair_count != 33 ||
      receipt.projection.lost_count != 7 || receipt.projection.projection_loss != 0 ||
      !receipt.projection.factor_expansion_agree || !receipt.projection.basis_injective;
  const std::int64_t translations[5][4]{{1,0,0,0}, {0,1,0,0}, {0,0,1,0},
      {0,0,0,1}, {-1,-1,-1,-1}};
  const std::uint8_t masks[5]{1,2,4,8,15};
  const std::uint8_t populations[5]{8,8,8,8,1};
  for (std::uint8_t direction = 0; direction < 5; ++direction) {
    failures += !receipt.translations[direction].exact ||
        receipt.translations[direction].residue_mask != masks[direction] ||
        receipt.projection.direction_population[direction] != populations[direction];
    for (std::uint8_t slot = 0; slot < 4; ++slot) {
      failures += receipt.translations[direction].value.coefficients[slot] !=
          translations[direction][slot];
    }
  }
  const std::int64_t periodic[17]{1,0,-40,0,540,-384,-3480,5760,8070,-29440,
      17640,37120,-82020,74880,-37800,10368,-1215};
  const std::int64_t window[17]{1,0,-33,0,376,-48,-1984,576,4992,-2304,-4864,
      3072,0,0,0,0,0};
  for (std::uint8_t slot = 0; slot < 17; ++slot) {
    failures += receipt.periodic.characteristic[slot] != periodic[slot] ||
        receipt.window.characteristic[slot] != window[slot];
  }
  failures += receipt.periodic.factor_count != 3 || receipt.window.factor_count != 5 ||
      !receipt.scattering.interchange_broken;
  for (std::uint8_t axis = 0; axis < 4; ++axis) {
    failures += receipt.scattering.commutator_nonzero[axis] != 4 ||
        receipt.scattering.commutator_square[axis] != 4;
  }
  for (const auto& candidate : receipt.candidates) { failures += candidate.admitted; }
  return failures;
}

}  // namespace

int main() {
  using namespace holonics;
  const auto mount = tests::r22_case(tests::r22_host_blind_rest(), tests::r22_host_card());
  organ::cm_incidence_receipt receipt{};
  organ::cm_incidence_detail::form_translations(mount.foundation.card, receipt);
  organ::cm_incidence_detail::form_periodic(receipt);
  organ::cm_window_detail::form_window(receipt);
  organ::cm_window_detail::form_expanded_projection(receipt);
  organ::cm_window_detail::form_scattering(receipt);
  organ::cm_incidence_detail::form_characteristic(mount.foundation.card, receipt.periodic);
  organ::cm_incidence_detail::form_characteristic(mount.foundation.card, receipt.window);
  organ::cm_incidence_detail::form_candidates(receipt);
  organ::cm_incidence_detail::close_cm_incidence(
      mount.foundation, mount.question, receipt);
  int failures = verify_return(receipt);
  failures += !receipt.all_exact || !receipt.theory_formed;
  auto changed = mount.foundation.card;
  changed.translation_count = 4;
  organ::cm_incidence_receipt probe{};
  organ::cm_incidence_detail::form_translations(changed, probe);
  organ::cm_incidence_detail::form_periodic(probe);
  organ::cm_window_detail::form_window(probe);
  organ::cm_window_detail::form_expanded_projection(probe);
  organ::cm_incidence_detail::form_characteristic(changed, probe.periodic);
  organ::cm_incidence_detail::form_characteristic(changed, probe.window);
  failures += probe.periodic.edge_count != 32 || probe.window.edge_count != 32 ||
      probe.projection.lost_count != 0 ||
      probe.periodic.characteristic[2] == receipt.periodic.characteristic[2];
  return failures == 0 ? 0 : 1;
}

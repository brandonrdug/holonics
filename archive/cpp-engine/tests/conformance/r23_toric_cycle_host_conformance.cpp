#include "r23_cases.hpp"

namespace {

[[nodiscard]] bool rational(holonics::exact::small_rational value,
    std::int64_t numerator, std::int64_t denominator = 1) noexcept {
  return value.numerator == numerator && value.denominator == denominator;
}

}  // namespace

int main() {
  using namespace holonics;
  const auto mount = tests::r23_case(tests::r23_host_cm_rest(), tests::r23_host_card());
  organ::toric_cycle_receipt receipt{};
  organ::toric_cycle_detail::derive(mount.foundation, receipt);
  organ::toric_cycle_detail::close(mount.foundation, mount.question, receipt);
  int failures = !receipt.all_exact || !receipt.theory_formed ||
      !receipt.alternatives_retained || receipt.fans[0].source.ray_count != 3 ||
      receipt.fans[1].source.ray_count != 4 || receipt.quotients[0].rank != 1 ||
      receipt.quotients[1].rank != 2 || !receipt.intersections[1].fan_chow_agree ||
      receipt.intersections[1].positive != 1 || receipt.intersections[1].negative != 1 ||
      receipt.intersections[1].rank != 2 ||
      !receipt.comparisons[0].ranks_returned || !receipt.comparisons[1].ranks_returned ||
      receipt.comparisons[0].betti[2] != 1 || receipt.comparisons[1].hodge[1][1] != 2;
  failures += !rational(receipt.intersections[0].quotient_form[0][0], 1) ||
      !rational(receipt.intersections[1].quotient_form[0][0], 0) ||
      !rational(receipt.intersections[1].quotient_form[0][1], 1) ||
      !rational(receipt.intersections[1].quotient_form[1][1], 0) ||
      !rational(receipt.intersections[1].determinant, -1) ||
      !rational(receipt.intersections[1].congruence_form[0][0], 2) ||
      !rational(receipt.intersections[1].congruence_form[1][1], -2);
  failures += receipt.realizations[0].state != organ::toric_realization_state::integral ||
      !rational(receipt.realizations[0].class_coordinates[0], 2) ||
      !rational(receipt.realizations[0].class_coordinates[1], 3) ||
      receipt.realizations[1].state != organ::toric_realization_state::rational_only ||
      !rational(receipt.realizations[1].class_coordinates[0], 1, 2) ||
      receipt.realizations[2].state != organ::toric_realization_state::incompatible;
  failures += !rational(receipt.polarization.primitive_negative[0], 1) ||
      !receipt.source_polarization.exact ||
      !rational(receipt.source_polarization.primitive[0], 1) ||
      !rational(receipt.polarization.primitive_negative[1], -1) ||
      !rational(receipt.polarization.primitive_square, -2) ||
      receipt.blowup.derived_ray.x != 1 || receipt.blowup.derived_ray.y != 1 ||
      !rational(receipt.blowup.exceptional[0], -1) ||
      !rational(receipt.blowup.exceptional[1], 1) ||
      !rational(receipt.blowup.exceptional_square, -1) ||
      !rational(receipt.blowup.polarization.primitive_negative[0], 3) ||
      !rational(receipt.blowup.polarization.primitive_negative[1], -2) ||
      !rational(receipt.blowup.polarization.primitive_square, -8) ||
      !receipt.blowup.projection_formula || !receipt.blowup.comparison.ranks_returned ||
      !rational(receipt.blowup.transforms[0].total[0], 0) ||
      !rational(receipt.blowup.transforms[0].total[1], 1) ||
      !receipt.foils.principal_not_zero_support ||
      !receipt.foils.congruence_not_operator_conjugacy ||
      !receipt.foils.equal_class_not_equal_support;
  auto changed = mount.foundation;
  changed.card.targets[0].response[0].numerator = 4;
  changed.card.targets[0].response[2].numerator = 4;
  organ::toric_cycle_receipt probe{};
  organ::toric_cycle_detail::derive(changed, probe);
  failures += probe.realizations[0].state != organ::toric_realization_state::integral ||
      !rational(probe.realizations[0].class_coordinates[0], 2) ||
      !rational(probe.realizations[0].class_coordinates[1], 4) ||
      rational(probe.realizations[0].class_coordinates[1],
          receipt.realizations[0].class_coordinates[1].numerator);
  return failures == 0 ? 0 : 1;
}

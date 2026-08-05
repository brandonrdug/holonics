#include <holonics/organ/algebraic_variation_law.hpp>

namespace {

[[nodiscard]] constexpr holonics::organ::algebraic_variation_foundation foundation() noexcept {
  using namespace holonics;
  organ::algebraic_variation_foundation value{};
  value.ecology = exact::word{140'010'20}; value.family = exact::word{191'300};
  value.differential = exact::word{191'301}; value.connection = exact::word{191'302};
  value.invariant = exact::word{191'303}; value.loop = exact::word{191'304};
  value.theorem = exact::word{191'305}; value.provenance = exact::word{240'304};
  auto& card = value.card; card.schema = exact::word{240'024};
  card.occurrence = exact::word{191'300}; card.lineage = exact::word{240'304};
  card.coefficients[0] = {0, 0}; card.coefficients[1] = {0, 1};
  card.coefficients[2] = {-1, -1}; card.coefficients[3] = {1, 0};
  const exact::small_rational samples[7]{{-3,1},{-2,1},{-1,1},{1,2},{2,1},{3,1},{4,1}};
  for (std::uint8_t slot = 0; slot < 7; ++slot) { card.samples[slot] = samples[slot]; }
  card.root_min = -2; card.root_max = 2; card.form_min = -2; card.form_max = 2;
  card.degree = 3; card.cover_degree = 2; card.sample_count = 7;
  card.discovery_count = 5; card.series_depth = 6; card.parsed = true;
  return value;
}

}  // namespace

int main() {
  using namespace holonics;
  const auto receipt = organ::algebraic_variation_detail::derive(foundation(),
      {exact::word{191'310}, exact::word{191'311}, exact::word{191'312}});
  int failures = !receipt.all_exact || receipt.root_count != 3 ||
      receipt.collision_count != 2 || receipt.discriminant.degree != 4 ||
      receipt.discriminant.coefficients[2] != 1 ||
      receipt.discriminant.coefficients[3] != -2 ||
      receipt.discriminant.coefficients[4] != 1 ||
      receipt.connection.denominator_scale != 2 ||
      receipt.connection.numerator[0][0].parameter != 1 ||
      receipt.connection.numerator[0][1].constant != -1 ||
      receipt.connection.numerator[1][0].parameter != 1 ||
      receipt.connection.numerator[1][1].parameter != -1 ||
      receipt.invariant.selected[0][1] != 1 ||
      receipt.invariant.selected[1][0] != -1;
  failures += receipt.scalar.second[0] != 0 || receipt.scalar.second[1] != 4 ||
      receipt.scalar.second[2] != -4 || receipt.scalar.first[0] != 4 ||
      receipt.scalar.first[1] != -8 || receipt.scalar.zeroth != -1 ||
      receipt.scalar.series[1].numerator != 1 || receipt.scalar.series[1].denominator != 4 ||
      receipt.scalar.series[2].numerator != 9 || receipt.scalar.series[2].denominator != 64;
  failures += receipt.loops.monodromy[0][0][1] != 2 ||
      receipt.loops.monodromy[1][1][0] != -2 ||
      receipt.loops.monodromy[2][0][1] != -2 ||
      receipt.loops.monodromy[2][1][0] != 2 ||
      receipt.selection.selected.value() == 0;
  auto changed = foundation(); changed.card.coefficients[1].parameter = 2;
  const auto probe = organ::algebraic_variation_detail::derive(changed,
      {exact::word{191'320}, exact::word{191'321}, exact::word{191'322}});
  failures += probe.all_exact || probe.obstruction == organ::variation_obstruction::none ||
      probe.selection.selected.value() != 0;
  return failures == 0 ? 0 : 1;
}

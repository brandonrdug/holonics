#include "r27_cases.hpp"

namespace {

[[nodiscard]] std::int64_t fifth(std::int64_t value) noexcept {
  return value * value * value * value * value;
}

[[nodiscard]] std::int64_t independent_resultant(
    std::int64_t parameter, std::int64_t constant) noexcept {
  return 3125 * constant * constant * constant * constant - 256 * fifth(parameter);
}

}  // namespace

int main() {
  using namespace holonics; const auto mount = tests::r27_case({}, tests::r27_host_card());
  organ::expression_geometry_receipt inquiry{}; inquiry.question = mount.question;
  for (std::uint8_t slot = 0; slot < 3; ++slot) {
    organ::expression_geometry_detail::derive_presentation(
        mount.foundation, slot, inquiry.presentations[slot]);
  }
  organ::expression_geometry_detail::compose(mount.foundation, inquiry);
  organ::expression_changed_receipt changed{};
  organ::expression_geometry_detail::derive_changed(mount.changed_foundation, changed);
  changed.discriminant_changed = !organ::expression_exact_detail::same_polynomial(
      inquiry.presentations[0].ideal.resultant, changed.presentations[0].ideal.resultant);
  changed.series_changed = !organ::expression_exact_detail::equal(
      inquiry.presentations[0].scalar.series[0][5],
      changed.presentations[0].scalar.series[0][5]);
  changed.source_sensitive = changed.exact && changed.discriminant_changed && changed.series_changed;
  inquiry.controls.changed_source_sensitive = changed.source_sensitive;
  inquiry.controls.exact = inquiry.controls.exact && changed.source_sensitive;
  inquiry.all_exact = inquiry.all_exact && changed.source_sensitive;
  inquiry.theory_formed = inquiry.all_exact;
  const auto surface = event::expression_geometry_surface(inquiry, changed, changed.source_sensitive);
  codec::expression_geometry_formal_face formal{};
  codec::expression_geometry_explanation explanation{}; int failures = !inquiry.all_exact ||
      !inquiry.theory_formed || !changed.source_sensitive || !codec::render_expression_geometry(
          surface, formal) || !codec::render_expression_geometry_explanation(surface, explanation);
  const std::int64_t constants[3]{1,1,-1};
  for (std::uint8_t slot = 0; slot < 3; ++slot) {
    const auto& value = inquiry.presentations[slot];
    failures += !value.exact || value.ideal.constant_parameter != constants[slot] ||
        value.ideal.resultant.coefficients[0] != independent_resultant(0, constants[slot]) ||
        value.ideal.resultant.coefficients[5] != -256 ||
        value.scalar.coefficients[4].coefficients[0] != 50000 ||
        value.scalar.coefficients[4].coefficients[5] != -4096 ||
        value.scalar.coefficients[3].coefficients[4] != -61440 ||
        value.scalar.coefficients[2].coefficients[3] != -247680 ||
        value.scalar.coefficients[1].coefficients[2] != -264000 ||
        value.scalar.coefficients[0].coefficients[1] != -29601 ||
        !value.residue.rank_one || !value.residue.square_zero;
    for (std::int64_t parameter = -4; parameter <= 6; ++parameter) {
      exact::small_rational actual{};
      failures += !organ::expression_exact_detail::evaluate(value.ideal.resultant,
          {parameter,1}, actual) || actual.numerator !=
          independent_resultant(parameter, constants[slot]) || actual.denominator != 1;
    }
  }
  failures += changed.presentations[0].ideal.constant_parameter != 2 ||
      changed.presentations[0].ideal.resultant.coefficients[0] != 50000 ||
      changed.presentations[0].scalar.coefficients[4].coefficients[0] != 800000 ||
      !inquiry.rational_rechart.rational || !inquiry.gaussian_rechart.gaussian ||
      inquiry.rational_rechart.x_shift != 1 || inquiry.gaussian_rechart.x_scale != -1 ||
      inquiry.gaussian_rechart.y_square != -1 || inquiry.invariant_fiber.member_count != 3;
  return failures == 0 ? 0 : 1;
}

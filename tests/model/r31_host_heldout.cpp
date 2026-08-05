#include <holonics/organ/cultivated_organ_application_law.hpp>

#include "r31_host_reference.hpp"

namespace holonics::tests {
std::size_t r31_heldout_reference_failures() noexcept {
  organ::cultivated_shift_organ organs[4]{};
  const std::int64_t coefficients[4][6]{{1,1,-2,-1},{1,4,4,-4,-8,-4},{5,-2,1},{1,-3,3,-1}};
  const std::uint8_t orders[4]{1,1,2,3}, degrees[4]{1,2,0,0}, features[4]{4,6,3,4};
  for (std::uint8_t f = 0; f < 4; ++f) {
    organs[f].order=orders[f]; organs[f].degree=degrees[f]; organs[f].features=features[f];
    organs[f].minimum_prefix=orders[f]; organs[f].checker_founded=true;
    for (std::uint8_t i=0;i<features[f];++i) organs[f].coefficients[i]=coefficients[f][i];
  }
  organ::star_structure_card star{}; star.first_branch_count=1; star.last_branch_count=10;
  star.common_conductance=1; star.changed_conductance=2;
  organ::walk_structure_card walk{}; walk.step_count=4; walk.maximum_half_horizon=8;
  const std::int8_t steps[4][2]{{1,0},{-1,0},{0,1},{0,-1}};
  for(std::uint8_t i=0;i<4;++i){walk.steps[i][0]=steps[i][0];walk.steps[i][1]=steps[i][1];}
  organ::signed_carrier_card carrier{}; carrier.maximum_horizon=8;
  const std::int16_t matrix[4]{1,-2,2,1}; for(std::uint8_t i=0;i<4;++i)carrier.matrix[i]=matrix[i];
  carrier.changed_slot=1;carrier.changed_value=-3;
  organ::graded_structure_card graded{};graded.generators=2;graded.maximum_horizon=8;graded.changed_generators=3;
  organ::tail_receipt tails[4]{};
  organ::cultivated_application_detail::derive_star(star,organs[0],tails[0]);
  organ::cultivated_application_detail::derive_walk(walk,organs[1],tails[1]);
  organ::cultivated_application_detail::derive_carrier(carrier,organs[2],tails[2]);
  organ::cultivated_application_detail::derive_graded(graded,organs[3],tails[3]);
  std::size_t failures=0; const std::int64_t trace[9]{2,2,-6,-22,-14,82,234,58,-1054};
  for(std::uint8_t n=0;n<10;++n) failures += !exact::small_rational_law::equal(tails[0].source[n],exact::small_rational_law::make(1,n+2));
  std::int64_t choose=1,denominator=1;
  for(std::uint8_t n=0;n<9;++n){if(n>0){choose=choose*(4*n-2)/n;denominator*=16;}
    failures += !exact::small_rational_law::equal(tails[1].source[n],exact::small_rational_law::make(choose*choose,denominator));
    failures += tails[2].source[n].numerator!=trace[n];
    failures += tails[3].source[n].numerator!=static_cast<std::int64_t>((n+1U)*(n+2U)/2U);}
  for(const auto &tail:tails) failures += !tail.exact ||
      tail.changed_source!=organ::cultivation_obstruction::heldout_residual;
  return failures;
}
}  // namespace holonics::tests

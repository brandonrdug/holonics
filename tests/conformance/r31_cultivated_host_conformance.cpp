#include <holonics/organ/shift_organ_cultivation_law.hpp>

#include "r31_host_reference.hpp"

int main() {
  holonics::organ::developmental_stream_card cards[4]{};
  holonics::tests::r31_development_cards(cards);
  constexpr std::uint8_t orders[9]{1,2,1,3,1,2,3,2,3};
  constexpr std::uint8_t degrees[9]{0,0,1,0,2,1,1,2,2};
  std::size_t failures = 0;
  for (std::uint8_t family=0;family<4;++family) for(std::uint8_t i=0;i<9;++i) {
    holonics::exact::small_rational matrix[28][12]{};
    holonics::organ::feature_geometry_receipt actual{};
    holonics::organ::shift_cultivation_detail::derive_candidate(
        cards[family],orders[i],degrees[i],matrix,actual);
    const auto expected=holonics::tests::r31_reference_candidate(cards[family],orders[i],degrees[i]);
    failures += actual.rows!=expected.rows || actual.rank!=expected.rank ||
        actual.nullity!=expected.nullity || actual.obstruction!=expected.obstruction;
    for(std::uint8_t k=0;k<actual.features;++k) failures += actual.coefficients[k]!=expected.coefficients[k];
  }
  failures += holonics::tests::r31_heldout_reference_failures();
  return failures == 0 ? 0 : 1;
}

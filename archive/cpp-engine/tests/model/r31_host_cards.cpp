#include "r31_host_reference.hpp"

namespace holonics::tests {
namespace rational = exact::small_rational_law;

void r31_development_cards(
    organ::developmental_stream_card (&cards)[organ::cultivation_family_count]) noexcept {
  const std::int64_t numerators[4][4][8]{
      {{1,1,1,1,1,1,1,1}},
      {{1,1,9,25,1225,3969,53361}},
      {{2,2,-6,-22,-14,82,234}},
      {{1,11,33,67,113},{1,12,35,70,117},{1,12,33,64,105},{1,13,40,82,139}}};
  const std::int64_t denominators[4][8]{
      {1,2,3,4,5,6,7,8}, {1,4,64,256,16384,65536,1048576,1},
      {1,1,1,1,1,1,1,1}, {1,1,1,1,1,1,1,1}};
  const std::uint8_t series_counts[4]{1,1,1,4}, sample_counts[4]{8,7,7,5};
  for (std::uint8_t family = 0; family < 4; ++family) {
    auto &card = cards[family]; card.metadata.parsed = true;
    card.metadata.lineage = exact::word{410'131U + family};
    card.family = static_cast<organ::cultivation_family>(family);
    card.series_count = series_counts[family]; card.maximum_order = 3; card.maximum_degree = 2;
    for (std::uint8_t series = 0; series < card.series_count; ++series) {
      card.sample_count[series] = sample_counts[family];
      for (std::uint8_t i = 0; i < card.sample_count[series]; ++i)
        card.samples[series][i] = rational::make(
            numerators[family][series][i], denominators[family][i]);
    }
  }
}

}  // namespace holonics::tests

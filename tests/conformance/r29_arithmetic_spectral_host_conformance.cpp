#include "r29_reference.hpp"

int main() {
  const auto result = holonics::tests::r29_reference();
  const std::uint32_t expected[7][4]{{4,32,148,640},{8,32,104,640},
      {20,160,2180,28800},{8,160,2216,28800},{10,180,2290,28800},
      {20,160,2180,28800},{18,180,2106,28800}};
  const std::int8_t gaussian[7][2]{{1,2},{-1,-2},{-3,-2},{3,2},{2,-3},{-3,-2},{-2,3}};
  std::size_t failures = !result.exact;
  for (std::uint8_t curve = 0; curve < 7; ++curve) {
    failures += result.curves[curve].real != gaussian[curve][0] ||
        result.curves[curve].imaginary != gaussian[curve][1];
    for (std::uint8_t degree = 0; degree < 4; ++degree) {
      failures += result.curves[curve].counts[degree] != expected[curve][degree];
    }
  }
  return failures == 0 ? 0 : 1;
}

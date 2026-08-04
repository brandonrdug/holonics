#include "r11_oracle.hpp"

namespace holonics::tests {
r11_expected r11_oracle() noexcept {
  return {{112'010, 112'020, 112'030, 112'040, 112'050, 112'060, 112'070},
      7, 10, 4, 1, 111'070, 111'071};
}
}  // namespace holonics::tests

#include "r10_oracle.hpp"

namespace holonics::tests {
r10_expected r10_oracle() noexcept {
  return {10'001'000U, 11'001'000U, 10'001'001U, 10'002'000U,
      5U, 8U, 2U, 14U, 4U, 1U, 16U, 3U};
}
}  // namespace holonics::tests

#include "r9_oracle.hpp"

namespace holonics::tests {

r9_expected r9_oracle() noexcept {
  return {9'001'000U, 10'001'000U, 9'001'001U, 9'000U, 90'000U,
      9'001U, 9'002U, 9'401U, 42U, 40U, 4U, 2U, 45U, 37U, 4U, 5U, 45U};
}

}  // namespace holonics::tests

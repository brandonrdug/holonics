#include "r10_cases.hpp"

#include <cstddef>

namespace holonics::tests {

apparatus::conditioning_mount r10_case() noexcept {
  apparatus::conditioning_mount mount{};
  mount.foundation.admitted_tally = {exact::word{10'001}, exact::word{100'001},
      exact::word{2}, exact::word{1}, exact::word{0}, exact::word{0}, exact::word{1}};
  mount.foundation.production_seed = 10'001'000U;
  mount.foundation.ablation_seed = 10'002'000U;
  for (std::size_t slot = 0; slot < body::live_region_capacity; ++slot) {
    mount.foundation.regions[slot] = {10U + slot, 0};
  }
  mount.passage.exposure = {exact::word{10'100}, exact::word{10'101},
      exact::word{10'102}, exact::word{10'103}, exact::word{2}, exact::word{1}, exact::word{3}};
  mount.passage.training = {exact::word{10'200}, exact::word{10'201}, exact::word{10'202},
      exact::word{3}, exact::word{2}, exact::word{1}, exact::word{1}, exact::word{3}};
  mount.passage.reference = {exact::word{10'300}, exact::word{10'301}, exact::word{777}};
  mount.held_out = {exact::word{10'400}, exact::word{10'401},
      exact::word{3}, exact::word{2}, exact::word{2}};
  return mount;
}

}  // namespace holonics::tests

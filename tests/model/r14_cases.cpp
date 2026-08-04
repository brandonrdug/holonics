#include "r14_cases.hpp"

#include <cstddef>

namespace holonics::tests {

apparatus::theorem_production_mount r14_case() noexcept {
  apparatus::theorem_production_mount mount{};
  mount.foundation.ecology = exact::word{111'001};
  mount.foundation.trace_declaration = exact::word{112'001};
  mount.foundation.trace_trans_declaration = exact::word{112'033};
  mount.foundation.rebase_declaration = exact::word{112'015};
  mount.foundation.trace_rebase_declaration = exact::word{112'023};
  mount.foundation.provenance = exact::word{111'106};
  mount.foundation.rules[0] = {exact::word{141'010}, exact::word{141'011},
      organ::theorem_formation::compose_then_transport, 3};
  mount.foundation.rules[1] = {exact::word{141'020}, exact::word{141'021},
      organ::theorem_formation::transport_then_compose, 4};
  mount.question = {exact::word{141'200}, exact::word{141'201},
      exact::word{141'202}, exact::word{141'203}, 3};
  mount.held_probe = {exact::word{141'300}, exact::word{141'301},
      exact::word{181'200}, exact::word{141'302}, 3};
  mount.regions[0] = {128, 150'100};
  for (std::size_t slot = 1; slot < body::live_region_capacity; ++slot) {
    mount.regions[slot] = {128U + slot, 0};
  }
  mount.body_seed = 14'001'000;
  mount.mathematical_morphology = 43;
  mount.codec_morphology = 32;
  return mount;
}

}  // namespace holonics::tests

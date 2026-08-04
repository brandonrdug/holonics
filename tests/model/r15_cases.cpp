#include "r15_cases.hpp"

namespace holonics::tests {

apparatus::return_conditioning_mount r15_case(
    const event::theorem_production_rest_record& inherited) noexcept {
  apparatus::return_conditioning_mount mount{};
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
  mount.inherited = inherited;
  mount.question = {exact::word{142'200}, exact::word{142'201},
      exact::word{181'200}, exact::word{142'202}, 3};
  return mount;
}

}  // namespace holonics::tests

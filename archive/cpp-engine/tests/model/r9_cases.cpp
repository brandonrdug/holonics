#include "r9_cases.hpp"

#include <cstddef>

namespace holonics::tests {

apparatus::reflective_codec_mount r9_case(
    const codec::codec_environment& environment,
    const apparatus::codec_store_receipt& original,
    const apparatus::codec_store_receipt& relocated) noexcept {
  apparatus::reflective_codec_mount mount{};
  mount.environment = environment;
  mount.body_seed = 9'001'000U;
  mount.source_detached = true;
  mount.original_material = original.material_testimony;
  mount.relocated_material = relocated.material_testimony;
  mount.original_path = original.path_testimony;
  mount.relocated_path = relocated.path_testimony;
  for (std::size_t slot = 0; slot < body::live_region_capacity; ++slot) {
    mount.regions[slot] = {0};
  }
  mount.deed.probe = {exact::word{40}, exact::word{0}};
  mount.deed.render_core = exact::word{42};
  mount.deed.reflection_occurrence = exact::word{90'500};
  mount.deed.reflection_lineage = exact::word{90'600};
  mount.deed.revision.occurrence = exact::word{90'700};
  mount.deed.revision.return_port = exact::word{9'302};
  mount.deed.revision.lineage = exact::word{90'800};
  mount.deed.revision.next_version = exact::word{2};
  mount.deed.revision.next_bias = exact::word{5};
  return mount;
}

}  // namespace holonics::tests

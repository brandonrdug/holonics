#include "r12_cases.hpp"

#include <cstddef>

namespace holonics::tests {

apparatus::generative_math_mount r12_case() noexcept {
  apparatus::generative_math_mount mount{};
  mount.foundation.ecology = exact::word{111'001};
  mount.foundation.premise_declaration = exact::word{112'070};
  mount.foundation.premise_type = exact::word{111'070};
  mount.foundation.premise_proof = exact::word{111'071};
  mount.foundation.provenance = exact::word{111'106};
  mount.foundation.conditioning = {exact::word{10'001}, exact::word{100'001},
      exact::word{2}, exact::word{1}, exact::word{0}, exact::word{0}, exact::word{1}};
  mount.foundation.rules[0] = {exact::word{121'010}, exact::word{121'011},
      exact::word{121'012}, organ::proof_formation::equivalence_symmetry, 1};
  mount.foundation.rules[1] = {exact::word{121'020}, exact::word{121'021},
      exact::word{121'022}, organ::proof_formation::paired_implications, 4};
  for (std::size_t slot = 0; slot < body::live_region_capacity; ++slot) {
    mount.regions[slot] = {120U + slot, 0};
  }
  mount.question = {exact::word{120'100}, exact::word{120'200}, exact::word{112'070},
      exact::word{111'070}, exact::word{120'300}, 1,
      receiver::equivalence_orientation::reverse};
  mount.body_seed = 12'001'000U;
  return mount;
}

}  // namespace holonics::tests

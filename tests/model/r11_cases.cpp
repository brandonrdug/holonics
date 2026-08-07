#include "r11_cases.hpp"

#include <cstddef>

namespace holonics::tests {
namespace {

using organ::dependency_role;
using organ::term_constructor;

organ::mathematical_foundation canonical_foundation(std::uint64_t testimony) noexcept {
  organ::mathematical_foundation value{};
  value.environment = exact::word{111'001};
  value.kernel_declarations = exact::word{111'002};
  value.provenance = exact::word{111'003};
  value.source_material_testimony = exact::word{testimony};
  value.term_count = 13;
  value.declaration_count = 7;
  value.dependency_count = 10;
  value.terms[0] = {exact::word{111'000}, exact::word{111'000}, exact::word{111'003},
      term_constructor::sort, 0, 0, false, false};
  value.terms[1] = {exact::word{111'010}, exact::word{111'000}, exact::word{111'100},
      term_constructor::constant, 0, 0, false, false};
  value.terms[2] = {exact::word{111'020}, exact::word{111'000}, exact::word{111'101},
      term_constructor::implication, 1, 1, true, true};
  value.terms[3] = {exact::word{111'021}, exact::word{111'020}, exact::word{111'101},
      term_constructor::proof, 1, 0, true, false};
  value.terms[4] = {exact::word{111'030}, exact::word{111'000}, exact::word{111'102},
      term_constructor::implication, 1, 1, true, true};
  value.terms[5] = {exact::word{111'031}, exact::word{111'030}, exact::word{111'102},
      term_constructor::proof, 1, 0, true, false};
  value.terms[6] = {exact::word{111'040}, exact::word{111'000}, exact::word{111'103},
      term_constructor::constant, 0, 0, false, false};
  value.terms[7] = {exact::word{111'050}, exact::word{111'000}, exact::word{111'104},
      term_constructor::implication, 6, 6, true, true};
  value.terms[8] = {exact::word{111'051}, exact::word{111'050}, exact::word{111'104},
      term_constructor::proof, 6, 0, true, false};
  value.terms[9] = {exact::word{111'060}, exact::word{111'000}, exact::word{111'105},
      term_constructor::implication, 7, 1, true, true};
  value.terms[10] = {exact::word{111'061}, exact::word{111'060}, exact::word{111'105},
      term_constructor::proof, 8, 3, true, true};
  value.terms[11] = {exact::word{111'070}, exact::word{111'000}, exact::word{111'106},
      term_constructor::implication, 9, 6, true, true};
  value.terms[12] = {exact::word{111'071}, exact::word{111'070}, exact::word{111'106},
      term_constructor::proof, 10, 8, true, true};

  value.declarations[0] = {exact::word{112'010}, exact::word{111'100}, 1, 0, 0, 0, false, false};
  value.declarations[1] = {exact::word{112'020}, exact::word{111'101}, 2, 3, 0, 1, true, true};
  value.declarations[2] = {exact::word{112'030}, exact::word{111'102}, 4, 5, 1, 1, true, true};
  value.declarations[3] = {exact::word{112'040}, exact::word{111'103}, 6, 0, 2, 0, false, false};
  value.declarations[4] = {exact::word{112'050}, exact::word{111'104}, 7, 8, 2, 1, true, true};
  value.declarations[5] = {exact::word{112'060}, exact::word{111'105}, 9, 10, 3, 3, true, true};
  value.declarations[6] = {exact::word{112'070}, exact::word{111'106}, 11, 12, 6, 4, true, true};
  value.dependencies[0] = {0, dependency_role::proof_support, exact::word{113'001}, exact::word{114'001}};
  value.dependencies[1] = {0, dependency_role::proof_support, exact::word{113'002}, exact::word{114'002}};
  value.dependencies[2] = {3, dependency_role::definition_incidence, exact::word{113'003}, exact::word{114'003}};
  value.dependencies[3] = {4, dependency_role::lemma_transport, exact::word{113'004}, exact::word{114'004}};
  value.dependencies[4] = {1, dependency_role::lemma_transport, exact::word{113'005}, exact::word{114'005}};
  value.dependencies[5] = {0, dependency_role::type_incidence, exact::word{113'006}, exact::word{114'006}};
  value.dependencies[6] = {5, dependency_role::lemma_transport, exact::word{113'007}, exact::word{114'007}};
  value.dependencies[7] = {4, dependency_role::definition_incidence, exact::word{113'008}, exact::word{114'008}};
  value.dependencies[8] = {3, dependency_role::type_incidence, exact::word{113'009}, exact::word{114'009}};
  value.dependencies[9] = {2, dependency_role::lemma_transport, exact::word{113'010}, exact::word{114'010}};
  return value;
}

organ::mathematical_foundation reordered_foundation(
    const organ::mathematical_foundation& source) noexcept {
  organ::mathematical_foundation value = source;
  constexpr std::uint16_t old_at_new[7]{4, 1, 5, 0, 3, 2, 6};
  constexpr std::uint16_t new_for_old[7]{3, 1, 5, 4, 0, 2, 6};
  value.dependency_count = 0;
  for (std::size_t new_slot = 0; new_slot < 7; ++new_slot) {
    const auto& old = source.declarations[old_at_new[new_slot]];
    auto declaration = old;
    declaration.dependency_begin = value.dependency_count;
    for (std::size_t offset = 0; offset < old.dependency_count; ++offset) {
      auto dependency = source.dependencies[old.dependency_begin + offset];
      dependency.target_slot = new_for_old[dependency.target_slot];
      value.dependencies[value.dependency_count++] = dependency;
    }
    value.declarations[new_slot] = declaration;
  }
  return value;
}

}  // namespace

apparatus::mathematical_ecology_mount r11_case(std::uint64_t material_testimony) noexcept {
  apparatus::mathematical_ecology_mount mount{};
  mount.canonical = canonical_foundation(material_testimony);
  mount.reordered = reordered_foundation(mount.canonical);
  for (std::size_t slot = 0; slot < body::live_region_capacity; ++slot) {
    mount.regions[slot] = {0};
  }
  mount.held_out = {exact::word{115'001}, exact::word{115'002}, 6,
      exact::word{111'070}, exact::word{111'070}, exact::word{115'003}, false};
  mount.mismatch = mount.held_out;
  mount.mismatch.identity = exact::word{115'004};
  mount.mismatch.target_type = exact::word{119'999};
  mount.unsolved = mount.held_out;
  mount.unsolved.identity = exact::word{115'005};
  mount.unsolved.request_generated_closure = true;
  mount.canonical_body_seed = 11'001'000U;
  mount.reordered_body_seed = 11'002'000U;
  return mount;
}

}  // namespace holonics::tests

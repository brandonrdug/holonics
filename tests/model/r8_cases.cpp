#include "r8_cases.hpp"

#include <cstddef>
#include <cstdint>

namespace holonics::tests {

apparatus::boundary_condensation_mount r8_case() noexcept {
  apparatus::boundary_condensation_mount mount{};
  auto& program = mount.program;
  program.identity = exact::word{8'001};
  program.predecessor = exact::word{8'001'000};
  program.incidence = exact::word{8'001'001};
  program.lineage = exact::word{100};
  program.morphology = exact::word{10};
  program.logical_resource = exact::word{0};
  program.alternatives = exact::word{2};
  program.reconstruction_capability = exact::word{8'009'001};
  program.refinement_occurrence = exact::word{8'002'099};
  program.refinement_lineage = exact::word{10};
  program.source_count = 8;
  program.initial_group_count = 3;
  program.refined_group_count = 4;
  program.refinement_after_history = 2;
  const std::uint64_t values[8]{2, 3, 5, 7, 11, 13, 17, 19};
  const std::uint16_t initial_groups[8]{0, 0, 0, 1, 1, 1, 2, 2};
  const std::uint16_t refined_groups[8]{0, 1, 1, 2, 2, 2, 3, 3};
  const std::uint64_t weights[3][8]{
      {1, 1, 1, 2, 2, 2, 3, 3},
      {4, 4, 4, 5, 5, 5, 6, 6},
      {7, 8, 8, 9, 9, 9, 10, 10}};
  for (std::size_t source = 0; source < 8; ++source) {
    program.source_identities[source] = exact::word{801U + source};
    program.source_values[source] = exact::word{values[source]};
    program.initial_groups[source] = initial_groups[source];
    program.refined_groups[source] = refined_groups[source];
    for (std::size_t query = 0; query < 3; ++query) {
      program.initial_family.query_weights[query][source] = exact::word{weights[query][source]};
      program.refined_family.query_weights[query][source] = exact::word{weights[query][source]};
    }
  }
  program.initial_family.identity = exact::word{8'101};
  program.initial_family.version = exact::word{1};
  program.initial_family.admitted_input_support = exact::word{255};
  program.initial_family.query_count = 2;
  program.refined_family.identity = exact::word{8'102};
  program.refined_family.version = exact::word{2};
  program.refined_family.admitted_input_support = exact::word{255};
  program.refined_family.query_count = 3;
  program.history[0] = {exact::word{8'201}, exact::word{8'301}, exact::word{1},
      exact::word{2}, exact::word{1}, 1, 0};
  program.history[1] = {exact::word{8'202}, exact::word{8'302}, exact::word{2},
      exact::word{3}, exact::word{1}, 4, 1};
  program.history[2] = {exact::word{8'203}, exact::word{8'303}, exact::word{3},
      exact::word{5}, exact::word{2}, 0, 2};
  program.history[3] = {exact::word{8'204}, exact::word{8'304}, exact::word{4},
      exact::word{7}, exact::word{2}, 7, 0};
  for (std::size_t region = 0; region < body::live_region_capacity; ++region) {
    mount.body_regions[region] = {30U + region, 0};
  }
  return mount;
}

}  // namespace holonics::tests

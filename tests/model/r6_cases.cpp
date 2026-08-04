#include "r6_cases.hpp"

#include <cstddef>
#include <cstdint>

namespace holonics::tests {
namespace {

current::weave_program make_program(std::uint64_t identity, bool alternative) noexcept {
  current::weave_program program{};
  program.identity = exact::word{identity};
  program.predecessor = exact::word{identity * 1'000U};
  program.incidence = exact::word{identity * 1'000U + 1U};
  program.lineage_seed = exact::word{3};
  program.logical_capacity = exact::word{32};
  program.cell_count = 9;
  program.event_count = 10;
  program.interaction_left = 7;
  program.interaction_right = 8;
  program.recurrence_first = 0;
  program.recurrence_second = 9;
  program.layer_count = 6;
  const std::uint16_t layer_offsets[6]{0, 1, 2, 4, 7, 9};
  const std::uint16_t layer_counts[6]{1, 1, 2, 3, 2, 1};
  for (std::size_t layer = 0; layer < 6; ++layer) {
    program.layer_offsets[layer] = layer_offsets[layer];
    program.layer_counts[layer] = layer_counts[layer];
  }
  for (std::size_t cell = 0; cell < program.cell_count; ++cell) {
    program.cells[cell] = {exact::word{identity * 100U + cell + 1U},
        exact::word{100U + cell}, exact::word{10U + cell}, exact::word{0},
        exact::word{identity * 10U + cell}, 1, 8};
  }
  const std::uint64_t deltas[10]{3, 5, 7, 11, 13, 17, 19, 23, 29, 31};
  const std::uint16_t cells[10]{0, 1, 2, 3, 4, 5, 6, 7, 7, 0};
  for (std::size_t slot = 0; slot < program.event_count; ++slot) {
    const std::uint64_t support = std::uint64_t{1} << cells[slot];
    program.events[slot] = {exact::word{identity * 1'000U + 100U + slot},
        exact::word{identity * 1'000U + 200U + slot},
        exact::word{identity * 1'000U + 300U + slot},
        exact::word{identity * 1'000U + 400U + slot},
        exact::word{support}, exact::word{support}, exact::word{deltas[slot]},
        exact::word{slot + 1U}, exact::word{1'000U + slot},
        exact::word{2'000U + slot}, exact::word{slot + 1U}, exact::word{1},
        exact::word{0}, cells[slot]};
  }
  const exact::word intermediate{identity * 1'000U + 900U};
  program.events[0].output_port = intermediate;
  program.events[1].input_port = intermediate;
  program.events[7].interaction = exact::word{identity * 1'000U + 777U};
  program.events[8].interaction = program.events[7].interaction;
  program.unproved_left_support = exact::word{std::uint64_t{1} << 8U};
  program.unproved_right_support = program.unproved_left_support;
  const std::uint16_t orders[4][10]{
      {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
      {0, 2, 4, 7, 8, 3, 5, 6, 1, 9},
      {4, 5, 6, 2, 3, 0, 1, 7, 8, 9},
      {0, 1, 3, 2, 6, 5, 4, 7, 8, 9}};
  const std::uint16_t partitions[4]{1, 2, 4, 3};
  for (std::size_t variant = 0; variant < 4; ++variant) {
    program.variant_partitions[variant] = partitions[variant];
    for (std::size_t position = 0; position < 10; ++position) {
      program.variant_orders[variant][position] = orders[variant][position];
    }
  }
  const exact::word resource_port{identity * 1'000U + 950U};
  program.resource = {resource_port, exact::word{500}, exact::word{320'000},
      2, 4, alternative};
  program.returned_resource = {exact::word{identity * 1'000U + 951U}, resource_port,
      exact::word{identity * 1'000U + 952U}, exact::word{400}, exact::word{600},
      exact::word{330'000}};
  for (std::size_t region = 0; region < body::live_region_capacity; ++region) {
    program.body_regions[region] = {20U + region, 0};
  }
  return program;
}

}  // namespace

current::weave_mount_batch r6_cases() noexcept {
  current::weave_mount_batch batch{};
  batch.count = 2;
  batch.programs[0] = make_program(6'001, true);
  batch.programs[1] = make_program(6'002, false);
  return batch;
}

}  // namespace holonics::tests

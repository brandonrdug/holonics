#include "r5_cases.hpp"

#include <cstddef>
#include <cstdint>

namespace holonics::tests {
namespace {

current::causal_program base_program(
    std::uint64_t identity,
    std::uint16_t sites,
    std::uint16_t arcs,
    std::uint16_t currents,
    std::uint8_t components,
    std::uint8_t fronts) noexcept {
  current::causal_program program{};
  program.identity = exact::word{identity};
  program.predecessor = exact::word{identity * 1'000U};
  program.input_port = exact::word{identity * 1'000U + 101U};
  program.output_port = exact::word{identity * 1'000U + 102U};
  program.lineage = exact::word{identity * 1'000U + 200U};
  program.next_occurrence = exact::word{identity * 1'000U + 1'000U};
  program.next_event = exact::word{identity * 1'000U + 2'000U};
  program.site_count = sites;
  program.arc_count = arcs;
  program.initial_current_count = currents;
  program.resource_obligation = 16;
  program.component_count = components;
  program.receiver_front_aperture = fronts;
  for (std::size_t slot = 0; slot < body::live_region_capacity; ++slot) {
    program.body_regions[slot] = {0};
  }
  for (std::size_t slot = 0; slot < sites; ++slot) {
    const std::uint64_t support = std::uint64_t{1} << slot;
    program.receiver_support = exact::word{program.receiver_support.value() | support};
    program.sites[slot].identity = exact::word{identity * 10U + slot + 1U};
    program.sites[slot].support = exact::word{support};
    program.morphology[slot] = {exact::word{2}, exact::word{1}, exact::word{0}};
  }
  return program;
}

void set_current(current::causal_program& program,
    std::size_t slot,
    std::uint16_t site,
    std::uint64_t state) noexcept {
  program.initial_currents[slot] = {exact::word{program.identity.value() * 100U + slot + 1U},
      exact::word{program.lineage.value() + slot + 1U}, exact::word{state},
      program.sites[site].support, site, 0, 1, program.sites[site].component, false};
}

current::causal_program serial_rest() noexcept {
  auto program = base_program(5'001, 4, 3, 1, 1, 6);
  program.sites[0].first_arc = 0; program.sites[0].arc_count = 1;
  program.sites[1].first_arc = 1; program.sites[1].arc_count = 1;
  program.sites[2].first_arc = 2; program.sites[2].arc_count = 1;
  program.sites[3].first_arc = 3;
  program.arcs[0] = {exact::word{51'001}, exact::word{52'001}, 1, 1};
  program.arcs[1] = {exact::word{51'002}, exact::word{52'002}, 2, 1};
  program.arcs[2] = {exact::word{51'003}, exact::word{52'003}, 3, 1};
  program.morphology[0] = {exact::word{2}, exact::word{1}, {}};
  program.morphology[1] = {exact::word{3}, exact::word{2}, {}};
  program.morphology[2] = {exact::word{2}, exact::word{3}, {}};
  program.morphology[3] = {exact::word{1}, exact::word{4}, {}};
  set_current(program, 0, 0, 2);
  return program;
}

current::causal_program parallel_rest() noexcept {
  auto program = base_program(5'002, 4, 2, 2, 2, 4);
  program.sites[0].first_arc = 0; program.sites[0].arc_count = 1;
  program.sites[1].first_arc = 1; program.sites[1].arc_count = 1;
  program.sites[2].first_arc = 2;
  program.sites[3].first_arc = 2;
  program.sites[0].component = 0; program.sites[2].component = 0;
  program.sites[1].component = 1; program.sites[3].component = 1;
  program.arcs[0] = {exact::word{51'101}, exact::word{52'101}, 2, 1};
  program.arcs[1] = {exact::word{51'102}, exact::word{52'102}, 3, 1};
  set_current(program, 0, 0, 3);
  set_current(program, 1, 1, 4);
  return program;
}

current::causal_program open_boundary() noexcept {
  auto program = base_program(5'003, 2, 1, 1, 1, 4);
  program.sites[0].first_arc = 0; program.sites[0].arc_count = 1;
  program.sites[1].first_arc = 1;
  program.sites[1].outbound_port = exact::word{53'099};
  program.arcs[0] = {exact::word{51'201}, exact::word{52'201}, 1, 1};
  program.morphology[1] = {exact::word{1}, exact::word{7}, {}};
  set_current(program, 0, 0, 5);
  return program;
}

current::causal_program overflow_refusal() noexcept {
  auto program = base_program(5'004, 1, 0, 1, 1, 2);
  program.morphology[0] = {exact::word{2}, exact::word{0}, {}};
  set_current(program, 0, 0, ~std::uint64_t{0});
  return program;
}

}  // namespace

current::current_mount_batch r5_cases() noexcept {
  current::current_mount_batch batch{};
  batch.count = 4;
  batch.programs[0] = serial_rest();
  batch.programs[1] = parallel_rest();
  batch.programs[2] = open_boundary();
  batch.programs[3] = overflow_refusal();
  return batch;
}

}  // namespace holonics::tests

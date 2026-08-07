#pragma once

#include <cstddef>
#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/causal_current_resident.hpp>

namespace holonics::apparatus::r5_device {

__device__ inline void certify_components(current::resident_causal_body& body) noexcept {
  const auto& program = body.program();
  for (std::size_t component = 0; component < program.component_count; ++component) {
    auto& receipt = body.component(component);
    receipt = {};
    for (std::size_t slot = 0; slot < body.current_count(); ++slot) {
      if (body.current(slot).component == component) { ++receipt.local_current; }
    }
    receipt.in_flight = body.pending_live() ? 1U : 0U;
    receipt.certified = receipt.local_current == 0 && receipt.in_flight == 0;
  }
}

__device__ inline void prepare_front(current::resident_causal_body& body,
    std::uint16_t& input_count,
    std::uint16_t& produced,
    std::uint64_t& occurrence_first,
    std::uint16_t frontier) noexcept {
  input_count = body.current_count();
  produced = 0;
  if (!body.begin_front()) {
    body.obstruct(current::current_obstruction::reservation_conflict);
    input_count = 0;
    return;
  }
  body.reset_scratch();
  for (std::size_t left = 0; left < input_count; ++left) {
    for (std::size_t right = left + 1U; right < input_count; ++right) {
      if ((body.current(left).caused_support.value() &
           body.current(right).caused_support.value()) != 0) {
        body.failure() =
            static_cast<std::uint32_t>(current::current_obstruction::reservation_conflict);
      }
    }
  }
  for (std::size_t slot = 0; slot < input_count; ++slot) {
    const auto& site = body.program().sites[body.current(slot).site];
    const std::uint16_t count = site.arc_count != 0 ? site.arc_count :
        static_cast<std::uint16_t>(site.outbound_port.value() != 0 ? 1U : 0U);
    body.output_offset(slot) = produced;
    body.output_count(slot) = count;
    if (count > current::sparse_current_capacity - produced) {
      body.failure() = static_cast<std::uint32_t>(current::current_obstruction::capacity_refused);
      break;
    }
    produced = static_cast<std::uint16_t>(produced + count);
  }
  if (body.delta_count() + input_count > body.program().resource_obligation ||
      body.delta_count() + input_count > current::current_delta_capacity) {
    body.failure() = static_cast<std::uint32_t>(current::current_obstruction::capacity_refused);
  }
  occurrence_first = body.reserve_occurrences(produced);
  auto& receipt = body.front(frontier);
  receipt.predecessor = body.standing().head();
  receipt.event_first = exact::word{body.event_first()};
  receipt.input_count = input_count;
  receipt.output_count = produced;
  receipt.pending_before = input_count;
}

__device__ inline void advance_member(current::resident_causal_body& body,
    std::uint16_t slot,
    std::uint64_t occurrence_first) noexcept {
  const auto value = body.current(slot);
  const auto& site = body.program().sites[value.site];
  auto& pending = body.local_pending(slot);
  const std::uint64_t event = body.event_first() + slot;
  pending = {body.standing().head(), exact::word{event}, value.occurrence,
      value.caused_support, value.lineage, value.site, true};
  const auto transformed = current::apply_morphology(
      value.local_state, body.morphology(value.site), 1);
  std::uint64_t changed_support = site.support.value();
  for (std::size_t offset = 0;
       transformed.obstruction == current::current_obstruction::none &&
       offset < body.output_count(slot); ++offset) {
    const std::size_t output_slot = body.output_offset(slot) + offset;
    auto successor = value;
    auto output_value = transformed;
    successor.occurrence = exact::word{occurrence_first + output_slot};
    successor.phase = static_cast<std::uint16_t>(value.phase + 1U);
    successor.open = site.arc_count == 0;
    if (site.arc_count != 0) {
      const auto& arc = body.program().arcs[site.first_arc + offset];
      const std::uint32_t prior = atomicCAS(body.reservations() + arc.target,
          current::resident_causal_body::unreserved, slot);
      if (prior != current::resident_causal_body::unreserved) {
        atomicCAS(&body.failure(), 0U,
            static_cast<std::uint32_t>(current::current_obstruction::reservation_conflict));
        continue;
      }
      const current::morphology_cell multiplicity{
          exact::word{arc.multiplicity}, exact::word{0}, {}};
      output_value = current::apply_morphology(transformed.value, multiplicity, 1);
      if (output_value.obstruction != current::current_obstruction::none) {
        atomicCAS(&body.failure(), 0U, static_cast<std::uint32_t>(output_value.obstruction));
        continue;
      }
      successor.site = arc.target;
      successor.component = body.program().sites[arc.target].component;
      successor.caused_support = exact::word{value.caused_support.value() |
          body.program().sites[arc.target].support.value()};
      successor.lineage = exact::word{value.lineage.value() + arc.lineage.value() + event};
      successor.multiplicity = arc.multiplicity;
      changed_support |= body.program().sites[arc.target].support.value();
    } else {
      successor.lineage = exact::word{value.lineage.value() + event};
      atomicAdd(&body.open_count(), 1U);
    }
    successor.local_state = output_value.value;
    body.next(output_slot) = successor;
  }
  if (transformed.obstruction != current::current_obstruction::none) {
    atomicCAS(&body.failure(), 0U, static_cast<std::uint32_t>(transformed.obstruction));
  }
  auto& delta = body.delta(body.delta_base() + slot);
  delta = {body.standing().head(), exact::word{event}, exact::word{event},
      value.caused_support, exact::word{changed_support},
      static_cast<std::int64_t>(body.output_count(slot)) - 1,
      transformed.value, transformed.value, exact::word{value.multiplicity},
      exact::word{static_cast<std::uint64_t>(transformed.obstruction)},
      exact::word{body.output_count(slot)}, exact::word{value.lineage.value() + event},
      value.site, body.output_count(slot)};
  pending.active = false;
  atomicOr(&body.touched_support(), static_cast<unsigned long long>(value.caused_support.value()));
  atomicOr(&body.changed_support(), static_cast<unsigned long long>(changed_support));
}

}  // namespace holonics::apparatus::r5_device

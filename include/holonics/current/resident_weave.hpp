#pragma once

#include <cstddef>
#include <cstdint>
#include <type_traits>

#include <holonics/body/continuing_body.hpp>
#include <holonics/current/weave_certificate_law.hpp>

namespace holonics::current {
class resident_weave final {
 public:
  resident_weave() = delete;
  resident_weave(const resident_weave&) = delete;
  resident_weave& operator=(const resident_weave&) = delete;
  resident_weave(resident_weave&&) = delete;
  resident_weave& operator=(resident_weave&&) = delete;

  HOLONICS_CALLABLE explicit resident_weave(const weave_program& program) noexcept
      : program_(program), body_(program.predecessor.value(), program.body_regions),
        standing_(predecessor_snapshot(program)) {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr const weave_program& program() const noexcept {
    return program_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const weave_snapshot& standing() const noexcept {
    return standing_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr weave_snapshot& standing() noexcept {
    return standing_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const weave_delta& delta(
      std::size_t slot) const noexcept { return deltas_[slot]; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const resource_backreaction_receipt& resource()
      const noexcept { return resource_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t committed_layers() const noexcept {
    return committed_layers_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr weave_obstruction validation() const noexcept {
    return validation_;
  }
  HOLONICS_CALLABLE constexpr void set_validation(weave_obstruction state) noexcept {
    validation_ = state;
    standing_.obstruction = state;
  }

  HOLONICS_CALLABLE constexpr void stage(std::size_t slot) noexcept {
    deltas_[slot] = stage_weave_delta(body_.head(), program_.events[slot]);
  }

  [[nodiscard]] HOLONICS_CALLABLE bool commit_layer(
      std::uint64_t logical_resource,
      std::uint64_t current_fold) noexcept {
    if (!body_.can_open() || standing_.head != body_.head() ||
        logical_resource > standing_.logical.capacity.value() ||
        standing_.logical.used.value() > standing_.logical.capacity.value() - logical_resource) {
      standing_.obstruction = weave_obstruction::logical_resource_refused;
      return false;
    }
    auto capability = body_.take_continuation();
    const auto receipt = body_.commit(body_.head(), static_cast<std::uint16_t>(committed_layers_ %
        body::live_region_capacity), current_fold,
        static_cast<body::linear_continuation&&>(capability));
    if (receipt.state != body::body_change_status::committed) {
      standing_.obstruction = weave_obstruction::logical_resource_refused;
      return false;
    }
    standing_.head = receipt.successor;
    standing_.logical.used = exact::word{standing_.logical.used.value() + logical_resource};
    ++committed_layers_;
    return true;
  }

  HOLONICS_CALLABLE void apply_cell(std::size_t slot) noexcept {
    const weave_delta& value = deltas_[slot];
    weave_cell& cell = standing_.cells[value.cell];
    cell.value = exact::word{cell.value.value() + value.value_delta.value()};
    cell.current = value.successor_current;
    cell.lineage = value.lineage;
    standing_.emitted[slot] = value.consequence;
    standing_.logical.reservations[slot] = value.logical_resource;
  }

  HOLONICS_CALLABLE void equalize_interaction() noexcept {
    const auto& left = program_.events[program_.interaction_left];
    const auto& right = program_.events[program_.interaction_right];
    standing_.cells[left.cell].current = exact::word{
        left.successor_current.value() + right.successor_current.value()};
    standing_.cells[left.cell].lineage = exact::word{
        left.lineage.value() + right.lineage.value()};
  }

  HOLONICS_CALLABLE void begin_resource_return() noexcept {
    resource_.returned = program_.returned_resource;
    resource_.policy = program_.resource;
    resource_.predecessor_head = standing_.head;
    resource_.partition_before = standing_.cells[0].placement;
    resource_.aperture_before = standing_.cells[0].aperture;
    resource_.pressure_returned =
        program_.returned_resource.available_bytes.value() < program_.resource.required_bytes.value() ||
        program_.returned_resource.resident_bytes.value() >
            program_.returned_resource.available_bytes.value() ||
        program_.returned_resource.temperature_upper_millikelvin.value() >
            program_.resource.temperature_limit_millikelvin.value();
  }

  [[nodiscard]] HOLONICS_CALLABLE bool commit_resource_return() noexcept {
    if (!resource_.pressure_returned) {
      resource_.successor_head = standing_.head;
      return true;
    }
    if (!commit_layer(0, program_.returned_resource.available_bytes.value())) {
      resource_.obstruction = weave_obstruction::logical_resource_refused;
      return false;
    }
    resource_.successor_head = standing_.head;
    if (!program_.resource.alternative_declared) {
      standing_.obstruction = weave_obstruction::returned_resource_open;
      resource_.obstruction = weave_obstruction::returned_resource_open;
      resource_.partition_after = resource_.partition_before;
      resource_.aperture_after = resource_.aperture_before;
      resource_.remained_open = true;
      return true;
    }
    resource_.partition_after = program_.resource.alternative_partition;
    resource_.aperture_after = program_.resource.alternative_aperture;
    resource_.morphology_changed = true;
    return true;
  }

  HOLONICS_CALLABLE void apply_resource_cell(std::size_t cell_slot) noexcept {
    if (!resource_.morphology_changed || cell_slot >= standing_.cell_count) { return; }
    standing_.cells[cell_slot].placement = resource_.partition_after;
    standing_.cells[cell_slot].aperture = resource_.aperture_after;
  }

 private:
  weave_program program_;
  body::continuing_body body_;
  weave_snapshot standing_{};
  weave_delta deltas_[weave_event_capacity]{};
  resource_backreaction_receipt resource_{};
  std::uint16_t committed_layers_{};
  weave_obstruction validation_{weave_obstruction::none};
};

static_assert(std::is_trivially_destructible_v<resident_weave>);

}  // namespace holonics::current

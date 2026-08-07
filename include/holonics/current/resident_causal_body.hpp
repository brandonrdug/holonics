#pragma once

#include <cstddef>
#include <cstdint>
#include <new>
#include <type_traits>
#include <holonics/body/continuing_body.hpp>
#include <holonics/current/current_law.hpp>
#include <holonics/current/frontier_pending.hpp>
namespace holonics::current {
class resident_causal_body final {
 public:
  resident_causal_body() = delete;
  resident_causal_body(const resident_causal_body&) = delete;
  resident_causal_body& operator=(const resident_causal_body&) = delete;
  resident_causal_body(resident_causal_body&&) = delete;
  resident_causal_body& operator=(resident_causal_body&&) = delete;

  HOLONICS_CALLABLE explicit resident_causal_body(const causal_program& program) noexcept
      : program_(program), standing_(program.predecessor.value(), program.body_regions),
        next_occurrence_(program.next_occurrence.value()), next_event_(program.next_event.value()),
        current_count_(program.initial_current_count), state_(current_status::mounted) {
    for (std::size_t slot = 0; slot < program_site_capacity; ++slot) {
      morphology_[slot] = program.morphology[slot];
      reservations_[slot] = unreserved;
    }
    for (std::size_t slot = 0; slot < program.initial_current_count; ++slot) {
      currents_[0][slot] = program.initial_currents[slot];
    }
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr const causal_program& program() const noexcept {
    return program_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr body::continuing_body& standing() noexcept {
    return standing_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const body::continuing_body& standing() const noexcept {
    return standing_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr current_status state() const noexcept { return state_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr current_obstruction obstruction() const noexcept {
    return obstruction_;
  }
  HOLONICS_CALLABLE constexpr void obstruct(current_obstruction cause) noexcept {
    obstruction_ = cause;
    state_ = current_status::obstructed;
  }
  HOLONICS_CALLABLE constexpr void open_with(current_obstruction cause) noexcept {
    obstruction_ = cause;
    state_ = current_status::open_frontier;
  }
  HOLONICS_CALLABLE constexpr void set_state(current_status state) noexcept { state_ = state; }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t current_count() const noexcept {
    return current_count_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr sparse_current& current(std::size_t slot) noexcept {
    return currents_[active_buffer_][slot];
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const sparse_current& current(
      std::size_t slot) const noexcept {
    return currents_[active_buffer_][slot];
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr sparse_current& next(std::size_t slot) noexcept {
    return currents_[active_buffer_ ^ 1U][slot];
  }
  HOLONICS_CALLABLE constexpr void publish(std::uint16_t count) noexcept {
    active_buffer_ ^= 1U;
    current_count_ = count;
  }

  [[nodiscard]] HOLONICS_CALLABLE bool begin_front() noexcept {
    if (pending_live_ || !standing_.can_open() || current_count_ == 0) { return false; }
    event_first_ = next_event_;
    next_event_ += current_count_;
    ::new (static_cast<void*>(pending_storage_)) frontier_pending{
        standing_.take_continuation(), standing_.head(), exact::word{event_first_}, current_count_};
    pending_live_ = true;
    delta_base_ = delta_count_;
    return true;
  }
  [[nodiscard]] HOLONICS_CALLABLE frontier_pending* pending() noexcept {
    return pending_live_ ? reinterpret_cast<frontier_pending*>(pending_storage_) : nullptr;
  }
  [[nodiscard]] HOLONICS_CALLABLE body::body_change_receipt commit_front(
      exact::word current_fold) noexcept {
    frontier_pending* live = pending();
    if (live == nullptr) { return {}; }
    auto capability = live->release();
    pending_live_ = false;
    return standing_.commit(live->predecessor(), static_cast<std::uint16_t>(front_count_ %
        body::live_region_capacity), current_fold.value(),
        static_cast<body::linear_continuation&&>(capability));
  }
  HOLONICS_CALLABLE void recover_front() noexcept {
    frontier_pending* live = pending();
    if (live == nullptr) { return; }
    auto capability = live->release();
    pending_live_ = false;
    standing_.recover(static_cast<body::linear_continuation&&>(capability));
  }

  HOLONICS_CALLABLE constexpr void reset_scratch() noexcept {
    failure_ = 0;
    produced_count_ = 0;
    open_count_ = 0;
    front_touched_support_ = 0;
    front_changed_support_ = 0;
    for (std::size_t slot = 0; slot < program_site_capacity; ++slot) {
      reservations_[slot] = unreserved;
    }
    for (std::size_t slot = 0; slot < sparse_current_capacity; ++slot) {
      local_pending_[slot] = {};
      output_offsets_[slot] = 0;
      output_counts_[slot] = 0;
    }
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t* reservations() noexcept {
    return reservations_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr local_pending_deed& local_pending(
      std::size_t slot) noexcept { return local_pending_[slot]; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr current_delta& delta(std::size_t slot) noexcept {
    return deltas_[slot];
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr morphology_cell& morphology(
      std::size_t slot) noexcept { return morphology_[slot]; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr front_receipt& front(std::size_t slot) noexcept {
    return fronts_[slot];
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr component_quiescence& component(
      std::size_t slot) noexcept { return components_[slot]; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t& output_offset(
      std::size_t slot) noexcept { return output_offsets_[slot]; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t& output_count(
      std::size_t slot) noexcept { return output_counts_[slot]; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t& failure() noexcept { return failure_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t& produced_count() noexcept {
    return produced_count_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t& open_count() noexcept {
    return open_count_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr unsigned long long& touched_support() noexcept {
    return front_touched_support_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr unsigned long long& changed_support() noexcept {
    return front_changed_support_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t reserve_occurrences(
      std::uint16_t count) noexcept {
    const std::uint64_t first = next_occurrence_;
    next_occurrence_ += count;
    return first;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t event_first() const noexcept {
    return event_first_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t delta_base() const noexcept {
    return delta_base_;
  }
  HOLONICS_CALLABLE constexpr void complete_front(
      std::uint16_t produced,
      std::uint16_t deltas) noexcept {
    produced_count_ = produced;
    delta_count_ = static_cast<std::uint16_t>(delta_count_ + deltas);
    ++front_count_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t front_count() const noexcept {
    return front_count_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t delta_count() const noexcept {
    return delta_count_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool pending_live() const noexcept {
    return pending_live_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const front_receipt* fronts() const noexcept {
    return fronts_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const component_quiescence* components() const noexcept {
    return components_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const morphology_cell* morphology_cells() const noexcept {
    return morphology_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const current_delta* deltas() const noexcept {
    return deltas_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t touched_support_value() const noexcept {
    return all_touched_support_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t front_touched_support() const noexcept {
    return front_touched_support_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t front_changed_support() const noexcept {
    return front_changed_support_;
  }
  HOLONICS_CALLABLE constexpr void retain_front_support() noexcept {
    all_touched_support_ |= front_touched_support_;
  }

  static constexpr std::uint32_t unreserved = ~std::uint32_t{0};

 private:
  causal_program program_;
  body::continuing_body standing_;
  morphology_cell morphology_[program_site_capacity]{};
  sparse_current currents_[2][sparse_current_capacity]{};
  local_pending_deed local_pending_[sparse_current_capacity]{};
  current_delta deltas_[current_delta_capacity]{};
  front_receipt fronts_[program_front_capacity]{};
  component_quiescence components_[program_component_capacity]{};
  std::uint32_t reservations_[program_site_capacity]{};
  std::uint16_t output_offsets_[sparse_current_capacity]{};
  std::uint16_t output_counts_[sparse_current_capacity]{};
  alignas(frontier_pending) unsigned char pending_storage_[sizeof(frontier_pending)]{};
  std::uint64_t next_occurrence_{};
  std::uint64_t next_event_{};
  std::uint64_t event_first_{};
  unsigned long long front_touched_support_{};
  unsigned long long front_changed_support_{};
  std::uint64_t all_touched_support_{};
  std::uint32_t failure_{};
  std::uint16_t current_count_{};
  std::uint16_t produced_count_{};
  std::uint32_t open_count_{};
  std::uint16_t front_count_{};
  std::uint16_t delta_count_{};
  std::uint16_t delta_base_{};
  std::uint8_t active_buffer_{};
  current_status state_{current_status::unmounted};
  current_obstruction obstruction_{current_obstruction::none};
  bool pending_live_{};
};
static_assert(std::is_trivially_destructible_v<resident_causal_body>);

}  // namespace holonics::current

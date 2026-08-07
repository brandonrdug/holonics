#pragma once

#include <cstdint>

#include <holonics/body/continuation.hpp>

namespace holonics::current {

class frontier_pending final {
 public:
  frontier_pending() = delete;
  frontier_pending(const frontier_pending&) = delete;
  frontier_pending& operator=(const frontier_pending&) = delete;
  HOLONICS_CALLABLE frontier_pending(frontier_pending&& other) noexcept
      : capability_(static_cast<body::linear_continuation&&>(other.capability_)),
        predecessor_(other.predecessor_), event_first_(other.event_first_),
        input_count_(other.input_count_), active_(other.active_) {
    other.active_ = false;
  }
  frontier_pending& operator=(frontier_pending&&) = delete;

  HOLONICS_CALLABLE frontier_pending(
      body::linear_continuation&& capability,
      exact::word predecessor,
      exact::word event_first,
      std::uint16_t input_count) noexcept
      : capability_(static_cast<body::linear_continuation&&>(capability)),
        predecessor_(predecessor), event_first_(event_first),
        input_count_(input_count), active_(true) {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr exact::word predecessor() const noexcept {
    return predecessor_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr exact::word event_first() const noexcept {
    return event_first_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t input_count() const noexcept {
    return input_count_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool active() const noexcept { return active_; }
  [[nodiscard]] HOLONICS_CALLABLE body::linear_continuation release() noexcept {
    active_ = false;
    return static_cast<body::linear_continuation&&>(capability_);
  }

 private:
  body::linear_continuation capability_;
  exact::word predecessor_{};
  exact::word event_first_{};
  std::uint16_t input_count_{};
  bool active_{};
};

}  // namespace holonics::current

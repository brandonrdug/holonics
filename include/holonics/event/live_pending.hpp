#pragma once

#include <cstdint>

#include <holonics/body/continuation.hpp>
#include <holonics/event/deed.hpp>
#include <holonics/event/lifecycle_schema.hpp>

namespace holonics::event {

class live_pending final {
 public:
  using holonics_pending_deed = pending_deed_marker;
  using continuation_type = body::linear_continuation;

  live_pending() = delete;
  live_pending(const live_pending&) = delete;
  live_pending& operator=(const live_pending&) = delete;
  HOLONICS_CALLABLE live_pending(live_pending&& other) noexcept
      : capability_(static_cast<body::linear_continuation&&>(other.capability_)),
        outbound_(other.outbound_) {}
  live_pending& operator=(live_pending&&) = delete;

  HOLONICS_CALLABLE live_pending(
      body::linear_continuation&& capability,
      outbound_occurrence outbound) noexcept
      : capability_(static_cast<body::linear_continuation&&>(capability)), outbound_(outbound) {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool resumable() const noexcept {
    return capability_.valid();
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const outbound_occurrence& outbound() const noexcept {
    return outbound_;
  }
  [[nodiscard]] HOLONICS_CALLABLE body::linear_continuation take_continuation() noexcept {
    return static_cast<body::linear_continuation&&>(capability_);
  }

 private:
  body::linear_continuation capability_;
  outbound_occurrence outbound_{};
};

static_assert(pending_deed<live_pending>);

}  // namespace holonics::event

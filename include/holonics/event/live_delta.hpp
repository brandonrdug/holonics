#pragma once

#include <holonics/body/continuation.hpp>
#include <holonics/event/deed.hpp>
#include <holonics/event/lifecycle_schema.hpp>

namespace holonics::event {

class live_delta final {
 public:
  using holonics_delta = delta_marker;
  using continuation_type = body::linear_continuation;

  live_delta() = delete;
  live_delta(const live_delta&) = delete;
  live_delta& operator=(const live_delta&) = delete;
  HOLONICS_CALLABLE live_delta(live_delta&& other) noexcept
      : capability_(static_cast<body::linear_continuation&&>(other.capability_)),
        receipt_(other.receipt_) {}
  live_delta& operator=(live_delta&&) = delete;

  HOLONICS_CALLABLE live_delta(
      body::linear_continuation&& capability,
      complete_delta_receipt receipt) noexcept
      : capability_(static_cast<body::linear_continuation&&>(capability)), receipt_(receipt) {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr const complete_delta_receipt& receipt() const noexcept {
    return receipt_;
  }
  [[nodiscard]] HOLONICS_CALLABLE body::linear_continuation take_continuation() noexcept {
    return static_cast<body::linear_continuation&&>(capability_);
  }

 private:
  body::linear_continuation capability_;
  complete_delta_receipt receipt_{};
};

static_assert(delta<live_delta>);

}  // namespace holonics::event

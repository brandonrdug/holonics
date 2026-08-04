#pragma once

#include <type_traits>

#include <holonics/body/continuation.hpp>
#include <holonics/event/deed.hpp>
#include <holonics/event/checker_return_schema.hpp>

namespace holonics::event {

class checker_pending_deed final {
 public:
  using holonics_pending_deed = pending_deed_marker;
  using continuation_type = body::linear_continuation;

  checker_pending_deed() = delete;
  checker_pending_deed(const checker_pending_deed&) = delete;
  checker_pending_deed& operator=(const checker_pending_deed&) = delete;
  HOLONICS_CALLABLE checker_pending_deed(checker_pending_deed&& other) noexcept
      : capability_(static_cast<body::linear_continuation&&>(other.capability_)),
        outbound_(other.outbound_) {}
  checker_pending_deed& operator=(checker_pending_deed&&) = delete;

  HOLONICS_CALLABLE checker_pending_deed(
      body::linear_continuation&& capability,
      checker_outbound_occurrence outbound) noexcept
      : capability_(static_cast<body::linear_continuation&&>(capability)), outbound_(outbound) {}

  [[nodiscard]] HOLONICS_CALLABLE bool resumable() const noexcept { return capability_.valid(); }
  [[nodiscard]] HOLONICS_CALLABLE const checker_outbound_occurrence& outbound() const noexcept {
    return outbound_;
  }
  [[nodiscard]] HOLONICS_CALLABLE body::linear_continuation take_continuation() noexcept {
    return static_cast<body::linear_continuation&&>(capability_);
  }

 private:
  body::linear_continuation capability_;
  checker_outbound_occurrence outbound_{};
};

static_assert(pending_deed<checker_pending_deed>);
static_assert(std::is_trivially_destructible_v<checker_pending_deed>);

}  // namespace holonics::event

#pragma once

#include <concepts>
#include <type_traits>

#include <holonics/body/ownership.hpp>
#include <holonics/exact/config.hpp>

namespace holonics::event {

struct pending_deed_marker final {};
struct delta_marker final {};

template<class Pending>
concept pending_deed = requires {
  typename Pending::holonics_pending_deed;
  typename Pending::continuation_type;
} && std::same_as<typename Pending::holonics_pending_deed, pending_deed_marker>
  && body::continuation<typename Pending::continuation_type>
  && std::is_move_constructible_v<Pending>
  && (!std::is_copy_constructible_v<Pending>);

template<class Delta>
concept delta = requires {
  typename Delta::holonics_delta;
  typename Delta::continuation_type;
} && std::same_as<typename Delta::holonics_delta, delta_marker>
  && body::continuation<typename Delta::continuation_type>
  && std::is_move_constructible_v<Delta>
  && (!std::is_copy_constructible_v<Delta>);

template<body::continuation Continuation>
class pending final {
 public:
  using holonics_pending_deed = pending_deed_marker;
  using continuation_type = Continuation;

  pending() = delete;
  pending(const pending&) = delete;
  pending& operator=(const pending&) = delete;
  HOLONICS_CALLABLE pending(pending&& other) noexcept
      : capability_(static_cast<Continuation&&>(other.capability_)) {}
  HOLONICS_CALLABLE pending& operator=(pending&& other) noexcept {
    capability_ = static_cast<Continuation&&>(other.capability_);
    return *this;
  }

 private:
  HOLONICS_CALLABLE explicit pending(Continuation&& capability) noexcept
      : capability_(static_cast<Continuation&&>(capability)) {}

  Continuation capability_;
};

template<body::continuation Continuation>
class staged_delta final {
 public:
  using holonics_delta = delta_marker;
  using continuation_type = Continuation;

  staged_delta() = delete;
  staged_delta(const staged_delta&) = delete;
  staged_delta& operator=(const staged_delta&) = delete;
  HOLONICS_CALLABLE staged_delta(staged_delta&& other) noexcept
      : capability_(static_cast<Continuation&&>(other.capability_)) {}
  HOLONICS_CALLABLE staged_delta& operator=(staged_delta&& other) noexcept {
    capability_ = static_cast<Continuation&&>(other.capability_);
    return *this;
  }

 private:
  HOLONICS_CALLABLE explicit staged_delta(Continuation&& capability) noexcept
      : capability_(static_cast<Continuation&&>(capability)) {}

  Continuation capability_;
};

using pending_contract = pending<body::continuation_capability>;
using delta_contract = staged_delta<body::continuation_capability>;

static_assert(pending_deed<pending_contract>);
static_assert(delta<delta_contract>);

}  // namespace holonics::event

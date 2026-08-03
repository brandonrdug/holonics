#pragma once

#include <concepts>
#include <type_traits>

#include <holonics/exact/config.hpp>

namespace holonics::body {

struct continuation_marker final {};

template<class Capability>
concept continuation = requires {
  typename Capability::holonics_continuation;
} && std::same_as<typename Capability::holonics_continuation, continuation_marker>
  && std::is_move_constructible_v<Capability>
  && std::is_move_assignable_v<Capability>
  && (!std::is_copy_constructible_v<Capability>)
  && (!std::is_copy_assignable_v<Capability>);

class continuation_capability final {
 public:
  using holonics_continuation = continuation_marker;

  continuation_capability() = delete;
  continuation_capability(const continuation_capability&) = delete;
  continuation_capability& operator=(const continuation_capability&) = delete;
  HOLONICS_CALLABLE continuation_capability(continuation_capability&&) noexcept {}
  HOLONICS_CALLABLE continuation_capability& operator=(continuation_capability&&) noexcept {
    return *this;
  }

 private:
  struct mint;
  HOLONICS_CALLABLE explicit constexpr continuation_capability(mint*) noexcept {}
};

class body_contract final {
 public:
  body_contract() = delete;
  body_contract(const body_contract&) = delete;
  body_contract& operator=(const body_contract&) = delete;
  HOLONICS_CALLABLE body_contract(body_contract&&) noexcept {}
  HOLONICS_CALLABLE body_contract& operator=(body_contract&&) noexcept { return *this; }
};

class live_morphology_contract final {
 public:
  live_morphology_contract() = delete;
  live_morphology_contract(const live_morphology_contract&) = delete;
  live_morphology_contract& operator=(const live_morphology_contract&) = delete;
  HOLONICS_CALLABLE live_morphology_contract(live_morphology_contract&&) noexcept {}
  HOLONICS_CALLABLE live_morphology_contract& operator=(
      live_morphology_contract&&) noexcept {
    return *this;
  }
};

class rest_ownership final {
 public:
  rest_ownership() = delete;
  rest_ownership(const rest_ownership&) = delete;
  rest_ownership& operator=(const rest_ownership&) = delete;
  HOLONICS_CALLABLE rest_ownership(rest_ownership&&) noexcept {}
  HOLONICS_CALLABLE rest_ownership& operator=(rest_ownership&&) noexcept { return *this; }
};

static_assert(continuation<continuation_capability>);

}  // namespace holonics::body

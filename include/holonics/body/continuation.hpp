#pragma once

#include <cstdint>

#include <holonics/body/ownership.hpp>
#include <holonics/exact/word.hpp>

namespace holonics::body {

class continuing_body;

class linear_continuation final {
 public:
  using holonics_continuation = continuation_marker;

  linear_continuation() = delete;
  linear_continuation(const linear_continuation&) = delete;
  linear_continuation& operator=(const linear_continuation&) = delete;
  HOLONICS_CALLABLE linear_continuation(linear_continuation&& other) noexcept
      : serial_(other.serial_), valid_(other.valid_) {
    other.valid_ = false;
  }
  HOLONICS_CALLABLE linear_continuation& operator=(linear_continuation&& other) noexcept {
    if (this != &other) {
      serial_ = other.serial_;
      valid_ = other.valid_;
      other.valid_ = false;
    }
    return *this;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool valid() const noexcept { return valid_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr exact::word serial() const noexcept { return serial_; }

 private:
  friend class continuing_body;

  HOLONICS_CALLABLE explicit constexpr linear_continuation(exact::word serial) noexcept
      : serial_(serial), valid_(true) {}
  HOLONICS_CALLABLE constexpr void consume() noexcept { valid_ = false; }

  exact::word serial_{};
  bool valid_{};
};

static_assert(continuation<linear_continuation>);

}  // namespace holonics::body

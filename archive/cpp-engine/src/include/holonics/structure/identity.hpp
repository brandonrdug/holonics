#pragma once

#include <holonics/exact/config.hpp>
#include <holonics/exact/word.hpp>

namespace holonics::structure {

template<class Owner>
class identity_mint;

template<class Owner>
class identity_reservation;

template<class Owner>
class identity final {
 public:
  using owner_type = Owner;

  identity() = delete;
  HOLONICS_CALLABLE constexpr identity(const identity& other) noexcept : serial_(other.serial_) {}
  HOLONICS_CALLABLE constexpr identity& operator=(const identity& other) noexcept {
    serial_ = other.serial_;
    return *this;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr exact::word serial() const noexcept {
    return serial_;
  }

  friend HOLONICS_CALLABLE constexpr bool operator==(identity left, identity right) noexcept {
    return left.serial_ == right.serial_;
  }

 private:
  friend Owner;
  friend class identity_mint<Owner>;
  friend class identity_reservation<Owner>;

  HOLONICS_CALLABLE explicit constexpr identity(exact::word serial) noexcept : serial_(serial) {}

  exact::word serial_;
};

}  // namespace holonics::structure

#pragma once

#include <concepts>
#include <cstdint>
#include <type_traits>

#include <holonics/exact/config.hpp>

namespace holonics::exact {

struct exact_carrier_marker final {};

template<class Carrier>
concept exact_carrier = requires {
  typename Carrier::holonics_exact_carrier;
} && std::same_as<typename Carrier::holonics_exact_carrier, exact_carrier_marker>
  && (!std::is_floating_point_v<Carrier>);

class word final {
 public:
  using holonics_exact_carrier = exact_carrier_marker;

  HOLONICS_CALLABLE constexpr word() noexcept : value_{} {}
  HOLONICS_CALLABLE explicit constexpr word(std::uint64_t value) noexcept : value_(value) {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t value() const noexcept {
    return value_;
  }

  friend HOLONICS_CALLABLE constexpr bool operator==(word left, word right) noexcept {
    return left.value_ == right.value_;
  }

 private:
  std::uint64_t value_{};
};

static_assert(exact_carrier<word>);
static_assert(!exact_carrier<std::uint64_t>);

}  // namespace holonics::exact

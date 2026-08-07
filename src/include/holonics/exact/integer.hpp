#pragma once

#include <concepts>
#include <cstddef>
#include <cstdint>

#include <holonics/exact/config.hpp>
#include <holonics/exact/status.hpp>
#include <holonics/exact/word.hpp>

namespace holonics::exact {

enum class limb_order : std::uint8_t { least_significant_first, most_significant_first };

template<std::size_t Capacity>
class unsigned_integer final {
  static_assert(Capacity > 0);
  static_assert(Capacity <= 65'535);

 public:
  using holonics_exact_carrier = exact_carrier_marker;
  static constexpr std::size_t capacity = Capacity;
  static constexpr limb_order internal_order = limb_order::least_significant_first;

  HOLONICS_CALLABLE constexpr unsigned_integer() noexcept : limbs_{}, used_{} {}

  [[nodiscard]] HOLONICS_CALLABLE static constexpr unsigned_integer from_word(
      std::uint64_t value) noexcept {
    unsigned_integer result;
    result.limbs_[0] = value;
    result.used_ = value == 0 ? 0 : 1;
    return result;
  }

  [[nodiscard]] HOLONICS_CALLABLE static constexpr checked_result<unsigned_integer> from_limbs(
      const std::uint64_t* limbs,
      std::size_t count,
      limb_order order) noexcept {
    checked_result<unsigned_integer> result{};
    result.receipt.admitted_limbs = static_cast<std::uint16_t>(Capacity);
    result.receipt.required_limbs =
        static_cast<std::uint16_t>(count > 65'535 ? 65'535 : count);
    if (count > Capacity) {
      result.receipt.state = status::capacity_refused;
      return result;
    }
    for (std::size_t index = 0; index < count; ++index) {
      const std::size_t source =
          order == limb_order::least_significant_first ? index : count - index - 1;
      result.value.limbs_[index] = limbs[source];
    }
    result.value.used_ = count;
    result.value.normalize();
    return result;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::size_t used() const noexcept { return used_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool is_zero() const noexcept { return used_ == 0; }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t limb(
      std::size_t index) const noexcept {
    return index < used_ && index < Capacity ? limbs_[index] : 0;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool bit(std::size_t index) const noexcept {
    const std::size_t limb_index = index / 64;
    const std::size_t bit_index = index % 64;
    return limb_index < used_ && ((limbs_[limb_index] >> bit_index) & 1U) != 0;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::size_t bit_length() const noexcept {
    if (used_ == 0) {
      return 0;
    }
    std::uint64_t high = limbs_[used_ - 1];
    std::size_t bits = (used_ - 1) * 64;
    while (high != 0) {
      ++bits;
      high >>= 1U;
    }
    return bits;
  }

  HOLONICS_CALLABLE constexpr void clear() noexcept {
    for (std::size_t index = 0; index < Capacity; ++index) {
      limbs_[index] = 0;
    }
    used_ = 0;
  }

  HOLONICS_CALLABLE constexpr void set_limb(std::size_t index, std::uint64_t value) noexcept {
    if (index >= Capacity) {
      return;
    }
    limbs_[index] = value;
    if (value != 0 && used_ <= index) {
      used_ = index + 1;
    }
    if (value == 0 && used_ == index + 1) {
      normalize();
    }
  }

  HOLONICS_CALLABLE constexpr void normalize() noexcept {
    while (used_ != 0 && limbs_[used_ - 1] == 0) {
      --used_;
    }
    for (std::size_t index = used_; index < Capacity; ++index) {
      limbs_[index] = 0;
    }
  }

  friend HOLONICS_CALLABLE constexpr bool operator==(
      const unsigned_integer& left,
      const unsigned_integer& right) noexcept {
    if (left.used_ != right.used_) {
      return false;
    }
    for (std::size_t index = 0; index < left.used_; ++index) {
      if (left.limbs_[index] != right.limbs_[index]) {
        return false;
      }
    }
    return true;
  }

 private:
  std::uint64_t limbs_[Capacity]{};
  std::size_t used_{};
};

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr int compare(
    const unsigned_integer<Capacity>& left,
    const unsigned_integer<Capacity>& right) noexcept {
  if (left.used() != right.used()) {
    return left.used() < right.used() ? -1 : 1;
  }
  for (std::size_t index = left.used(); index != 0; --index) {
    const std::uint64_t a = left.limb(index - 1);
    const std::uint64_t b = right.limb(index - 1);
    if (a != b) {
      return a < b ? -1 : 1;
    }
  }
  return 0;
}

using unsigned_128 = unsigned_integer<2>;
using unsigned_192 = unsigned_integer<3>;
using unsigned_256 = unsigned_integer<4>;
using unsigned_384 = unsigned_integer<6>;

template<std::size_t MaximumLimbs>
using dynamic_unsigned = unsigned_integer<MaximumLimbs>;

static_assert(exact_carrier<unsigned_128>);
static_assert(exact_carrier<unsigned_192>);
static_assert(exact_carrier<unsigned_256>);
static_assert(exact_carrier<unsigned_384>);
static_assert(exact_carrier<dynamic_unsigned<5>>);

}  // namespace holonics::exact

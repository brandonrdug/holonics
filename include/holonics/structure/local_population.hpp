#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/sparse_ordinal_atlas.hpp>

namespace holonics::structure {

/// Receiver-local sorted population. `capacity()` is **physical testimony,
/// never a semantic population and never an admission gate** — a refusal at
/// capacity is a resource obstruction that the caller must resolve by changing
/// partition, factorization, or aperture, not by widening a number.
template<class Value, std::size_t Capacity>
class local_set final {
  static_assert(Capacity > 0);

 public:
  HOLONICS_CALLABLE constexpr local_set() noexcept : values_{} {}

  [[nodiscard]] HOLONICS_CALLABLE static constexpr std::size_t capacity() noexcept {
    return Capacity;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t used() const noexcept {
    return used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const Value& at(
      std::uint32_t slot) const noexcept {
    return values_[slot];
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool contains(
      const Value& value) const noexcept {
    return locate(value) < used_ && values_[locate(value)] == value;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool try_insert(const Value& value) noexcept {
    const std::uint32_t at_slot = locate(value);
    if (at_slot < used_ && values_[at_slot] == value) {
      return true;
    }
    if (used_ >= Capacity) {
      return false;
    }
    for (std::uint32_t slot = used_; slot > at_slot; --slot) {
      values_[slot] = values_[slot - 1U];
    }
    values_[at_slot] = value;
    used_ = used_ + 1U;
    return true;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool disjoint_from(
      const local_set& other) const noexcept {
    for (std::uint32_t slot = 0; slot < used_; ++slot) {
      if (other.contains(values_[slot])) {
        return false;
      }
    }
    return true;
  }

  /// Inclusion, which is the relation a minimal-witness comparison needs.
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool includes(
      const local_set& other) const noexcept {
    for (std::uint32_t slot = 0; slot < other.used_; ++slot) {
      if (!contains(other.values_[slot])) {
        return false;
      }
    }
    return true;
  }

 private:
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t locate(
      const Value& value) const noexcept {
    std::uint32_t low = 0;
    std::uint32_t high = used_;
    while (low < high) {
      const std::uint32_t middle = low + ((high - low) >> 1U);
      if (values_[middle] < value) {
        low = middle + 1U;
      } else {
        high = middle;
      }
    }
    return low;
  }

  Value values_[Capacity]{};
  std::uint32_t used_{};
};

/// Ordered population retaining arrival order. Distinct from `local_set`: a
/// sequence keeps duplicates, because repeated testimony is recurrence and not
/// redundancy.
template<class Value, std::size_t Capacity>
class local_sequence final {
  static_assert(Capacity > 0);

 public:
  HOLONICS_CALLABLE constexpr local_sequence() noexcept : values_{} {}

  [[nodiscard]] HOLONICS_CALLABLE static constexpr std::size_t capacity() noexcept {
    return Capacity;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t used() const noexcept {
    return used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const Value& at(
      std::uint32_t slot) const noexcept {
    return values_[slot];
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr Value* at_mut(
      std::uint32_t slot) noexcept {
    return slot < used_ ? &values_[slot] : nullptr;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool try_append(const Value& value) noexcept {
    if (used_ >= Capacity) {
      return false;
    }
    values_[used_] = value;
    used_ = used_ + 1U;
    return true;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool try_append_recover(
      const Value& value,
      Value& recovered) noexcept {
    if (!try_append(value)) {
      recovered = value;
      return false;
    }
    return true;
  }

 private:
  Value values_[Capacity]{};
  std::uint32_t used_{};
};

}  // namespace holonics::structure

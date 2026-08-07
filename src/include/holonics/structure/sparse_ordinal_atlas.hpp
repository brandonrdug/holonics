#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::structure {

inline constexpr std::uint32_t no_ordinal = 0xFFFF'FFFFU;

enum class ordinal_status : std::uint8_t {
  admitted,
  capacity_refused,
  ordinal_refused,
  absent
};

struct ordinal_receipt final {
  ordinal_status state{ordinal_status::capacity_refused};
  std::uint32_t ordinal{no_ordinal};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool accepted() const noexcept {
    return state == ordinal_status::admitted;
  }
};

struct ordinal_atlas_memory final {
  std::uint32_t extent{};
  std::uint32_t occupied{};
  std::uint32_t pages_present{};
  std::uint64_t value_octets{};
};

/// A sparse ordinal population over fixed physical pages with a per-page
/// occupancy mask.
///
/// **Ordinals are never reused.** Departure leaves a tombstone and the minting
/// horizon only ever advances, so an ordinal that named an occurrence never
/// later names a different one — remount included. Slots are 32-bit, not 16-bit:
/// a research corpus does not fit under 65,535.
///
/// Every admission has a recovering form that returns the value on refusal, so
/// no capacity refusal can destroy a causal body.
template<class Value, std::size_t PageCapacity, std::size_t PageCount>
class sparse_ordinal_atlas final {
  static_assert(PageCapacity > 0 && PageCapacity <= 64);
  static_assert(PageCount > 0);

 public:
  static constexpr std::size_t capacity = PageCapacity * PageCount;

  HOLONICS_CALLABLE constexpr sparse_ordinal_atlas() noexcept : values_{}, occupancy_{} {}
  sparse_ordinal_atlas(const sparse_ordinal_atlas&) = delete;
  sparse_ordinal_atlas& operator=(const sparse_ordinal_atlas&) = delete;
  sparse_ordinal_atlas(sparse_ordinal_atlas&&) = delete;
  sparse_ordinal_atlas& operator=(sparse_ordinal_atlas&&) = delete;

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t extent() const noexcept {
    return horizon_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t occupied() const noexcept {
    return occupied_;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool present(
      std::uint32_t ordinal) const noexcept {
    if (ordinal >= capacity) {
      return false;
    }
    const std::size_t page = ordinal / PageCapacity;
    const std::uint64_t mask = std::uint64_t{1} << (ordinal % PageCapacity);
    return (occupancy_[page] & mask) != 0U;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr const Value* get(
      std::uint32_t ordinal) const noexcept {
    return present(ordinal) ? &values_[ordinal] : nullptr;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr Value* get_mut(
      std::uint32_t ordinal) noexcept {
    return present(ordinal) ? &values_[ordinal] : nullptr;
  }

  /// Mint the next ordinal. The horizon advances even when a page is sparse, so
  /// a tombstoned slot is never handed out again.
  [[nodiscard]] HOLONICS_CALLABLE constexpr ordinal_receipt try_push(
      const Value& value) noexcept {
    ordinal_receipt receipt{};
    if (horizon_ >= capacity) {
      receipt.state = ordinal_status::capacity_refused;
      return receipt;
    }
    const std::uint32_t ordinal = horizon_;
    values_[ordinal] = value;
    mark(ordinal);
    horizon_ = horizon_ + 1U;
    occupied_ = occupied_ + 1U;
    receipt.state = ordinal_status::admitted;
    receipt.ordinal = ordinal;
    return receipt;
  }

  /// Recovering admission: on refusal the value is written back to `recovered`
  /// and the body is unchanged.
  [[nodiscard]] HOLONICS_CALLABLE constexpr ordinal_receipt try_push_recover(
      const Value& value,
      Value& recovered) noexcept {
    const ordinal_receipt receipt = try_push(value);
    if (!receipt.accepted()) {
      recovered = value;
    }
    return receipt;
  }

  /// Found at a declared ordinal at or beyond the horizon. Refuses to overwrite
  /// an occupied slot and refuses to reach behind the horizon.
  [[nodiscard]] HOLONICS_CALLABLE constexpr ordinal_receipt try_found(
      std::uint32_t ordinal,
      const Value& value) noexcept {
    ordinal_receipt receipt{};
    if (ordinal >= capacity) {
      receipt.state = ordinal_status::capacity_refused;
      return receipt;
    }
    if (ordinal < horizon_ || present(ordinal)) {
      receipt.state = ordinal_status::ordinal_refused;
      return receipt;
    }
    values_[ordinal] = value;
    mark(ordinal);
    horizon_ = ordinal + 1U;
    occupied_ = occupied_ + 1U;
    receipt.state = ordinal_status::admitted;
    receipt.ordinal = ordinal;
    return receipt;
  }

  /// Departure. The slot is tombstoned; the horizon does not retreat.
  [[nodiscard]] HOLONICS_CALLABLE constexpr ordinal_receipt depart(
      std::uint32_t ordinal,
      Value& returned) noexcept {
    ordinal_receipt receipt{};
    if (!present(ordinal)) {
      receipt.state = ordinal_status::absent;
      return receipt;
    }
    returned = values_[ordinal];
    values_[ordinal] = Value{};
    const std::size_t page = ordinal / PageCapacity;
    occupancy_[page] &= ~(std::uint64_t{1} << (ordinal % PageCapacity));
    occupied_ = occupied_ - 1U;
    receipt.state = ordinal_status::admitted;
    receipt.ordinal = ordinal;
    return receipt;
  }

  /// Restore a minting horizon across a remount. Refuses to retreat, so a rest
  /// image can never make the atlas hand out a used ordinal again.
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool try_restore_horizon(
      std::uint32_t horizon) noexcept {
    if (horizon < horizon_ || horizon > capacity) {
      return false;
    }
    horizon_ = horizon;
    return true;
  }

  /// Physical testimony. This is resource reporting, never a semantic population
  /// and never an admission gate.
  [[nodiscard]] HOLONICS_CALLABLE constexpr ordinal_atlas_memory memory() const noexcept {
    ordinal_atlas_memory report{};
    report.extent = horizon_;
    report.occupied = occupied_;
    for (std::size_t page = 0; page < PageCount; ++page) {
      report.pages_present += occupancy_[page] != 0U ? 1U : 0U;
    }
    report.value_octets = static_cast<std::uint64_t>(capacity) * sizeof(Value);
    return report;
  }

 private:
  HOLONICS_CALLABLE constexpr void mark(std::uint32_t ordinal) noexcept {
    const std::size_t page = ordinal / PageCapacity;
    occupancy_[page] |= std::uint64_t{1} << (ordinal % PageCapacity);
  }

  Value values_[capacity]{};
  std::uint64_t occupancy_[PageCount]{};
  std::uint32_t horizon_{};
  std::uint32_t occupied_{};
};

}  // namespace holonics::structure

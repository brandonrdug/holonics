#pragma once

#include <cstdint>

#include <holonics/exact/config.hpp>

namespace holonics::structure {

/// A non-owning view over resident storage.
///
/// **This is the carrier that lets an ecology stop being a kernel frame value.**
/// A ported ecology that declares its arrays inline is bounded by the device
/// stack — Phase 5 already returned that evidence, where a three-kilobyte
/// standing surface overflowed the default one-kilobyte per-thread stack and the
/// repair was a physical reservation. No reservation admits a corpus.
///
/// A span carries a pointer and an extent and nothing else. It **allocates
/// nothing, frees nothing, and owns nothing**: the apparatus owns the storage
/// and the interior receives the view. Passing an ecology to a kernel therefore
/// costs pointers, not a copy of the body.
///
/// Every access is guarded. `holds` is the admission and `at` is only defined
/// where `holds` returned true, so an absent or short span refuses rather than
/// reading past its extent.
template<class Value>
struct resident_span final {
  Value* first{};
  std::uint32_t extent{};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool present() const noexcept {
    return first != nullptr && extent != 0;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool holds(std::uint32_t slot) const noexcept {
    return first != nullptr && slot < extent;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr Value& at(std::uint32_t slot) const noexcept {
    return first[slot];
  }
  /// The span from `start`, clipped to this extent. A start beyond the extent
  /// returns an absent span rather than a negative or wrapped length.
  [[nodiscard]] HOLONICS_CALLABLE constexpr resident_span from(
      std::uint32_t start) const noexcept {
    return start < extent ? resident_span{first + start, extent - start}
                          : resident_span{};
  }
};

/// Are these two spans over the same storage? Physical testimony about the
/// arena; it establishes no causality and no order.
template<class Value>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_storage(
    resident_span<Value> left,
    resident_span<Value> right) noexcept {
  return left.first == right.first && left.extent == right.extent;
}

}  // namespace holonics::structure

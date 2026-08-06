#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/body/standing_rest.hpp>

namespace holonics::body {

/// What a resident chart did, and did not have to do.
///
/// **RIDE is cheap because the terrain already paid**, and until this the
/// asymmetry was a predicate over an enum: `rebase_exposed` and `cross`
/// performed identical work and RIDE never read the standing at all. Here a ride
/// is a measured absence of work.
struct residency_receipt final {
  std::uint64_t full_mounts{};
  std::uint64_t rides{};
  std::uint64_t appended_organs{};
  std::uint64_t mounted_octets{};
  std::uint64_t avoided_octets{};
  bool base_address_unchanged{true};
};

/// A resident chart over one standing.
///
/// The revision is a **hint**. When it matches, the exact logical comparison
/// still runs and always wins; when it does not, the chart re-mounts. A standing
/// that grew by appending carries only the appended organs, and the earlier
/// image keeps its addresses — which is what lets a founded tensor stay founded.
template<std::size_t Capacity>
class standing_residency final {
 public:
  HOLONICS_CALLABLE constexpr standing_residency() noexcept : image_{} {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr const residency_receipt& receipt()
      const noexcept { return receipt_; }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t mounted() const noexcept {
    return mounted_extent_;
  }

  /// Bring the chart up to the standing, doing as little as the standing allows.
  template<class Standing>
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool synchronize(
      const Standing& body) noexcept {
    const std::uint32_t extent = standing_rest_law::rest_extent(body);
    if (extent > Capacity) {
      return false;
    }
    // The shape short-circuit: unchanged revision and identical octets means the
    // terrain already paid, and the chart does nothing at all.
    if (mounted_ && revision_ == body.revision() && mounted_extent_ == extent &&
        identical(body, extent)) {
      receipt_.rides = receipt_.rides + 1U;
      receipt_.avoided_octets = receipt_.avoided_octets + extent;
      return true;
    }
    const std::uint32_t held = mounted_extent_;
    const bool appended = mounted_ && extent > held && prefix_holds(body, held);
    const auto written = standing_rest_law::encode(body, image_, Capacity);
    if (written == 0) {
      return false;
    }
    if (appended) {
      receipt_.appended_organs = receipt_.appended_organs + 1U;
      receipt_.mounted_octets = receipt_.mounted_octets + (extent - held);
      receipt_.avoided_octets = receipt_.avoided_octets + held;
    } else {
      receipt_.full_mounts = receipt_.full_mounts + 1U;
      receipt_.mounted_octets = receipt_.mounted_octets + extent;
    }
    mounted_ = true;
    mounted_extent_ = extent;
    revision_ = body.revision();
    return true;
  }

 private:
  template<class Standing>
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool identical(
      const Standing& body, std::uint32_t extent) const noexcept {
    unsigned char probe[Capacity]{};
    return standing_rest_law::encode(body, probe, Capacity) == extent &&
        same_octets(probe, extent);
  }
  template<class Standing>
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool prefix_holds(
      const Standing& body, std::uint32_t held) const noexcept {
    unsigned char probe[Capacity]{};
    if (standing_rest_law::encode(body, probe, Capacity) == 0) {
      return false;
    }
    // Only the payload prefix must agree; the header carries the new counts.
    for (std::uint32_t slot = standing_rest_header; slot < held; ++slot) {
      if (probe[slot] != image_[slot]) {
        return false;
      }
    }
    return true;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool same_octets(
      const unsigned char* probe, std::uint32_t extent) const noexcept {
    for (std::uint32_t slot = 0; slot < extent; ++slot) {
      if (probe[slot] != image_[slot]) {
        return false;
      }
    }
    return true;
  }

  unsigned char image_[Capacity]{};
  residency_receipt receipt_{};
  std::uint32_t mounted_extent_{};
  std::uint64_t revision_{};
  bool mounted_{};
};

}  // namespace holonics::body

#pragma once

#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::apparatus {

enum class sealed_geometry_status : std::uint8_t {
  returned,
  invalid_aperture,
  open_refused,
  read_refused,
  capacity_refused
};

struct sealed_geometry_comparison final {
  sealed_geometry_status state{sealed_geometry_status::invalid_aperture};
  exact::word bytes{};
  exact::word observer_reads{};
  exact::word engine_reads{};
  std::uint64_t content_fold{};
  bool opened_after_kernel_return{};
  bool affine_neighbor_present{};
  bool fractional_neighbor_present{};
  bool body_resumed_after_open{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == sealed_geometry_status::returned;
  }
};

[[nodiscard]] sealed_geometry_comparison compare_sealed_geometry_reference(
    const char* path, bool kernel_returned) noexcept;

}  // namespace holonics::apparatus

#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/codec/mathematical_source_environment.hpp>

namespace holonics::apparatus {

enum class mathematical_source_status : std::uint8_t {
  exact,
  invalid_aperture,
  open_refused,
  read_refused,
  capacity_refused,
  recognition_refused,
  relocation_refused
};

struct mathematical_source_receipt final {
  mathematical_source_status state{mathematical_source_status::invalid_aperture};
  std::uint16_t source_count{};
  std::uint16_t chunk_aperture{};
  std::uint16_t chunk_count{};
  std::uint64_t byte_count{};
  std::uint64_t material_testimony{};
  std::uint64_t path_testimony{};
  std::uint64_t recognized_declarations{};
};

struct mathematical_source_result final {
  codec::mathematical_source_environment environment{};
  mathematical_source_receipt receipt{};

  mathematical_source_result() noexcept = default;
  mathematical_source_result(const mathematical_source_result&) = delete;
  mathematical_source_result& operator=(const mathematical_source_result&) = delete;
  mathematical_source_result(mathematical_source_result&&) noexcept = default;
  mathematical_source_result& operator=(mathematical_source_result&&) noexcept = default;
};

[[nodiscard]] mathematical_source_result mount_mathematical_sources(
    const char* const* paths, std::size_t count, std::uint16_t chunk_aperture) noexcept;
[[nodiscard]] mathematical_source_result mount_relocated_mathematical_sources(
    const char* const* paths, std::size_t count, std::uint16_t chunk_aperture,
    const char* destination) noexcept;
[[nodiscard]] bool same_mathematical_material(
    const codec::mathematical_source_environment& left,
    const codec::mathematical_source_environment& right) noexcept;

}  // namespace holonics::apparatus

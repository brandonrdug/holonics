#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/codec/source_environment.hpp>

namespace holonics::apparatus {

enum class source_store_status : std::uint8_t {
  exact,
  invalid_aperture,
  open_refused,
  read_refused,
  capacity_refused,
  relocation_refused
};

struct source_store_receipt final {
  source_store_status state{source_store_status::invalid_aperture};
  std::uint16_t source_count{};
  std::uint16_t byte_count{};
  std::uint64_t path_testimony_fold{};
  std::uint64_t byte_testimony_fold{};
};

struct source_store_result final {
  codec::source_environment environment{};
  source_store_receipt receipt{};

  source_store_result() noexcept = default;
  source_store_result(const source_store_result&) = delete;
  source_store_result& operator=(const source_store_result&) = delete;
  source_store_result(source_store_result&&) noexcept = default;
  source_store_result& operator=(source_store_result&&) noexcept = default;
};

[[nodiscard]] source_store_result mount_source_store(
    const char* const* paths,
    std::size_t count) noexcept;

[[nodiscard]] source_store_result mount_relocated_source_store(
    const char* const* paths,
    std::size_t count,
    const char* destination) noexcept;

[[nodiscard]] bool same_source_material(
    const codec::source_environment& left,
    const codec::source_environment& right) noexcept;

}  // namespace holonics::apparatus

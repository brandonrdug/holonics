#pragma once

#include <cstdint>

#include <holonics/codec/mounted_codec_environment.hpp>

namespace holonics::apparatus {

enum class codec_store_status : std::uint8_t {
  exact,
  allocation_refused,
  open_refused,
  schema_refused,
  relocation_refused
};

struct codec_store_receipt final {
  codec_store_status state{codec_store_status::allocation_refused};
  exact::word material_testimony{};
  exact::word path_testimony{};
  exact::word inherited_provenance{};
};

struct codec_store_result final {
  codec::mounted_codec_environment environment{};
  codec_store_receipt receipt{};
};

[[nodiscard]] codec_store_result mount_codec_store(const char* path) noexcept;
[[nodiscard]] codec_store_result mount_relocated_codec_store(
    const char* path, const char* destination) noexcept;
[[nodiscard]] bool same_codec_material(
    const codec::mounted_codec_environment& left,
    const codec::mounted_codec_environment& right) noexcept;

}  // namespace holonics::apparatus

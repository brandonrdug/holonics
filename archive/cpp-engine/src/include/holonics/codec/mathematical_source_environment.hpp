#pragma once

#include <cstddef>
#include <cstdint>
#include <new>
#include <utility>

namespace holonics::codec {

inline constexpr std::size_t mathematical_source_capacity = 2;
inline constexpr std::size_t mathematical_source_byte_capacity = 4096;

struct mathematical_source_buffer final {
  std::uint16_t byte_count{};
  std::uint64_t material_testimony{};
  unsigned char bytes[mathematical_source_byte_capacity]{};
};

struct encoded_mathematical_sources final {
  std::uint16_t source_count{};
  mathematical_source_buffer sources[mathematical_source_capacity]{};
};

class mathematical_source_environment final {
 public:
  mathematical_source_environment() noexcept
      : encoded_(new (std::nothrow) encoded_mathematical_sources{}) {}
  ~mathematical_source_environment() noexcept { delete encoded_; }

  mathematical_source_environment(const mathematical_source_environment&) = delete;
  mathematical_source_environment& operator=(const mathematical_source_environment&) = delete;
  mathematical_source_environment(mathematical_source_environment&& other) noexcept
      : encoded_(std::exchange(other.encoded_, nullptr)) {}
  mathematical_source_environment& operator=(mathematical_source_environment&& other) noexcept {
    if (this != &other) {
      delete encoded_;
      encoded_ = std::exchange(other.encoded_, nullptr);
    }
    return *this;
  }

  [[nodiscard]] bool admitted() const noexcept { return encoded_ != nullptr; }
  [[nodiscard]] encoded_mathematical_sources& encoded() noexcept { return *encoded_; }
  [[nodiscard]] const encoded_mathematical_sources& encoded() const noexcept { return *encoded_; }

  void detach() noexcept {
    if (encoded_ == nullptr) { return; }
    for (std::size_t source = 0; source < mathematical_source_capacity; ++source) {
      for (std::size_t slot = 0; slot < mathematical_source_byte_capacity; ++slot) {
        encoded_->sources[source].bytes[slot] = 0;
      }
    }
    delete encoded_;
    encoded_ = nullptr;
  }

 private:
  encoded_mathematical_sources* encoded_{};
};

}  // namespace holonics::codec

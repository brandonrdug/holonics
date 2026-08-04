#pragma once

#include <cstddef>
#include <new>
#include <utility>

#include <holonics/codec/environment_contract.hpp>
#include <holonics/codec/source_schema.hpp>

namespace holonics::codec {

class source_environment final {
 public:
  source_environment() noexcept
      : encoded_(new (std::nothrow) encoded_source_environment{}) {}
  ~source_environment() noexcept { delete encoded_; }

  source_environment(const source_environment&) = delete;
  source_environment& operator=(const source_environment&) = delete;
  source_environment(source_environment&& other) noexcept
      : encoded_(std::exchange(other.encoded_, nullptr)) {}
  source_environment& operator=(source_environment&& other) noexcept {
    if (this != &other) {
      delete encoded_;
      encoded_ = std::exchange(other.encoded_, nullptr);
    }
    return *this;
  }

  [[nodiscard]] bool admitted() const noexcept { return encoded_ != nullptr; }
  [[nodiscard]] encoded_source_environment& encoded() noexcept { return *encoded_; }
  [[nodiscard]] const encoded_source_environment& encoded() const noexcept { return *encoded_; }

  void detach() noexcept {
    if (encoded_ == nullptr) {
      return;
    }
    for (std::size_t slot = 0; slot < source_byte_capacity; ++slot) {
      encoded_->bytes[slot] = 0;
    }
    delete encoded_;
    encoded_ = nullptr;
  }

 private:
  encoded_source_environment* encoded_{};
};

static_assert(face_contract<source_mount_port, source_mount_port>::source_port_type::direction ==
    structure::port_direction::inbound);

}  // namespace holonics::codec

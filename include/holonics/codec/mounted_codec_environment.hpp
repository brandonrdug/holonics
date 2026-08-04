#pragma once

#include <new>
#include <utility>

#include <holonics/codec/reflection_schema.hpp>

namespace holonics::codec {

class mounted_codec_environment final {
 public:
  mounted_codec_environment() noexcept
      : value_(new (std::nothrow) codec_environment{}) {}
  ~mounted_codec_environment() noexcept { delete value_; }

  mounted_codec_environment(const mounted_codec_environment&) = delete;
  mounted_codec_environment& operator=(const mounted_codec_environment&) = delete;
  mounted_codec_environment(mounted_codec_environment&& other) noexcept
      : value_(std::exchange(other.value_, nullptr)) {}
  mounted_codec_environment& operator=(mounted_codec_environment&& other) noexcept {
    if (this != &other) {
      delete value_;
      value_ = std::exchange(other.value_, nullptr);
    }
    return *this;
  }

  [[nodiscard]] bool admitted() const noexcept { return value_ != nullptr; }
  [[nodiscard]] codec_environment& value() noexcept { return *value_; }
  [[nodiscard]] const codec_environment& value() const noexcept { return *value_; }

  void detach() noexcept {
    delete value_;
    value_ = nullptr;
  }

 private:
  codec_environment* value_{};
};

}  // namespace holonics::codec

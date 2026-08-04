#pragma once

#include <cstddef>

#include <holonics/exact/config.hpp>

namespace holonics::structure {

template<class Value>
class bounded_view final {
 public:
  HOLONICS_CALLABLE constexpr bounded_view(
      const Value* values,
      std::size_t count,
      std::size_t capacity) noexcept
      : values_(values), count_(count), capacity_(capacity) {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::size_t size() const noexcept {
    return count_ <= capacity_ ? count_ : capacity_;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool complete() const noexcept {
    return count_ <= capacity_ && (count_ == 0 || values_ != nullptr);
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr const Value* at(
      std::size_t index) const noexcept {
    return complete() && index < count_ ? values_ + index : nullptr;
  }

 private:
  const Value* values_{};
  std::size_t count_{};
  std::size_t capacity_{};
};

}  // namespace holonics::structure

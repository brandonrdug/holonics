#pragma once

#include <cstddef>
#include <new>

#include <holonics/exact/config.hpp>

namespace holonics::structure {

template<class Value, std::size_t Capacity>
class parallel_arena final {
 public:
  HOLONICS_CALLABLE constexpr parallel_arena() noexcept : size_{} {}
  parallel_arena(const parallel_arena&) = delete;
  parallel_arena& operator=(const parallel_arena&) = delete;
  parallel_arena(parallel_arena&&) = delete;
  parallel_arena& operator=(parallel_arena&&) = delete;

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool reserve(std::size_t count) noexcept {
    if (count > Capacity || size_ != 0) {
      return false;
    }
    size_ = count;
    return true;
  }

  template<class... Arguments>
  HOLONICS_CALLABLE Value& construct(std::size_t slot, Arguments... arguments) noexcept {
    return *::new (static_cast<void*>(storage_ + slot * sizeof(Value)))
        Value(arguments...);
  }

  [[nodiscard]] HOLONICS_CALLABLE Value& at(std::size_t slot) noexcept {
    return *reinterpret_cast<Value*>(storage_ + slot * sizeof(Value));
  }

  [[nodiscard]] HOLONICS_CALLABLE const Value& at(std::size_t slot) const noexcept {
    return *reinterpret_cast<const Value*>(storage_ + slot * sizeof(Value));
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::size_t size() const noexcept { return size_; }
  [[nodiscard]] static constexpr std::size_t capacity() noexcept { return Capacity; }

 private:
  alignas(Value) unsigned char storage_[sizeof(Value) * Capacity];
  std::size_t size_{};
};

}  // namespace holonics::structure

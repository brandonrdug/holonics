#pragma once

#include <cstddef>
#include <cstdint>
#include <new>
#include <type_traits>
#include <utility>

#include <holonics/exact/config.hpp>

namespace holonics::structure {

enum class arena_status : std::uint8_t { reserved, capacity_refused };

struct arena_reservation final {
  arena_status state{arena_status::capacity_refused};
  std::uint16_t offset{};
  std::uint16_t count{};
  std::uint16_t used_before{};
  std::uint16_t used_after{};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool accepted() const noexcept {
    return state == arena_status::reserved;
  }
};

template<class Value, std::size_t Capacity>
class arena final {
  static_assert(Capacity > 0 && Capacity <= 65'535);
  static_assert(std::is_trivially_destructible_v<Value>);

 public:
  HOLONICS_CALLABLE constexpr arena() noexcept : storage_{}, used_{} {}
  arena(const arena&) = delete;
  arena& operator=(const arena&) = delete;
  arena(arena&&) = delete;
  arena& operator=(arena&&) = delete;

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::size_t used() const noexcept { return used_; }
  [[nodiscard]] HOLONICS_CALLABLE static constexpr std::size_t capacity() noexcept {
    return Capacity;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool can_reserve(std::size_t count) const noexcept {
    return count <= Capacity - used_;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr arena_reservation reserve(
      std::size_t count) noexcept {
    arena_reservation result{};
    result.used_before = static_cast<std::uint16_t>(used_);
    result.count = static_cast<std::uint16_t>(count > 65'535 ? 65'535 : count);
    if (!can_reserve(count)) {
      result.used_after = result.used_before;
      return result;
    }
    result.state = arena_status::reserved;
    result.offset = static_cast<std::uint16_t>(used_);
    used_ += count;
    result.used_after = static_cast<std::uint16_t>(used_);
    return result;
  }

  template<class... Arguments>
  HOLONICS_CALLABLE Value* emplace(std::size_t index, Arguments&&... arguments) noexcept {
    if (index >= used_) {
      return nullptr;
    }
    void* location = static_cast<void*>(storage_ + index * sizeof(Value));
    return ::new (location) Value(static_cast<Arguments&&>(arguments)...);
  }

  [[nodiscard]] HOLONICS_CALLABLE Value* at(std::size_t index) noexcept {
    return index < used_
        ? reinterpret_cast<Value*>(storage_ + index * sizeof(Value))
        : nullptr;
  }

  [[nodiscard]] HOLONICS_CALLABLE const Value* at(std::size_t index) const noexcept {
    return index < used_
        ? reinterpret_cast<const Value*>(storage_ + index * sizeof(Value))
        : nullptr;
  }

 private:
  alignas(Value) unsigned char storage_[sizeof(Value) * Capacity];
  std::size_t used_{};
};

}  // namespace holonics::structure

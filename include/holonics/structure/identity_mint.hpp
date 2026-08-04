#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/identity.hpp>

namespace holonics::structure {

template<class Owner>
class identity_reservation final {
 public:
  HOLONICS_CALLABLE constexpr identity_reservation() noexcept : first_{}, count_{} {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::size_t size() const noexcept {
    return count_;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr identity<Owner> at(
      std::size_t offset) const noexcept {
    return identity<Owner>{exact::word{first_ + static_cast<std::uint64_t>(offset)}};
  }

 private:
  friend class identity_mint<Owner>;

  HOLONICS_CALLABLE constexpr identity_reservation(
      std::uint64_t first,
      std::size_t count) noexcept
      : first_(first), count_(count) {}

  std::uint64_t first_{};
  std::size_t count_{};
};

template<class Owner>
class identity_mint final {
 public:
  identity_mint() = delete;
  HOLONICS_CALLABLE explicit constexpr identity_mint(std::uint64_t first_serial) noexcept
      : next_(first_serial) {}

  identity_mint(const identity_mint&) = delete;
  identity_mint& operator=(const identity_mint&) = delete;

  HOLONICS_CALLABLE constexpr identity_mint(identity_mint&& other) noexcept
      : next_(other.next_), exhausted_(other.exhausted_) {
    other.exhausted_ = true;
  }

  HOLONICS_CALLABLE constexpr identity_mint& operator=(identity_mint&& other) noexcept {
    if (this != &other) {
      next_ = other.next_;
      exhausted_ = other.exhausted_;
      other.exhausted_ = true;
    }
    return *this;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool can_mint(std::size_t count) const noexcept {
    if (exhausted_) {
      return count == 0;
    }
    const std::uint64_t remaining = ~std::uint64_t{0} - next_;
    return count == 0 || static_cast<std::uint64_t>(count - 1) <= remaining;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr identity<Owner> mint() noexcept {
    const identity<Owner> result{exact::word{next_}};
    if (next_ == ~std::uint64_t{0}) {
      exhausted_ = true;
    } else {
      ++next_;
    }
    return result;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr identity_reservation<Owner> reserve(
      std::size_t count) noexcept {
    if (!can_mint(count)) {
      return {};
    }
    const std::uint64_t first = next_;
    if (count != 0) {
      const std::uint64_t advance = static_cast<std::uint64_t>(count - 1);
      next_ += advance;
      if (next_ == ~std::uint64_t{0}) {
        exhausted_ = true;
      } else {
        ++next_;
      }
    }
    return identity_reservation<Owner>{first, count};
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr exact::word next_serial() const noexcept {
    return exact::word{next_};
  }

 private:
  std::uint64_t next_{};
  bool exhausted_{};
};

}  // namespace holonics::structure

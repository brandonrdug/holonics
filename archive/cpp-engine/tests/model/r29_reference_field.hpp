#pragma once

#include <cstdint>

namespace holonics::tests::r29_reference_detail {

struct field final {
  std::uint16_t p{}; std::uint8_t degree{}; std::uint32_t q{};
  std::uint16_t modulus[5]{};
};

struct element final { std::uint16_t coefficient[4]{}; };

[[nodiscard]] field discover(std::uint16_t prime, std::uint8_t degree) noexcept;
[[nodiscard]] element decode(std::uint32_t value, const field& source) noexcept;
[[nodiscard]] std::uint32_t encode(const element& value, const field& source) noexcept;
[[nodiscard]] bool equal(const element& left, const element& right, const field& source) noexcept;
[[nodiscard]] element add(element left, element right, const field& source) noexcept;
[[nodiscard]] element negate(element value, const field& source) noexcept;
[[nodiscard]] element multiply(element left, element right, const field& source) noexcept;
[[nodiscard]] element power(element value, std::uint32_t exponent, const field& source) noexcept;
[[nodiscard]] element divide(element left, element right, const field& source) noexcept;
[[nodiscard]] std::int8_t character(element value, const field& source) noexcept;

}  // namespace holonics::tests::r29_reference_detail

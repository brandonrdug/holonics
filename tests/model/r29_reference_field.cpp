#include "r29_reference_field.hpp"

namespace holonics::tests::r29_reference_detail {
namespace {

[[nodiscard]] std::uint16_t mod(std::int64_t value, std::uint16_t p) noexcept {
  const auto residue = value % p;
  return static_cast<std::uint16_t>(residue < 0 ? residue + p : residue);
}
[[nodiscard]] std::uint32_t ipow(std::uint32_t base, std::uint8_t exponent) noexcept {
  std::uint32_t value = 1; while (exponent-- != 0) { value *= base; } return value;
}
[[nodiscard]] bool divides(const std::uint16_t* f, std::uint8_t n,
    const std::uint16_t* g, std::uint8_t d, std::uint16_t p) noexcept {
  std::uint16_t r[5]{}; for (std::uint8_t i = 0; i <= n; ++i) { r[i] = f[i]; }
  for (std::int8_t top = static_cast<std::int8_t>(n); top >= static_cast<std::int8_t>(d); --top) {
    const auto a = r[static_cast<std::uint8_t>(top)]; const auto shift =
        static_cast<std::uint8_t>(top) - d;
    for (std::uint8_t i = 0; i <= d; ++i) { r[i + shift] = mod(r[i + shift] - a * g[i], p); }
  }
  for (std::uint8_t i = 0; i < d; ++i) { if (r[i] != 0) { return false; } }
  return true;
}
[[nodiscard]] bool irreducible(const std::uint16_t* f, std::uint8_t n,
    std::uint16_t p) noexcept {
  for (std::uint8_t d = 1; d <= n / 2U; ++d) {
    for (std::uint32_t code = 0; code < ipow(p,d); ++code) {
      std::uint32_t value = code; std::uint16_t g[5]{};
      for (std::uint8_t i = 0; i < d; ++i) {
        g[i] = static_cast<std::uint16_t>(value % p); value /= p;
      }
      g[d] = 1; if (divides(f,n,g,d,p)) { return false; }
    }
  }
  return true;
}

}  // namespace

field discover(std::uint16_t prime, std::uint8_t degree) noexcept {
  field result{prime,degree,ipow(prime,degree),{}};
  if (degree == 1) { result.modulus[1] = 1; return result; }
  for (std::uint32_t code = 1; code < result.q; ++code) {
    std::uint32_t value = code; std::uint16_t candidate[5]{};
    for (std::uint8_t slot = 0; slot < degree; ++slot) {
      candidate[slot] = static_cast<std::uint16_t>(value % prime); value /= prime;
    }
    candidate[degree] = 1;
    if (irreducible(candidate,degree,prime)) {
      for (std::uint8_t slot = 0; slot <= degree; ++slot) { result.modulus[slot] = candidate[slot]; }
      return result;
    }
  }
  return {};
}

element decode(std::uint32_t value, const field& source) noexcept {
  element result{};
  for (std::uint8_t slot = 0; slot < source.degree; ++slot) {
    result.coefficient[slot] = static_cast<std::uint16_t>(value % source.p); value /= source.p;
  }
  return result;
}
std::uint32_t encode(const element& value, const field& source) noexcept {
  std::uint32_t result = 0; std::uint32_t place = 1;
  for (std::uint8_t slot = 0; slot < source.degree; ++slot) {
    result += value.coefficient[slot] * place; place *= source.p;
  }
  return result;
}
bool equal(const element& left, const element& right, const field& source) noexcept {
  for (std::uint8_t slot = 0; slot < source.degree; ++slot) {
    if (left.coefficient[slot] != right.coefficient[slot]) { return false; }
  }
  return true;
}
element add(element left, element right, const field& source) noexcept {
  element result{}; for (std::uint8_t i = 0; i < source.degree; ++i) {
    result.coefficient[i] = mod(left.coefficient[i] + right.coefficient[i], source.p);
  } return result;
}
element negate(element value, const field& source) noexcept {
  for (std::uint8_t i = 0; i < source.degree; ++i) {
    value.coefficient[i] = mod(-static_cast<std::int64_t>(value.coefficient[i]), source.p);
  } return value;
}
element multiply(element left, element right, const field& source) noexcept {
  std::int64_t product[7]{};
  for (std::uint8_t i = 0; i < source.degree; ++i) for (std::uint8_t j = 0; j < source.degree; ++j) {
    product[i+j] += left.coefficient[i] * right.coefficient[j];
  }
  for (std::int8_t top = static_cast<std::int8_t>(2U*source.degree-2U);
       top >= static_cast<std::int8_t>(source.degree); --top) {
    const auto a = mod(product[static_cast<std::uint8_t>(top)],source.p);
    for (std::uint8_t j = 0; j < source.degree; ++j) {
      product[j + static_cast<std::uint8_t>(top) - source.degree] -= a * source.modulus[j];
    }
  }
  element result{}; for (std::uint8_t i = 0; i < source.degree; ++i) {
    result.coefficient[i] = mod(product[i],source.p);
  } return result;
}
element power(element value, std::uint32_t exponent, const field& source) noexcept {
  auto result = decode(1,source); while (exponent != 0) {
    if ((exponent & 1U) != 0) { result = multiply(result,value,source); }
    exponent >>= 1U; if (exponent != 0) { value = multiply(value,value,source); }
  } return result;
}
element divide(element left, element right, const field& source) noexcept {
  return multiply(left,power(right,source.q-2U,source),source);
}
std::int8_t character(element value, const field& source) noexcept {
  if (encode(value,source) == 0) { return 0; }
  return equal(power(value,(source.q-1U)/2U,source),decode(1,source),source) ? 1 : -1;
}

}  // namespace holonics::tests::r29_reference_detail

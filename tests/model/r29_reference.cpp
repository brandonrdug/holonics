#include "r29_reference.hpp"

namespace holonics::tests {
namespace {
using namespace r29_reference_detail;

struct point final { element x{}; element y{}; bool infinite{}; };

[[nodiscard]] element rhs(element x, std::uint16_t c, const field& f) noexcept {
  auto scalar = element{}; scalar.coefficient[0] = c;
  return add(multiply(multiply(x,x,f),x,f),multiply(scalar,x,f),f);
}
[[nodiscard]] bool on_curve(const point& value, std::uint16_t c, const field& f) noexcept {
  return value.infinite || equal(multiply(value.y,value.y,f),rhs(value.x,c,f),f);
}
[[nodiscard]] bool same(const point& left, const point& right, const field& f) noexcept {
  if (left.infinite || right.infinite) { return left.infinite == right.infinite; }
  return equal(left.x,right.x,f) && equal(left.y,right.y,f);
}
[[nodiscard]] point negative(point value, const field& f) noexcept {
  if (!value.infinite) { value.y = negate(value.y,f); } return value;
}
[[nodiscard]] point sum(point left, point right, std::uint16_t c, const field& f) noexcept {
  if (left.infinite) { return right; } if (right.infinite) { return left; }
  if (equal(left.x,right.x,f) && equal(add(left.y,right.y,f),element{},f)) { return {{},{},true}; }
  element slope{};
  if (equal(left.x,right.x,f)) {
    if (encode(left.y,f) == 0) { return {{},{},true}; }
    auto three = decode(3,f); auto two = decode(2,f); auto coefficient = decode(c,f);
    slope = divide(add(multiply(three,multiply(left.x,left.x,f),f),coefficient,f),
        multiply(two,left.y,f),f);
  } else {
    slope = divide(add(right.y,negate(left.y,f),f),add(right.x,negate(left.x,f),f),f);
  }
  const auto x = add(add(multiply(slope,slope,f),negate(left.x,f),f),negate(right.x,f),f);
  const auto y = add(multiply(slope,add(left.x,negate(x,f),f),f),negate(left.y,f),f);
  return {x,y,false};
}
[[nodiscard]] point scalar(std::int8_t multiple, point value, std::uint16_t c,
    const field& f) noexcept {
  std::int16_t count = multiple;
  if (count < 0) { count = -count; value = negative(value,f); }
  point result{{},{},true}; while (count != 0) {
    if ((count & 1) != 0) { result = sum(result,value,c,f); }
    count >>= 1; if (count != 0) { value = sum(value,value,c,f); }
  } return result;
}
[[nodiscard]] point frobenius(point value, const field& f) noexcept {
  if (!value.infinite) { value.x = power(value.x,f.p,f); value.y = power(value.y,f.p,f); }
  return value;
}
[[nodiscard]] point cm(point value, std::uint16_t i, const field& f) noexcept {
  if (!value.infinite) {
    value.x = negate(value.x,f); value.y = multiply(decode(i,f),value.y,f);
  } return value;
}
[[nodiscard]] point gaussian(point value, std::int8_t a, std::int8_t b,
    std::uint16_t c, std::uint16_t i, const field& f) noexcept {
  return sum(scalar(a,value,c,f),scalar(b,cm(value,i,f),c,f),c,f);
}
[[nodiscard]] std::uint16_t imaginary_unit(std::uint16_t p) noexcept {
  for (std::uint16_t i = 1; i < p; ++i) { if ((i*i+1U)%p == 0) { return i; } } return 0;
}

[[nodiscard]] r29_reference_curve derive(std::uint16_t p, std::uint16_t c,
    const field (&fields)[4]) noexcept {
  r29_reference_curve out{}; out.prime = p; out.coefficient = c;
  for (std::uint8_t degree = 0; degree < 4; ++degree) {
    out.counts[degree] = 1;
    for (std::uint32_t x = 0; x < fields[degree].q; ++x) {
      out.counts[degree] += static_cast<std::uint32_t>(
          1 + character(rhs(decode(x,fields[degree]),c,fields[degree]),fields[degree]));
    }
  }
  const auto& quadratic = fields[1]; const auto i = imaginary_unit(p); std::uint8_t matches = 0;
  for (std::int8_t a = -4; a <= 4; ++a) for (std::int8_t b = -4; b <= 4; ++b) {
    if (a*a+b*b != p) { continue; } bool exact = true; std::uint32_t tested = 1;
    for (std::uint32_t x = 0; x < quadratic.q && exact; ++x) {
      for (std::uint32_t y = 0; y < quadratic.q; ++y) {
        point value{decode(x,quadratic),decode(y,quadratic),false};
        if (!on_curve(value,c,quadratic)) { continue; } ++tested;
        if (!same(frobenius(value,quadratic),gaussian(value,a,b,c,i,quadratic),quadratic)) {
          exact = false; break;
        }
      }
    }
    if (exact) { out.real = a; out.imaginary = b; out.quadratic_points = tested; ++matches; }
  }
  out.exact = matches == 1 && out.quadratic_points == out.counts[1]; return out;
}

}  // namespace

r29_reference_result r29_reference() noexcept {
  r29_reference_result out{}; const std::uint16_t primes[2]{5,13};
  for (std::uint8_t p = 0; p < 2; ++p) for (std::uint8_t d = 0; d < 4; ++d) {
    out.fields[p][d] = discover(primes[p],d+1U);
  }
  const std::uint16_t sources[7][2]{{5,1},{5,4},{13,1},{13,4},{13,2},{13,3},{13,7}};
  out.exact = true;
  for (std::uint8_t slot = 0; slot < 7; ++slot) {
    out.curves[slot] = derive(sources[slot][0],sources[slot][1],
        out.fields[sources[slot][0] == 5 ? 0 : 1]);
    out.exact = out.exact && out.curves[slot].exact;
  }
  return out;
}

}  // namespace holonics::tests

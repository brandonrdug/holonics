#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/integer_polynomial.hpp>

namespace holonics::exact {

/// An exact enclosure is a SET, never a value. It names the closed dyadic
/// interval `[lower, upper]` that provably contains one root of a declared
/// integer source. The enclosed quantity is never read, assigned, or rounded
/// into an owned carrier; only the endpoints are owned exactly.
struct enclosure final {
  dyadic lower{};
  dyadic upper{};
};

enum class enclosure_state : std::uint8_t {
  admitted,
  aperture_refused,
  bracket_absent,
  order_refused
};

struct enclosure_step final {
  enclosure value{};
  enclosure_state state{enclosure_state::admitted};
  std::uint8_t reached_exponent{};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool accepted() const noexcept {
    return state == enclosure_state::admitted;
  }
};

namespace enclosure_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool ordered(enclosure current) noexcept {
  const auto order = dyadic_law::compare(current.lower, current.upper);
  return order.accepted() && order.value <= 0;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool strictly_positive(
    enclosure current) noexcept {
  return dyadic_law::sign(current.lower) > 0;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool strictly_negative(
    enclosure current) noexcept {
  return dyadic_law::sign(current.upper) < 0;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool straddles_zero(
    enclosure current) noexcept {
  return dyadic_law::sign(current.lower) <= 0 && dyadic_law::sign(current.upper) >= 0;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t reached_exponent(
    enclosure current) noexcept {
  return current.lower.exponent > current.upper.exponent ? current.lower.exponent
                                                         : current.upper.exponent;
}

/// True when both endpoint magnitudes are strictly below `numerator /
/// denominator`. This is the containment test a separation certificate needs.
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<bool> inside_magnitude(
    enclosure current,
    std::int64_t numerator,
    std::int64_t denominator) noexcept {
  checked_result<bool> result{};
  const auto low = dyadic_law::compare_magnitude(current.lower, numerator, denominator);
  if (!low.accepted()) {
    result.receipt = low.receipt;
    return result;
  }
  const auto high = dyadic_law::compare_magnitude(current.upper, numerator, denominator);
  if (!high.accepted()) {
    result.receipt = high.receipt;
    return result;
  }
  result.value = low.value < 0 && high.value < 0;
  return result;
}

/// Does the declared source change sign across the enclosure? A bisection that
/// begins without this receipt is asserting a root it has not witnessed.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr enclosure_step bracket(
    const integer_polynomial<Capacity>& source,
    enclosure current) noexcept {
  enclosure_step step{};
  step.value = current;
  step.reached_exponent = reached_exponent(current);
  if (!ordered(current)) {
    step.state = enclosure_state::order_refused;
    return step;
  }
  const auto low = integer_polynomial_law::sign_at(source, current.lower);
  const auto high = integer_polynomial_law::sign_at(source, current.upper);
  if (!low.accepted() || !high.accepted()) {
    step.state = enclosure_state::aperture_refused;
    return step;
  }
  if (low.value != 0 && high.value != 0 && low.value == high.value) {
    step.state = enclosure_state::bracket_absent;
  }
  return step;
}

/// One exact bisection. The midpoint is the arithmetic midpoint; when the source
/// vanishes there the enclosure collapses to that exact point. Otherwise the
/// sub-interval retaining the sign change is returned. Nothing is approximated
/// and no step is taken outside the declared aperture.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr enclosure_step refine(
    const integer_polynomial<Capacity>& source,
    enclosure current) noexcept {
  enclosure_step step = bracket(source, current);
  if (!step.accepted()) {
    return step;
  }
  const auto low = integer_polynomial_law::sign_at(source, current.lower);
  if (low.value == 0) {
    step.value = enclosure{current.lower, current.lower};
    return step;
  }
  const auto high = integer_polynomial_law::sign_at(source, current.upper);
  if (high.value == 0) {
    step.value = enclosure{current.upper, current.upper};
    return step;
  }
  const auto middle = dyadic_law::midpoint(current.lower, current.upper);
  if (!middle.accepted()) {
    step.state = enclosure_state::aperture_refused;
    step.reached_exponent = static_cast<std::uint8_t>(middle.receipt.required_limbs);
    return step;
  }
  const auto centre = integer_polynomial_law::sign_at(source, middle.value);
  if (!centre.accepted()) {
    step.state = enclosure_state::aperture_refused;
    return step;
  }
  if (centre.value == 0) {
    step.value = enclosure{middle.value, middle.value};
  } else if (low.value != centre.value) {
    step.value = enclosure{current.lower, middle.value};
  } else {
    step.value = enclosure{middle.value, current.upper};
  }
  step.reached_exponent = reached_exponent(step.value);
  return step;
}

/// Bounded refinement. Stops early on an exact collapse and returns the last
/// admitted enclosure together with the state that ended the passage, so an
/// aperture refusal remains inspectable rather than silent.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr enclosure_step refine_times(
    const integer_polynomial<Capacity>& source,
    enclosure start,
    std::uint16_t count) noexcept {
  enclosure_step step{};
  step.value = start;
  step.reached_exponent = reached_exponent(start);
  for (std::uint16_t pass = 0; pass < count; ++pass) {
    const enclosure_step next = refine(source, step.value);
    if (!next.accepted()) {
      step.state = next.state;
      return step;
    }
    step = next;
    const auto collapsed = dyadic_law::compare(step.value.lower, step.value.upper);
    if (collapsed.accepted() && collapsed.value == 0) {
      return step;
    }
  }
  return step;
}

}  // namespace enclosure_law
}  // namespace holonics::exact

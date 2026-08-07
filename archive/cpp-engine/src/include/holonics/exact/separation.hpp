#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/integer_polynomial.hpp>

namespace holonics::exact {

/// A separation certificate is the exact statement:
///
///   every root of the declared integer source is either zero -- and only when
///   `admits_zero` -- or has magnitude at least `numerator / denominator`.
///
/// It is derived from the source's own integer coefficients. It is not a
/// tolerance, not an error estimate, and not a bound on an approximation. A
/// commitment made without one is refused rather than guessed.
struct separation_certificate final {
  std::int64_t numerator{};
  std::int64_t denominator{1};
  bool admits_zero{};
  bool derived{};
  std::uint8_t deflated_degree{};
};

namespace separation_law {

/// The reciprocal Cauchy bound. For a source with nonzero constant coefficient
/// `b_0` and remaining height `M`, every root satisfies
/// `|root| >= |b_0| / (|b_0| + M)`, because the reversed source bounds `1/root`
/// above by `1 + M / |b_0|`.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr separation_certificate derive(
    const integer_polynomial<Capacity>& source) noexcept {
  separation_certificate certificate{};
  const std::size_t shift = integer_polynomial_law::zero_multiplicity(source);
  if (source.used == 0 || shift >= source.used) {
    return certificate;
  }
  certificate.admits_zero = shift > 0;
  const integer_polynomial<Capacity> deflated =
      integer_polynomial_law::deflate_zero(source);
  const std::int64_t constant =
      dyadic_law::magnitude(deflated.coefficient[0]);
  if (constant == 0) {
    return certificate;
  }
  std::int64_t remaining = 0;
  for (std::size_t index = 1; index < deflated.used; ++index) {
    const std::int64_t candidate = dyadic_law::magnitude(deflated.coefficient[index]);
    if (candidate > remaining) {
      remaining = candidate;
    }
  }
  if (remaining > polynomial_product_ceiling - constant) {
    return certificate;
  }
  certificate.numerator = constant;
  certificate.denominator = constant + remaining;
  certificate.derived = true;
  certificate.deflated_degree = static_cast<std::uint8_t>(deflated.used - 1);
  return certificate;
}

/// Independent revalidation of a supplied certificate against its declared
/// source. A certificate is inspected here, never trusted because it arrived.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool certifies(
    const integer_polynomial<Capacity>& source,
    separation_certificate certificate) noexcept {
  const separation_certificate rederived = derive(source);
  return rederived.derived == certificate.derived &&
      rederived.admits_zero == certificate.admits_zero &&
      rederived.numerator == certificate.numerator &&
      rederived.denominator == certificate.denominator &&
      rederived.deflated_degree == certificate.deflated_degree;
}

/// A direct witness of the bound at one dyadic: when the source does not vanish
/// at a point whose magnitude is below the separation, that point is consistent
/// with the certificate. Used to expose the certificate's content rather than
/// only its arithmetic.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<bool> excludes_root_at(
    const integer_polynomial<Capacity>& source,
    separation_certificate certificate,
    dyadic point) noexcept {
  checked_result<bool> result{};
  if (!certificate.derived) {
    result.receipt.state = status::capacity_refused;
    return result;
  }
  const auto within = dyadic_law::compare_magnitude(
      point, certificate.numerator, certificate.denominator);
  if (!within.accepted()) {
    result.receipt = within.receipt;
    return result;
  }
  if (within.value >= 0) {
    result.value = false;
    return result;
  }
  const bool zero_point = dyadic_law::sign(point) == 0;
  result.value = !(zero_point && certificate.admits_zero);
  return result;
}

}  // namespace separation_law
}  // namespace holonics::exact

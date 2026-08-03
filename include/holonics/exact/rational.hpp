#pragma once

#include <cstddef>

#include <holonics/exact/signed_magnitude.hpp>

namespace holonics::exact {

template<std::size_t Capacity>
class rational final {
 public:
  using holonics_exact_carrier = exact_carrier_marker;

  HOLONICS_CALLABLE constexpr rational() noexcept
      : denominator_(unsigned_integer<Capacity>::from_word(1)) {}

  [[nodiscard]] HOLONICS_CALLABLE static constexpr checked_result<rational> normalized(
      signed_magnitude<Capacity> numerator,
      unsigned_integer<Capacity> denominator) noexcept {
    checked_result<rational> result{};
    result.receipt.admitted_limbs = static_cast<std::uint16_t>(Capacity);
    if (denominator.is_zero()) {
      result.receipt.state = status::zero_denominator;
      return result;
    }
    if (numerator.magnitude().is_zero()) {
      result.value = rational{};
      return result;
    }
    const auto divisor = greatest_common_divisor(numerator.magnitude(), denominator);
    if (!divisor.accepted()) {
      result.receipt = divisor.receipt;
      return result;
    }
    const auto reduced_numerator = divide(numerator.magnitude(), divisor.value);
    const auto reduced_denominator = divide(denominator, divisor.value);
    result.value.numerator_ = signed_magnitude<Capacity>{
        numerator.negative(), reduced_numerator.quotient};
    result.value.denominator_ = reduced_denominator.quotient;
    const std::size_t required = result.value.numerator_.magnitude().used() >
            result.value.denominator_.used()
        ? result.value.numerator_.magnitude().used()
        : result.value.denominator_.used();
    result.receipt.required_limbs = static_cast<std::uint16_t>(required);
    return result;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr const signed_magnitude<Capacity>& numerator() const noexcept {
    return numerator_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const unsigned_integer<Capacity>& denominator() const noexcept {
    return denominator_;
  }

  friend HOLONICS_CALLABLE constexpr bool operator==(
      const rational& left,
      const rational& right) noexcept {
    return left.numerator_ == right.numerator_ && left.denominator_ == right.denominator_;
  }

 private:
  signed_magnitude<Capacity> numerator_{};
  unsigned_integer<Capacity> denominator_{};
};

static_assert(exact_carrier<rational<6>>);

}  // namespace holonics::exact

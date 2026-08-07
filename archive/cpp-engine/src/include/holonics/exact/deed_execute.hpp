#pragma once

#include <cstddef>

#include <holonics/exact/deed.hpp>

namespace holonics::exact {

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr deed_output execute_deed_at_capacity(
    const deed_input& input) noexcept {
  deed_output output{};
  output.case_identity = input.case_identity;
  output.kind = input.kind;
  output.admitted_limbs = static_cast<std::uint16_t>(Capacity);
  const auto left = decode<Capacity>(input.left);
  const auto right = decode<Capacity>(input.right);
  const auto modulus = decode<Capacity>(input.modulus);
  if (!left.accepted()) {
    attach_receipt(output, left.receipt);
    return output;
  }
  if (!right.accepted()) {
    attach_receipt(output, right.receipt);
    return output;
  }
  if (!modulus.accepted()) {
    attach_receipt(output, modulus.receipt);
    return output;
  }

  switch (input.kind) {
    case deed_kind::add: {
      const auto result = add(left.value, right.value);
      attach_receipt(output, result.receipt);
      output.primary = encode(result.value);
      break;
    }
    case deed_kind::subtract: {
      const auto result = subtract(left.value, right.value);
      attach_receipt(output, result.receipt);
      output.primary = encode(result.value);
      break;
    }
    case deed_kind::multiply: {
      const auto result = multiply(left.value, right.value);
      attach_receipt(output, result.receipt);
      output.primary = encode(result.value);
      break;
    }
    case deed_kind::divide: {
      const auto result = divide(left.value, right.value);
      attach_receipt(output, result.receipt);
      output.primary = encode(result.quotient);
      output.secondary = encode(result.remainder);
      break;
    }
    case deed_kind::greatest_common_divisor: {
      const auto result = greatest_common_divisor(left.value, right.value);
      attach_receipt(output, result.receipt);
      output.primary = encode(result.value);
      break;
    }
    case deed_kind::shift_left: {
      const auto result = shift_left(left.value, input.shift);
      attach_receipt(output, result.receipt);
      output.primary = encode(result.value);
      break;
    }
    case deed_kind::signed_add: {
      const signed_magnitude<Capacity> signed_left{input.left_negative, left.value};
      const signed_magnitude<Capacity> signed_right{input.right_negative, right.value};
      const auto result = add(signed_left, signed_right);
      attach_receipt(output, result.receipt);
      output.primary = encode(result.value.magnitude());
      output.negative = result.value.negative();
      break;
    }
    case deed_kind::normalize_rational: {
      const auto result = rational<Capacity>::normalized(
          signed_magnitude<Capacity>{input.left_negative, left.value}, right.value);
      attach_receipt(output, result.receipt);
      if (result.accepted()) {
        output.primary = encode(result.value.numerator().magnitude());
        output.secondary = encode(result.value.denominator());
        output.negative = result.value.numerator().negative();
      }
      break;
    }
    case deed_kind::residue_multiply: {
      const auto left_residue = residue<Capacity>::reduced(left.value, modulus.value);
      const auto right_residue = residue<Capacity>::reduced(right.value, modulus.value);
      if (!left_residue.accepted()) {
        attach_receipt(output, left_residue.receipt);
        break;
      }
      const auto result = multiply(left_residue.value, right_residue.value);
      attach_receipt(output, result.receipt);
      output.primary = encode(result.value.value());
      output.secondary = encode(result.value.modulus());
      break;
    }
    case deed_kind::field_inverse: {
      const auto field_value = prime_field_element<Capacity>::admitted(
          left.value, modulus.value);
      if (!field_value.accepted()) {
        attach_receipt(output, field_value.receipt);
        break;
      }
      const auto result = inverse(field_value.value);
      attach_receipt(output, result.receipt);
      output.primary = encode(result.value.value().value());
      output.secondary = encode(result.value.value().modulus());
      break;
    }
    case deed_kind::polynomial_multiply: {
      polynomial<unsigned_integer<Capacity>, 8> left_polynomial{};
      polynomial<unsigned_integer<Capacity>, 8> right_polynomial{};
      for (std::size_t index = 0; index < input.left.used; ++index) {
        left_polynomial.set_coefficient(
            index, unsigned_integer<Capacity>::from_word(input.left.limbs[index]));
      }
      for (std::size_t index = 0; index < input.right.used; ++index) {
        right_polynomial.set_coefficient(
            index, unsigned_integer<Capacity>::from_word(input.right.limbs[index]));
      }
      const auto result = multiply(left_polynomial, right_polynomial);
      attach_receipt(output, result.receipt);
      for (std::size_t index = 0;
           result.accepted() && index < result.value.size();
           ++index) {
        output.auxiliary[index] = result.value.coefficient(index).limb(0);
      }
      break;
    }
    case deed_kind::projective_equality: {
      const projective_pair<unsigned_integer<Capacity>> first{
          unsigned_integer<Capacity>::from_word(input.left.limbs[0]),
          unsigned_integer<Capacity>::from_word(input.left.limbs[1])};
      const projective_pair<unsigned_integer<Capacity>> second{
          unsigned_integer<Capacity>::from_word(input.right.limbs[0]),
          unsigned_integer<Capacity>::from_word(input.right.limbs[1])};
      const auto result = projectively_equal(first, second);
      attach_receipt(output, result.receipt);
      output.relation = result.equal;
      break;
    }
    case deed_kind::representation_round_trip: {
      const auto bytes = encode_big_endian(left.value);
      const auto result = decode_big_endian(bytes);
      output.primary = encode(result);
      output.relation = result == left.value;
      output.witness_hash = stable_hash(result).value();
      output.required_limbs = static_cast<std::uint16_t>(result.used());
      break;
    }
    case deed_kind::promote_to_384: {
      const auto result = promote<deed_maximum_limbs>(left.value);
      attach_receipt(output, result.receipt);
      output.primary = encode(result.value);
      break;
    }
  }
  return output;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr deed_output execute_deed(
    const deed_input& input) noexcept {
  switch (input.tier_limbs) {
    case 2:
      return execute_deed_at_capacity<2>(input);
    case 3:
      return execute_deed_at_capacity<3>(input);
    case 4:
      return execute_deed_at_capacity<4>(input);
    case 5:
      return execute_deed_at_capacity<5>(input);
    case 6:
      return execute_deed_at_capacity<6>(input);
    default: {
      deed_output output{};
      output.case_identity = input.case_identity;
      output.kind = input.kind;
      output.state = status::capacity_refused;
      output.admitted_limbs = input.tier_limbs;
      output.required_limbs = input.left.used;
      return output;
    }
  }
}

}  // namespace holonics::exact

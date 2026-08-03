#include "r1_oracle.hpp"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <exception>

#include <boost/multiprecision/cpp_int.hpp>

namespace boost {

BOOST_NORETURN void throw_exception(const std::exception&) { std::abort(); }

BOOST_NORETURN void throw_exception(const std::exception&, const source_location&) {
  std::abort();
}

}  // namespace boost

namespace holonics::tests {
namespace {

using boost::multiprecision::cpp_int;

[[nodiscard]] cpp_int decode_integer(const exact::encoded_integer& encoded) {
  cpp_int value = 0;
  for (std::size_t index = encoded.used; index != 0; --index) {
    value <<= 64;
    value += encoded.limbs[index - 1];
  }
  return value;
}

[[nodiscard]] std::size_t limbs(const cpp_int& value) {
  if (value == 0) {
    return 0;
  }
  return static_cast<std::size_t>(boost::multiprecision::msb(value) / 64 + 1);
}

[[nodiscard]] exact::encoded_integer encode_integer(cpp_int value) {
  exact::encoded_integer encoded{};
  const cpp_int mask = (cpp_int{1} << 64) - 1;
  while (value != 0 && encoded.used < exact::deed_maximum_limbs) {
    encoded.limbs[encoded.used] = static_cast<std::uint64_t>(value & mask);
    ++encoded.used;
    value >>= 64;
  }
  return encoded;
}

void refuse_capacity(
    exact::deed_output& output,
    std::size_t required,
    std::size_t admitted) {
  output.state = exact::status::capacity_refused;
  output.admitted_limbs = static_cast<std::uint16_t>(admitted);
  output.required_limbs = static_cast<std::uint16_t>(required);
}

[[nodiscard]] bool exceeds(const cpp_int& value, std::size_t capacity) {
  return value >= (cpp_int{1} << (capacity * 64));
}

[[nodiscard]] cpp_int greatest_common_divisor(cpp_int left, cpp_int right) {
  while (right != 0) {
    const cpp_int remainder = left % right;
    left = right;
    right = remainder;
  }
  return left;
}

[[nodiscard]] std::uint64_t stable_hash(const cpp_int& input) {
  std::uint64_t hash = 14'695'981'039'346'656'037ULL;
  constexpr std::uint64_t prime = 1'099'511'628'211ULL;
  cpp_int value = input;
  const std::size_t used = limbs(value);
  for (std::size_t index = 0; index < used; ++index) {
    std::uint64_t limb = static_cast<std::uint64_t>(value & ((cpp_int{1} << 64) - 1));
    for (std::size_t octet = 0; octet < 8; ++octet) {
      hash ^= limb & 255U;
      hash *= prime;
      limb >>= 8U;
    }
    value >>= 64;
  }
  hash ^= static_cast<std::uint64_t>(used);
  hash *= prime;
  return hash;
}

[[nodiscard]] cpp_int modular_power(cpp_int base, cpp_int exponent, const cpp_int& modulus) {
  cpp_int result = 1;
  while (exponent != 0) {
    if ((exponent & 1) != 0) {
      result = (result * base) % modulus;
    }
    exponent >>= 1;
    if (exponent != 0) {
      base = (base * base) % modulus;
    }
  }
  return result;
}

}  // namespace

exact::deed_output r1_oracle(const exact::deed_input& input) {
  exact::deed_output output{};
  output.case_identity = input.case_identity;
  output.kind = input.kind;
  const std::size_t capacity = input.tier_limbs;
  if (capacity != 2 && capacity != 3 && capacity != 4 && capacity != 5 && capacity != 6) {
    refuse_capacity(output, input.left.used, capacity);
    return output;
  }
  output.admitted_limbs = static_cast<std::uint16_t>(capacity);
  if (input.left.used > capacity || input.right.used > capacity ||
      input.modulus.used > capacity) {
    const std::size_t required = std::max({
        static_cast<std::size_t>(input.left.used),
        static_cast<std::size_t>(input.right.used),
        static_cast<std::size_t>(input.modulus.used)});
    refuse_capacity(output, required, capacity);
    return output;
  }

  const cpp_int left = decode_integer(input.left);
  const cpp_int right = decode_integer(input.right);
  const cpp_int modulus = decode_integer(input.modulus);
  cpp_int primary = 0;
  cpp_int secondary = 0;

  switch (input.kind) {
    case exact::deed_kind::add:
      primary = left + right;
      if (exceeds(primary, capacity)) {
        refuse_capacity(output, limbs(primary), capacity);
        return output;
      }
      output.required_limbs = static_cast<std::uint16_t>(limbs(primary));
      break;
    case exact::deed_kind::subtract:
      if (left < right) {
        output.state = exact::status::negative_refused;
        return output;
      }
      primary = left - right;
      output.required_limbs = static_cast<std::uint16_t>(limbs(primary));
      break;
    case exact::deed_kind::multiply:
      primary = left * right;
      if (exceeds(primary, capacity)) {
        refuse_capacity(output, limbs(left) + limbs(right), capacity);
        return output;
      }
      output.required_limbs = static_cast<std::uint16_t>(limbs(primary));
      break;
    case exact::deed_kind::divide:
      if (right == 0) {
        output.state = exact::status::divide_by_zero;
        return output;
      }
      primary = left / right;
      secondary = left % right;
      output.required_limbs = static_cast<std::uint16_t>(limbs(primary));
      break;
    case exact::deed_kind::greatest_common_divisor:
      primary = greatest_common_divisor(left, right);
      output.required_limbs = static_cast<std::uint16_t>(limbs(primary));
      break;
    case exact::deed_kind::shift_left:
      primary = left << input.shift;
      if (exceeds(primary, capacity)) {
        refuse_capacity(output, limbs(primary), capacity);
        return output;
      }
      output.required_limbs = static_cast<std::uint16_t>(limbs(primary));
      break;
    case exact::deed_kind::signed_add: {
      const cpp_int signed_left = input.left_negative ? -left : left;
      const cpp_int signed_right = input.right_negative ? -right : right;
      const cpp_int sum = signed_left + signed_right;
      output.negative = sum < 0;
      primary = output.negative ? -sum : sum;
      if (exceeds(primary, capacity)) {
        refuse_capacity(output, limbs(primary), capacity);
        return output;
      }
      output.required_limbs = static_cast<std::uint16_t>(limbs(primary));
      break;
    }
    case exact::deed_kind::normalize_rational: {
      if (right == 0) {
        output.state = exact::status::zero_denominator;
        return output;
      }
      if (left == 0) {
        secondary = 1;
        break;
      }
      const cpp_int divisor = greatest_common_divisor(left, right);
      primary = left / divisor;
      secondary = right / divisor;
      output.negative = input.left_negative;
      output.required_limbs = static_cast<std::uint16_t>(
          std::max(limbs(primary), limbs(secondary)));
      break;
    }
    case exact::deed_kind::residue_multiply:
      if (modulus == 0) {
        output.state = exact::status::invalid_modulus;
        return output;
      }
      primary = (left % modulus) * (right % modulus);
      if (exceeds(primary, capacity)) {
        refuse_capacity(output, limbs(left % modulus) + limbs(right % modulus), capacity);
        return output;
      }
      primary %= modulus;
      secondary = modulus;
      output.required_limbs = static_cast<std::uint16_t>(limbs(modulus));
      break;
    case exact::deed_kind::field_inverse:
      if (modulus == 0) {
        output.state = exact::status::invalid_modulus;
        return output;
      }
      if (left % modulus == 0 || modulus < 2) {
        output.state = exact::status::noninvertible;
        return output;
      }
      primary = modular_power(left % modulus, modulus - 2, modulus);
      secondary = modulus;
      output.required_limbs = static_cast<std::uint16_t>(limbs(modulus));
      break;
    case exact::deed_kind::polynomial_multiply: {
      if (input.left.used == 0 || input.right.used == 0) {
        break;
      }
      const std::size_t required = static_cast<std::size_t>(input.left.used) +
                                   static_cast<std::size_t>(input.right.used) - 1;
      if (required > exact::deed_auxiliary_words) {
        output.state = exact::status::degree_refused;
        output.required_limbs = static_cast<std::uint16_t>(required);
        return output;
      }
      for (std::size_t left_index = 0; left_index < input.left.used; ++left_index) {
        for (std::size_t right_index = 0; right_index < input.right.used; ++right_index) {
          const cpp_int product =
              cpp_int{input.left.limbs[left_index]} * input.right.limbs[right_index];
          const std::size_t output_index = left_index + right_index;
          const cpp_int sum = cpp_int{output.auxiliary[output_index]} + product;
          if (exceeds(sum, capacity)) {
            refuse_capacity(output, limbs(sum), capacity);
            return output;
          }
          output.auxiliary[output_index] = static_cast<std::uint64_t>(sum);
        }
      }
      output.required_limbs = static_cast<std::uint16_t>(required);
      return output;
    }
    case exact::deed_kind::projective_equality: {
      const cpp_int left_first = input.left.limbs[0];
      const cpp_int left_second = input.left.limbs[1];
      const cpp_int right_first = input.right.limbs[0];
      const cpp_int right_second = input.right.limbs[1];
      if ((left_first == 0 && left_second == 0) ||
          (right_first == 0 && right_second == 0)) {
        output.state = exact::status::invalid_projective_pair;
        return output;
      }
      const cpp_int first_cross = left_first * right_second;
      const cpp_int second_cross = left_second * right_first;
      if (exceeds(first_cross, capacity) || exceeds(second_cross, capacity)) {
        refuse_capacity(output, std::max(limbs(first_cross), limbs(second_cross)), capacity);
        return output;
      }
      output.relation = first_cross == second_cross;
      output.required_limbs = static_cast<std::uint16_t>(limbs(first_cross));
      return output;
    }
    case exact::deed_kind::representation_round_trip:
      primary = left;
      output.relation = true;
      output.witness_hash = stable_hash(left);
      output.required_limbs = static_cast<std::uint16_t>(limbs(left));
      break;
    case exact::deed_kind::promote_to_384:
      primary = left;
      output.admitted_limbs = static_cast<std::uint16_t>(exact::deed_maximum_limbs);
      output.required_limbs = static_cast<std::uint16_t>(limbs(left));
      break;
  }
  output.primary = encode_integer(primary);
  output.secondary = encode_integer(secondary);
  return output;
}

bool equal_deed_output(
    const exact::deed_output& left,
    const exact::deed_output& right) noexcept {
  if (left.case_identity != right.case_identity || left.kind != right.kind ||
      left.state != right.state || left.admitted_limbs != right.admitted_limbs ||
      left.required_limbs != right.required_limbs || left.relation != right.relation ||
      left.negative != right.negative || left.primary.used != right.primary.used ||
      left.secondary.used != right.secondary.used || left.witness_hash != right.witness_hash) {
    return false;
  }
  for (std::size_t index = 0; index < exact::deed_maximum_limbs; ++index) {
    if (left.primary.limbs[index] != right.primary.limbs[index] ||
        left.secondary.limbs[index] != right.secondary.limbs[index]) {
      return false;
    }
  }
  for (std::size_t index = 0; index < exact::deed_auxiliary_words; ++index) {
    if (left.auxiliary[index] != right.auxiliary[index]) {
      return false;
    }
  }
  return true;
}

}  // namespace holonics::tests

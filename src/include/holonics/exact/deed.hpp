#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/finite_field.hpp>
#include <holonics/exact/polynomial.hpp>
#include <holonics/exact/projective.hpp>
#include <holonics/exact/rational.hpp>
#include <holonics/exact/representation.hpp>

namespace holonics::exact {

inline constexpr std::size_t deed_maximum_limbs = 6;
inline constexpr std::size_t deed_auxiliary_words = 8;

enum class deed_kind : std::uint8_t {
  add,
  subtract,
  multiply,
  divide,
  greatest_common_divisor,
  shift_left,
  signed_add,
  normalize_rational,
  residue_multiply,
  field_inverse,
  polynomial_multiply,
  projective_equality,
  representation_round_trip,
  promote_to_384
};

struct encoded_integer final {
  std::uint64_t limbs[deed_maximum_limbs]{};
  std::uint8_t used{};
};

struct deed_input final {
  std::uint64_t case_identity{};
  deed_kind kind{deed_kind::add};
  std::uint8_t tier_limbs{2};
  bool left_negative{};
  bool right_negative{};
  std::uint16_t shift{};
  encoded_integer left{};
  encoded_integer right{};
  encoded_integer modulus{};
};

struct deed_output final {
  std::uint64_t case_identity{};
  deed_kind kind{deed_kind::add};
  status state{status::exact};
  std::uint16_t admitted_limbs{};
  std::uint16_t required_limbs{};
  bool relation{};
  bool negative{};
  encoded_integer primary{};
  encoded_integer secondary{};
  std::uint64_t auxiliary[deed_auxiliary_words]{};
  std::uint64_t witness_hash{};
};

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<unsigned_integer<Capacity>> decode(
    const encoded_integer& encoded) noexcept {
  return unsigned_integer<Capacity>::from_limbs(
      encoded.limbs, encoded.used, limb_order::least_significant_first);
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr encoded_integer encode(
    const unsigned_integer<Capacity>& value) noexcept {
  encoded_integer result{};
  result.used = static_cast<std::uint8_t>(value.used());
  for (std::size_t index = 0; index < value.used(); ++index) {
    result.limbs[index] = value.limb(index);
  }
  return result;
}

HOLONICS_CALLABLE constexpr void attach_receipt(
    deed_output& output,
    operation_receipt receipt) noexcept {
  output.state = receipt.state;
  output.admitted_limbs = receipt.admitted_limbs;
  output.required_limbs = receipt.required_limbs;
}

}  // namespace holonics::exact

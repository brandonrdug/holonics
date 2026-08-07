#include "r1_cases.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <initializer_list>

namespace holonics::tests {
namespace {

[[nodiscard]] exact::encoded_integer encoded(std::initializer_list<std::uint64_t> limbs) {
  exact::encoded_integer result{};
  for (const std::uint64_t limb : limbs) {
    result.limbs[result.used] = limb;
    ++result.used;
  }
  while (result.used != 0 && result.limbs[result.used - 1] == 0) {
    --result.used;
  }
  return result;
}

[[nodiscard]] exact::deed_input base_case(
    std::size_t slot,
    exact::deed_kind kind,
    std::uint8_t tier) {
  exact::deed_input input{};
  input.case_identity = 4'096U + static_cast<std::uint64_t>(slot);
  input.kind = kind;
  input.tier_limbs = tier;
  return input;
}

void set_named_cases(r1_input_batch& cases) {
  using exact::deed_kind;
  constexpr std::uint64_t maximum = ~std::uint64_t{0};
  cases[0] = base_case(0, deed_kind::add, 2);
  cases[0].left = encoded({maximum, maximum});
  cases[0].right = encoded({1});
  cases[1] = base_case(1, deed_kind::add, 3);
  cases[1].left = encoded({maximum});
  cases[1].right = encoded({1});
  cases[2] = base_case(2, deed_kind::subtract, 2);
  cases[2].left = encoded({7});
  cases[2].right = encoded({9});
  cases[3] = base_case(3, deed_kind::multiply, 4);
  cases[3].left = encoded({maximum - 2, 17});
  cases[3].right = encoded({31, 5});
  cases[4] = base_case(4, deed_kind::divide, 6);
  cases[4].left = encoded({0, 0, 1, 9});
  cases[4].right = encoded({3});
  cases[5] = base_case(5, deed_kind::divide, 2);
  cases[5].left = encoded({99});
  cases[6] = base_case(6, deed_kind::greatest_common_divisor, 2);
  cases[6].left = encoded({48});
  cases[6].right = encoded({18});
  cases[7] = base_case(7, deed_kind::shift_left, 2);
  cases[7].left = encoded({0, std::uint64_t{1} << 63U});
  cases[7].shift = 1;
  cases[8] = base_case(8, deed_kind::signed_add, 2);
  cases[8].left = encoded({100});
  cases[8].right = encoded({40});
  cases[8].left_negative = true;
  cases[9] = base_case(9, deed_kind::normalize_rational, 2);
  cases[9].left = encoded({42});
  cases[9].right = encoded({56});
  cases[9].left_negative = true;
  cases[10] = base_case(10, deed_kind::normalize_rational, 2);
  cases[10].left = encoded({1});
  cases[11] = base_case(11, deed_kind::residue_multiply, 2);
  cases[11].left = encoded({123'456});
  cases[11].right = encoded({789'012});
  cases[11].modulus = encoded({1'000'003});
  cases[12] = base_case(12, deed_kind::field_inverse, 2);
  cases[12].left = encoded({5});
  cases[12].modulus = encoded({17});
  cases[13] = base_case(13, deed_kind::polynomial_multiply, 6);
  cases[13].left = encoded({1, 2, 3});
  cases[13].right = encoded({4, 5});
  cases[14] = base_case(14, deed_kind::projective_equality, 2);
  cases[14].left = encoded({2, 3});
  cases[14].right = encoded({4, 6});
  cases[15] = base_case(15, deed_kind::projective_equality, 2);
  cases[15].right = encoded({1, 1});
  cases[16] = base_case(16, deed_kind::representation_round_trip, 6);
  cases[16].left = encoded({0x0123'4567'89ab'cdefULL, maximum, 0, 7, 11, 13});
  cases[17] = base_case(17, deed_kind::promote_to_384, 2);
  cases[17].left = encoded({maximum, maximum});
  cases[18] = base_case(18, deed_kind::add, 5);
  cases[18].left = encoded({1});
  cases[18].right = encoded({2});
  cases[19] = base_case(19, deed_kind::multiply, 2);
  cases[19].left = encoded({maximum, maximum});
  cases[19].right = encoded({maximum});
}

void set_generated_cases(r1_input_batch& cases) {
  using exact::deed_kind;
  constexpr std::array<std::uint8_t, 4> tiers{2, 3, 4, 6};
  for (std::size_t group = 0; group < 12; ++group) {
    const std::size_t slot = 20 + group * 6;
    const std::uint8_t tier = tiers[group % tiers.size()];
    const std::uint64_t seed = 0x9e37'79b9'7f4a'7c15ULL *
        static_cast<std::uint64_t>(group + 21);
    const std::uint64_t companion =
        (seed ^ (seed >> 29U) ^ 0xa5a5'5a5a'c3c3'3c3cULL) | 1U;
    const auto left = encoded({seed, seed >> 7U});
    const auto right = encoded({companion, companion >> 11U});
    const auto small_left = encoded({seed & 0xffff'ffffU});
    const auto small_right = encoded({companion & 0xffff'ffffU});
    cases[slot] = base_case(slot, deed_kind::add, tier);
    cases[slot].left = left;
    cases[slot].right = right;
    cases[slot + 1] = base_case(slot + 1, deed_kind::add, tier);
    cases[slot + 1].left = right;
    cases[slot + 1].right = left;
    cases[slot + 2] = base_case(slot + 2, deed_kind::multiply, tier);
    cases[slot + 2].left = small_left;
    cases[slot + 2].right = small_right;
    cases[slot + 3] = base_case(slot + 3, deed_kind::multiply, tier);
    cases[slot + 3].left = small_right;
    cases[slot + 3].right = small_left;
    cases[slot + 4] = base_case(slot + 4, deed_kind::greatest_common_divisor, tier);
    cases[slot + 4].left = left;
    cases[slot + 4].right = right;
    cases[slot + 5] = base_case(slot + 5, deed_kind::greatest_common_divisor, tier);
    cases[slot + 5].left = right;
    cases[slot + 5].right = left;
  }
  cases[92] = base_case(92, deed_kind::add, 6);
  cases[92].left = encoded({7, 11, 13});
  cases[93] = base_case(93, deed_kind::multiply, 6);
  cases[93].left = cases[92].left;
  cases[93].right = encoded({1});
  cases[94] = base_case(94, deed_kind::representation_round_trip, 6);
  cases[94].left = cases[92].left;
  cases[95] = base_case(95, deed_kind::representation_round_trip, 2);
  cases[96] = base_case(96, deed_kind::add, 5);
  cases[96].left = encoded({1, 2, 3, 4, 5});
  cases[96].right = encoded({6, 7, 8, 9});
  cases[97] = base_case(97, deed_kind::add, 5);
  cases[97].left = cases[96].right;
  cases[97].right = cases[96].left;
  cases[98] = base_case(98, deed_kind::representation_round_trip, 5);
  cases[98].left = cases[96].left;
  cases[99] = base_case(99, deed_kind::add, 7);
  cases[99].left = encoded({1, 2, 3, 4, 5, 6});
  cases[99].right = encoded({1});
}

[[nodiscard]] bool encoded_equal(
    const exact::encoded_integer& left,
    const exact::encoded_integer& right) noexcept {
  if (left.used != right.used) {
    return false;
  }
  for (std::size_t index = 0; index < exact::deed_maximum_limbs; ++index) {
    if (left.limbs[index] != right.limbs[index]) {
      return false;
    }
  }
  return true;
}

}  // namespace

r1_input_batch r1_cases() {
  r1_input_batch cases{};
  set_named_cases(cases);
  set_generated_cases(cases);
  return cases;
}

bool r1_named_returns_hold(const r1_output_batch& outputs) noexcept {
  return outputs[0].state == exact::status::capacity_refused &&
      outputs[5].state == exact::status::divide_by_zero &&
      outputs[6].primary.used == 1 && outputs[6].primary.limbs[0] == 6 &&
      outputs[9].negative && outputs[9].primary.limbs[0] == 3 &&
      outputs[9].secondary.limbs[0] == 4 && outputs[12].primary.limbs[0] == 7 &&
      outputs[13].auxiliary[0] == 4 && outputs[13].auxiliary[1] == 13 &&
      outputs[13].auxiliary[2] == 22 && outputs[13].auxiliary[3] == 15 &&
      outputs[14].relation && outputs[15].state == exact::status::invalid_projective_pair &&
      outputs[16].relation && outputs[17].admitted_limbs == 6 &&
      outputs[18].state == exact::status::exact && outputs[18].admitted_limbs == 5 &&
      outputs[18].primary.limbs[0] == 3 &&
      outputs[99].state == exact::status::capacity_refused &&
      outputs[99].admitted_limbs == 7;
}

std::size_t r1_algebraic_failures(
    const r1_input_batch& inputs,
    const r1_output_batch& outputs) noexcept {
  std::size_t failures = 0;
  for (std::size_t group = 0; group < 12; ++group) {
    const std::size_t slot = 20 + group * 6;
    for (std::size_t pair = 0; pair < 3; ++pair) {
      const auto& left = outputs[slot + pair * 2];
      const auto& right = outputs[slot + pair * 2 + 1];
      if (left.state != exact::status::exact || right.state != exact::status::exact ||
          !encoded_equal(left.primary, right.primary)) {
        ++failures;
      }
    }
  }
  if (!encoded_equal(outputs[92].primary, inputs[92].left)) {
    ++failures;
  }
  if (!encoded_equal(outputs[93].primary, inputs[93].left)) {
    ++failures;
  }
  if (!outputs[94].relation || !encoded_equal(outputs[94].primary, inputs[94].left)) {
    ++failures;
  }
  if (!outputs[95].relation || outputs[95].primary.used != 0) {
    ++failures;
  }
  if (!encoded_equal(outputs[96].primary, outputs[97].primary)) {
    ++failures;
  }
  if (!outputs[98].relation || !encoded_equal(outputs[98].primary, inputs[98].left)) {
    ++failures;
  }
  return failures;
}

}  // namespace holonics::tests

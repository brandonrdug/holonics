#include "r21_cases.hpp"

namespace {

[[nodiscard]] int verify_exact_integer_law() noexcept {
  using namespace holonics::organ::blind_integer_detail;
  std::uint64_t quotient = 0;
  std::uint64_t remainder = 0;
  int failures = !divide_unsigned(18'446'744'073'709'551'615ULL, 10U,
      quotient, remainder);
  failures += quotient != 1'844'674'407'370'955'161ULL || remainder != 5U;
  failures += !divide_unsigned(18'446'744'073'709'551'615ULL,
      9'223'372'036'854'775'809ULL, quotient, remainder);
  failures += quotient != 1U || remainder != 9'223'372'036'854'775'806ULL;
  failures += divide_unsigned(1U, 0U, quotient, remainder);
  std::int64_t signed_quotient = 0;
  std::int64_t signed_remainder = 0;
  failures += !divide(-37, 5, signed_quotient, signed_remainder) ||
      signed_quotient != -7 || signed_remainder != -2;
  failures += !divide(37, -5, signed_quotient, signed_remainder) ||
      signed_quotient != -7 || signed_remainder != 2;
  failures += !divide_exact(-36, -6, signed_quotient) || signed_quotient != 6;
  failures += divide_exact(7, 3, signed_quotient);
  std::int64_t product = 0;
  failures += !multiply(exact_limit, 1, product) || product != exact_limit;
  failures += multiply(exact_limit, 2, product);
  return failures;
}

[[nodiscard]] int verify_code(const holonics::organ::blind_reconstruction_foundation& foundation,
    holonics::organ::blind_reconstruction_receipt& receipt) noexcept {
  using namespace holonics;
  organ::blind_code_detail::form_code_population(foundation.code, receipt.code);
  for (std::uint8_t slot = 0; slot < organ::blind_pair_capacity; ++slot) {
    organ::blind_code_detail::form_pair_incidence(
        foundation.code, receipt.code, slot, receipt.pairs[slot]);
  }
  int failures = 0;
  const std::uint16_t expected[8]{1, 0, 0, 7, 7, 0, 0, 1};
  const std::int64_t dual[8]{1, 0, 0, 0, 7, 0, 0, 0};
  failures += !receipt.code.exact || receipt.code.codeword_count != 16 ||
      receipt.code.minimum_distance != 3;
  for (std::uint8_t slot = 0; slot < 8; ++slot) {
    failures += receipt.code.distance_distribution[slot] != expected[slot];
    failures += receipt.code.dual_distribution[slot] != dual[slot];
  }
  const std::uint8_t distances[3]{3, 4, 7};
  const std::uint8_t cells[3]{20, 20, 8};
  for (std::uint8_t slot = 0; slot < 3; ++slot) {
    failures += !receipt.pairs[slot].exact || receipt.pairs[slot].distance != distances[slot] ||
        receipt.pairs[slot].cell_count != cells[slot] ||
        !receipt.pairs[slot].candidates[3].admitted;
  }
  failures += !organ::blind_code_detail::same_factor(receipt.pairs[0], receipt.pairs[1]);
  failures += receipt.pairs[0].candidates[0].admitted ||
      !receipt.pairs[2].candidates[0].admitted;
  return failures;
}

[[nodiscard]] int verify_moments(const holonics::organ::blind_reconstruction_foundation& foundation,
    holonics::organ::blind_reconstruction_receipt& receipt) noexcept {
  using namespace holonics;
  for (std::uint8_t slot = 0; slot < organ::blind_moment_case_capacity; ++slot) {
    organ::blind_moment_detail::form_moment_root(
        foundation.moments.cases[slot], slot, receipt.moments[slot]);
  }
  int failures = 0;
  const std::int64_t determinants[3]{36, 900, 4'410'000};
  const std::int64_t roots[3][4]{{1, 2, 4, 0}, {-2, 1, 3, 0}, {0, 2, 5, 7}};
  const std::uint8_t degrees[3]{3, 3, 4};
  for (std::uint8_t slot = 0; slot < 3; ++slot) {
    const auto& value = receipt.moments[slot];
    failures += !value.exact || !value.pencil_newton_agree ||
        !value.vandermonde_square || value.hankel_determinant != determinants[slot] ||
        value.discriminant != determinants[slot] || value.root_count != degrees[slot];
    for (std::uint8_t root = 0; root < degrees[slot]; ++root) {
      failures += value.roots[root] != roots[slot][root];
    }
  }
  failures += !receipt.moments[3].exact || receipt.moments[3].hankel_determinant != 0 ||
      receipt.moments[3].discriminant != 0 ||
      receipt.moments[3].obstruction != organ::blind_obstruction::singular_root_fiber;
  failures += !receipt.moments[4].exact || receipt.moments[4].access_complete ||
      receipt.moments[4].obstruction != organ::blind_obstruction::moment_access_refused;
  return failures;
}

}  // namespace

int main() {
  using namespace holonics;
  const auto mount = tests::r21_case(tests::r21_host_regular_singular_rest(),
      tests::r21_host_code_card(), tests::r21_host_moment_card());
  organ::blind_reconstruction_receipt receipt{};
  const int code_failures = verify_code(mount.foundation, receipt);
  const int moment_failures = verify_moments(mount.foundation, receipt);
  int failures = verify_exact_integer_law() + code_failures + moment_failures;
  organ::blind_reconstruction_detail::close_blind_reconstruction(
      mount.foundation, mount.question, receipt);
  const bool close_failed = !receipt.theory_formed || !receipt.all_exact;
  failures += close_failed;
  auto changed_code = mount.foundation.code;
  changed_code.parity_rows[0] = 83;
  organ::code_population_receipt changed_population{};
  organ::blind_code_detail::form_code_population(changed_code, changed_population);
  bool same_population = changed_population.codeword_count == receipt.code.codeword_count;
  for (std::uint8_t slot = 0; slot < receipt.code.codeword_count; ++slot) {
    same_population = same_population &&
        changed_population.codewords[slot] == receipt.code.codewords[slot];
  }
  const bool code_ablation_failed = same_population;
  failures += code_ablation_failed;
  auto changed_moment = mount.foundation.moments.cases[0];
  ++changed_moment.moments[5];
  organ::moment_root_receipt changed_root{};
  organ::blind_moment_detail::form_moment_root(changed_moment, 0, changed_root);
  const bool moment_ablation_failed = changed_root.pencil_newton_agree && changed_root.exact;
  failures += moment_ablation_failed;
  return failures == 0 ? 0 : 1;
}

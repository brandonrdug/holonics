#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/commitment.hpp>

namespace holonics::exact {

inline constexpr std::size_t enclosure_source_capacity = 8;
using enclosure_source = integer_polynomial<enclosure_source_capacity>;

/// One certified-enclosure occurrence crossing the device port. `supply_certificate`
/// selects the ablation: when it is false the same enclosure is committed under the
/// uncertified law alone, so the certificate's contribution is isolated rather than
/// asserted.
struct enclosure_deed_input final {
  enclosure_source source{};
  enclosure start{};
  std::uint16_t passes{};
  bool supply_certificate{};
};

struct enclosure_deed_output final {
  enclosure refined{};
  separation_certificate certificate{};
  commitment committed{};
  enclosure_state refinement_state{enclosure_state::admitted};
  std::uint8_t reached_exponent{};
  bool bracketed{};
  bool certificate_revalidates{};
};

/// The complete deed. Identical source runs on the device and on the host
/// conformance path; the returned structure is compared for exact equality.
[[nodiscard]] HOLONICS_CALLABLE constexpr enclosure_deed_output execute_enclosure_deed(
    const enclosure_deed_input& input) noexcept {
  enclosure_deed_output output{};
  const enclosure_step bracketed = enclosure_law::bracket(input.source, input.start);
  output.bracketed = bracketed.accepted();
  if (bracketed.accepted()) {
    const enclosure_step refined =
        enclosure_law::refine_times(input.source, input.start, input.passes);
    output.refined = refined.value;
    output.refinement_state = refined.state;
    output.reached_exponent = refined.reached_exponent;
  } else {
    // An absent bracket is not the end of the deed. The certificate may still
    // name why no root lives here, which is a stronger return than "no sign
    // change was observed".
    output.refined = input.start;
    output.refinement_state = bracketed.state;
    output.reached_exponent = bracketed.reached_exponent;
  }

  output.certificate = separation_law::derive(input.source);
  output.certificate_revalidates =
      separation_law::certifies(input.source, output.certificate);

  if (input.supply_certificate) {
    output.committed = commitment_law::commit_sign(output.refined, output.certificate);
  } else {
    output.committed = commitment_law::commit_sign(output.refined);
  }
  return output;
}

namespace enclosure_deed_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    dyadic left,
    dyadic right) noexcept {
  return left.numerator == right.numerator && left.exponent == right.exponent;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    enclosure left,
    enclosure right) noexcept {
  return equal(left.lower, right.lower) && equal(left.upper, right.upper);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    separation_certificate left,
    separation_certificate right) noexcept {
  return left.numerator == right.numerator && left.denominator == right.denominator &&
      left.admits_zero == right.admits_zero && left.derived == right.derived &&
      left.deflated_degree == right.deflated_degree;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    commitment left,
    commitment right) noexcept {
  return left.value == right.value && left.ground == right.ground &&
      left.certificate_consulted == right.certificate_consulted;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    const enclosure_deed_output& left,
    const enclosure_deed_output& right) noexcept {
  return equal(left.refined, right.refined) &&
      equal(left.certificate, right.certificate) &&
      equal(left.committed, right.committed) &&
      left.refinement_state == right.refinement_state &&
      left.reached_exponent == right.reached_exponent &&
      left.bracketed == right.bracketed &&
      left.certificate_revalidates == right.certificate_revalidates;
}

}  // namespace enclosure_deed_law
}  // namespace holonics::exact

#include "enclosure_cases.hpp"

#include <cstdint>
#include <initializer_list>
#include <limits>

namespace holonics::tests {
namespace {

using holonics::exact::commitment_ground;
using holonics::exact::dyadic;
using holonics::exact::enclosure;
using holonics::exact::enclosure_deed_input;
using holonics::exact::enclosure_deed_output;
using holonics::exact::enclosure_source;
using holonics::exact::enclosure_state;
using holonics::exact::sign_commitment;

// The oracle declares its own aperture. Every product is guarded, and a product
// it cannot prove in range makes the oracle refuse rather than wrap. `refused`
// is reported as a failure by the caller, never as agreement.
constexpr std::int64_t oracle_ceiling = std::numeric_limits<std::int64_t>::max() / 4;

bool product_in_range(std::int64_t left, std::int64_t right) {
  const std::int64_t left_magnitude = left < 0 ? -left : left;
  const std::int64_t right_magnitude = right < 0 ? -right : right;
  if (left_magnitude == 0 || right_magnitude == 0) {
    return true;
  }
  return left_magnitude <= oracle_ceiling / right_magnitude;
}

bool shift_in_range(std::int64_t value, std::uint8_t shift) {
  const std::int64_t magnitude = value < 0 ? -value : value;
  return shift < 62 && magnitude <= (oracle_ceiling >> shift);
}

enclosure_source source_of(std::initializer_list<std::int64_t> coefficients) {
  enclosure_source source{};
  std::size_t index = 0;
  for (const std::int64_t value : coefficients) {
    source.coefficient[index] = value;
    ++index;
  }
  source.used = index;
  return source;
}

// Independent evaluation of the declared source at numerator / 2^exponent by
// direct term summation. This is written separately from the carrier under test:
// it sums explicit terms rather than transporting a Horner accumulator, so an
// error in the carrier's recurrence cannot be reproduced here.
// Returns 2 when the oracle refuses.
int independent_sign(const enclosure_source& source, dyadic point) {
  if (source.used == 0) {
    return 2;
  }
  if (!shift_in_range(1, point.exponent)) {
    return 2;
  }
  const std::int64_t denominator = std::int64_t{1} << point.exponent;
  const std::size_t degree = source.used - 1;
  std::int64_t total = 0;
  for (std::size_t index = 0; index <= degree; ++index) {
    std::int64_t term = source.coefficient[index];
    for (std::size_t step = 0; step < index; ++step) {
      if (!product_in_range(term, point.numerator)) {
        return 2;
      }
      term *= point.numerator;
    }
    for (std::size_t step = 0; step < degree - index; ++step) {
      if (!product_in_range(term, denominator)) {
        return 2;
      }
      term *= denominator;
    }
    if (!product_in_range(total + term, 1) ||
        (term > 0 && total > oracle_ceiling - term) ||
        (term < 0 && total < -oracle_ceiling - term)) {
      return 2;
    }
    total += term;
  }
  if (total > 0) {
    return 1;
  }
  return total < 0 ? -1 : 0;
}

// Returns 2 when the oracle refuses.
int independent_order(dyadic left, dyadic right) {
  if (!shift_in_range(left.numerator, right.exponent) ||
      !shift_in_range(right.numerator, left.exponent)) {
    return 2;
  }
  const std::int64_t scaled_left = left.numerator << right.exponent;
  const std::int64_t scaled_right = right.numerator << left.exponent;
  if (scaled_left > scaled_right) {
    return 1;
  }
  return scaled_left < scaled_right ? -1 : 0;
}

bool independent_inside(enclosure current, std::int64_t numerator, std::int64_t denominator) {
  for (const dyadic point : {current.lower, current.upper}) {
    const std::int64_t magnitude = point.numerator < 0 ? -point.numerator : point.numerator;
    if (!product_in_range(magnitude, denominator) ||
        !shift_in_range(numerator, point.exponent)) {
      return false;
    }
    if (!(magnitude * denominator < (numerator << point.exponent))) {
      return false;
    }
  }
  return true;
}

}  // namespace

std::array<enclosure_deed_input, enclosure_case_count> enclosure_cases() {
  const enclosure_source quadratic = source_of({-2, 0, 1});
  const enclosure_source cubic = source_of({0, -2, 0, 1});
  const enclosure_source affine = source_of({-1, 2});
  const enclosure_source empty{};

  std::array<enclosure_deed_input, enclosure_case_count> cases{};
  cases[0] = {quadratic, enclosure{dyadic{1, 0}, dyadic{2, 0}}, 12, true};
  cases[1] = {quadratic, enclosure{dyadic{1, 0}, dyadic{2, 0}}, 64, true};
  cases[2] = {quadratic, enclosure{dyadic{-2, 0}, dyadic{-1, 0}}, 12, true};
  cases[3] = {cubic, enclosure{dyadic{-1, 1}, dyadic{1, 0}}, 8, true};
  cases[4] = {cubic, enclosure{dyadic{-1, 1}, dyadic{1, 0}}, 8, false};
  cases[5] = {cubic, enclosure{dyadic{-1, 0}, dyadic{1, 0}}, 0, true};
  cases[6] = {quadratic, enclosure{dyadic{-1, 2}, dyadic{1, 2}}, 4, true};
  cases[7] = {affine, enclosure{dyadic{0, 0}, dyadic{1, 0}}, 4, true};
  cases[8] = {empty, enclosure{dyadic{-1, 0}, dyadic{1, 0}}, 2, true};
  cases[9] = {quadratic, enclosure{dyadic{1, 0}, dyadic{-1, 0}}, 4, true};
  return cases;
}

std::array<std::string_view, enclosure_case_count> enclosure_case_names() {
  return {
      "positive-algebraic-enclosure",
      "aperture-refusal-retains-last-admitted",
      "negative-algebraic-enclosure",
      "certified-zero-commitment",
      "certificate-ablation",
      "separation-insufficient",
      "source-contradiction",
      "exact-dyadic-root-collapse",
      "underived-certificate",
      "disordered-enclosure"};
}

bool certified_enclosure_returns(
    const std::array<enclosure_deed_output, enclosure_case_count>& outputs) {
  const bool positive_root = outputs[0].bracketed &&
      outputs[0].refinement_state == enclosure_state::admitted &&
      outputs[0].committed.value == sign_commitment::positive &&
      outputs[0].committed.ground == commitment_ground::strict_endpoint &&
      outputs[0].certificate.derived && outputs[0].certificate_revalidates &&
      outputs[0].certificate.numerator == 2 && outputs[0].certificate.denominator == 3 &&
      !outputs[0].certificate.admits_zero;
  const bool negative_root = outputs[2].committed.value == sign_commitment::negative &&
      outputs[2].committed.ground == commitment_ground::strict_endpoint;
  const bool certified_zero = outputs[3].committed.value == sign_commitment::zero &&
      outputs[3].committed.ground == commitment_ground::certified_zero &&
      outputs[3].committed.certificate_consulted &&
      outputs[3].certificate.admits_zero && outputs[3].certificate_revalidates;
  const bool insufficient = outputs[5].committed.value == sign_commitment::refused &&
      outputs[5].committed.ground == commitment_ground::separation_insufficient;
  const bool contradiction = !outputs[6].bracketed &&
      outputs[6].refinement_state == enclosure_state::bracket_absent &&
      outputs[6].committed.ground == commitment_ground::source_contradiction;
  const bool collapse = outputs[7].committed.value == sign_commitment::positive &&
      outputs[7].refined.lower.numerator == 1 && outputs[7].refined.lower.exponent == 1 &&
      outputs[7].refined.upper.numerator == 1 && outputs[7].refined.upper.exponent == 1;
  const bool underived = !outputs[8].certificate.derived &&
      outputs[8].committed.ground == commitment_ground::certificate_underived;
  const bool disordered = outputs[9].committed.value == sign_commitment::refused &&
      outputs[9].committed.ground == commitment_ground::enclosure_disordered &&
      outputs[9].refinement_state == enclosure_state::order_refused;
  return positive_root && negative_root && certified_zero && insufficient &&
      contradiction && collapse && underived && disordered;
}

bool certificate_ablation_holds(
    const std::array<enclosure_deed_output, enclosure_case_count>& outputs) {
  // The same enclosure, at the same refinement depth, over the same source.
  // With the certificate it commits to zero; without it, nothing may be
  // committed at any depth.
  const bool identical_enclosure =
      exact::enclosure_deed_law::equal(outputs[3].refined, outputs[4].refined);
  const bool certified = outputs[3].committed.value == sign_commitment::zero;
  const bool ablated = outputs[4].committed.value == sign_commitment::refused &&
      outputs[4].committed.ground == commitment_ground::separation_absent &&
      !outputs[4].committed.certificate_consulted;
  return identical_enclosure && certified && ablated;
}

bool aperture_refusal_holds(
    const std::array<enclosure_deed_output, enclosure_case_count>& outputs) {
  return outputs[1].refinement_state == enclosure_state::aperture_refused &&
      outputs[1].reached_exponent <= exact::dyadic_exponent_ceiling &&
      outputs[1].committed.value == sign_commitment::positive &&
      independent_order(outputs[1].refined.lower, outputs[1].refined.upper) <= 0;
}

bool independent_enclosure_agrees(
    const enclosure_deed_input& input,
    const enclosure_deed_output& output) {
  if (input.source.used == 0) {
    return !output.certificate.derived;
  }
  if (output.committed.ground == commitment_ground::enclosure_disordered) {
    return independent_order(output.refined.lower, output.refined.upper) == 1;
  }
  if (independent_order(output.refined.lower, output.refined.upper) != -1 &&
      independent_order(output.refined.lower, output.refined.upper) != 0) {
    return false;
  }
  if (output.bracketed) {
    const int low = independent_sign(input.source, output.refined.lower);
    const int high = independent_sign(input.source, output.refined.upper);
    if (low != 0 && high != 0 && low == high) {
      return false;
    }
  }
  if (output.committed.value == sign_commitment::zero) {
    return output.certificate.admits_zero &&
        independent_inside(
            output.refined, output.certificate.numerator, output.certificate.denominator);
  }
  if (output.committed.ground == commitment_ground::source_contradiction) {
    return !output.certificate.admits_zero &&
        independent_inside(
            output.refined, output.certificate.numerator, output.certificate.denominator);
  }
  return true;
}

}  // namespace holonics::tests

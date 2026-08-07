#pragma once

#include <cstdint>

#include <holonics/exact/enclosure.hpp>
#include <holonics/exact/separation.hpp>

namespace holonics::exact {

/// The committed sign of the quantity an enclosure encloses. `refused` is a
/// first-class return: it means the enclosure is a lawful object about which no
/// exact sign may yet be asserted.
enum class sign_commitment : std::uint8_t { refused, negative, zero, positive };

/// Why the commitment resolved the way it did. This is the inspected content of
/// the deed; a commitment without its ground is not admissible testimony.
enum class commitment_ground : std::uint8_t {
  strict_endpoint,
  certified_zero,
  separation_absent,
  separation_insufficient,
  source_contradiction,
  certificate_underived,
  enclosure_disordered
};

struct commitment final {
  sign_commitment value{sign_commitment::refused};
  commitment_ground ground{commitment_ground::separation_absent};
  bool certificate_consulted{};
};

namespace commitment_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr commitment from_endpoints(
    enclosure current) noexcept {
  commitment decided{};
  if (!enclosure_law::ordered(current)) {
    // A disordered pair is not a set, and nothing may be committed about what it
    // would have enclosed.
    decided.ground = commitment_ground::enclosure_disordered;
    return decided;
  }
  if (enclosure_law::strictly_positive(current)) {
    decided.value = sign_commitment::positive;
    decided.ground = commitment_ground::strict_endpoint;
    return decided;
  }
  if (enclosure_law::strictly_negative(current)) {
    decided.value = sign_commitment::negative;
    decided.ground = commitment_ground::strict_endpoint;
    return decided;
  }
  decided.ground = commitment_ground::separation_absent;
  return decided;
}

/// The uncertified law. An enclosure that straddles zero can be refined without
/// bound and will never commit here. That refusal is the organ's falsifier: if
/// any route reaches a zero commitment through this entry point, the exactness
/// and certificate discipline is unenforced at this seam.
[[nodiscard]] HOLONICS_CALLABLE constexpr commitment commit_sign(
    enclosure current) noexcept {
  return from_endpoints(current);
}

/// The certified law. The strict cases still commit without consulting the
/// certificate. The straddling case commits only when the certificate excludes
/// every nonzero root from the enclosure, and then it commits to zero exactly.
[[nodiscard]] HOLONICS_CALLABLE constexpr commitment commit_sign(
    enclosure current,
    separation_certificate certificate) noexcept {
  commitment decided = from_endpoints(current);
  if (decided.value != sign_commitment::refused ||
      decided.ground == commitment_ground::enclosure_disordered) {
    return decided;
  }
  decided.certificate_consulted = true;
  if (!certificate.derived) {
    decided.ground = commitment_ground::certificate_underived;
    return decided;
  }
  const auto inside = enclosure_law::inside_magnitude(
      current, certificate.numerator, certificate.denominator);
  if (!inside.accepted()) {
    decided.ground = commitment_ground::separation_insufficient;
    return decided;
  }
  if (!inside.value) {
    decided.ground = commitment_ground::separation_insufficient;
    return decided;
  }
  if (!certificate.admits_zero) {
    decided.ground = commitment_ground::source_contradiction;
    return decided;
  }
  decided.value = sign_commitment::zero;
  decided.ground = commitment_ground::certified_zero;
  return decided;
}

/// The complete certified passage over a declared source: bracket, refine within
/// the declared aperture, revalidate the certificate against the source, and
/// commit. Every refusal along the way survives into the returned ground.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr commitment commit_over_source(
    const integer_polynomial<Capacity>& source,
    enclosure start,
    std::uint16_t passes,
    separation_certificate certificate) noexcept {
  commitment decided{};
  const enclosure_step refined = enclosure_law::refine_times(source, start, passes);
  if (!separation_law::certifies(source, certificate)) {
    decided.certificate_consulted = true;
    decided.ground = commitment_ground::certificate_underived;
    return decided;
  }
  return commit_sign(refined.value, certificate);
}

}  // namespace commitment_law
}  // namespace holonics::exact

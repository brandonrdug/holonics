#pragma once

#include <cstdint>

#include <holonics/structure/disposition.hpp>

namespace holonics::body {

using structure::chi_pair;
using structure::chi_projection;
using structure::chi_projection_receipt;
using structure::disposition;
using structure::returned_disposition;

/// The one move, with its four faces named.
///
/// ```text
///   MEETING   the rotor taken between arriving and standing in a frame
///   FLYWHEEL  the HELD rotor -- the groove's standing difference.
///             NOT a store: it is the current's own state.
///   TEST      chi = Delta_new . Delta_flywheel^-1, second order, read by sign
///   DEED      RIDE carries; FOUND deposits one integer winding quantum
/// ```
///
/// The frame eats the first order, so the first invariant is second order. The
/// test is a relation between relations, and the pair it forms is retained
/// whether or not any projection of it is available.
struct swing_input final {
  chi_pair test{};
  exact::word interface_capability{};
  exact::word standing_winding{};
  exact::word receiver{};
  bool hand_residual{};
};

struct swing_return final {
  returned_disposition disposition{};
  chi_pair retained{};
  bool groove_rebased{};
  exact::word next_groove{};
};

namespace swing_law {

/// Precession. The flywheel **never zeroes at the cut — it precesses**, and the
/// past cone it precesses through is read-only.
[[nodiscard]] HOLONICS_CALLABLE constexpr exact::word precess(
    exact::word groove,
    exact::word standing_winding) noexcept {
  return exact::word{groove.value() + standing_winding.value()};
}

/// Is the transported comparison wound? This is a projection and therefore
/// chart-dependent: without a declared chart the question has no answer and the
/// passage must stand OPEN rather than assume flatness.
[[nodiscard]] HOLONICS_CALLABLE constexpr chi_projection_receipt test(
    const swing_input& input,
    chi_projection projection) noexcept {
  return structure::chi_law::project(input.test, projection);
}

/// **The production law.** A re-comparison of already-exposed paths may only
/// RIDE or stand OPEN. It **cannot manufacture a FOUND**: founding is a deed of
/// the body against genuinely new terrain, not a reinterpretation of paths that
/// have already crossed.
///
/// A missing interface capability is not even a candidate. A wound comparison,
/// an oriented hand residual, or an unavailable projection all stand OPEN with
/// the complete pair retained.
[[nodiscard]] HOLONICS_CALLABLE constexpr swing_return rebase_exposed(
    const swing_input& input,
    chi_projection projection) noexcept {
  swing_return result{};
  result.retained = input.test;
  const chi_projection_receipt receipt = test(input, projection);
  if (input.interface_capability.value() == 0) {
    result.disposition = structure::disposition_law::stand_open(
        input.test, receipt, input.receiver);
    return result;
  }
  if (!receipt.available() || input.hand_residual ||
      !structure::chi_law::paths_identical(input.test)) {
    result.disposition = structure::disposition_law::stand_open(
        input.test, receipt, input.receiver);
    return result;
  }
  result.disposition = structure::disposition_law::ride();
  result.groove_rebased = true;
  result.next_groove = precess(input.standing_winding, exact::word{0});
  return result;
}

/// **The body law.** Against genuinely new terrain the deed may found. A wound
/// test deposits exactly one integer winding quantum and pays curvature; a flat
/// test rides and re-bases the groove.
///
/// At the cut the groove is **never replaced**: the prior held rotor precesses
/// and re-bases only at the completion. The founded blade enters the basis; it
/// does not overwrite the groove.
[[nodiscard]] HOLONICS_CALLABLE constexpr swing_return cross(
    const swing_input& input,
    chi_projection projection,
    exact::word winding_quantum) noexcept {
  swing_return result{};
  result.retained = input.test;
  const chi_projection_receipt receipt = test(input, projection);
  if (!receipt.available()) {
    result.disposition = structure::disposition_law::stand_open(
        input.test, receipt, input.receiver);
    return result;
  }
  if (structure::chi_law::paths_identical(input.test) && !input.hand_residual) {
    result.disposition = structure::disposition_law::ride();
    result.groove_rebased = true;
    result.next_groove = precess(input.standing_winding, exact::word{0});
    return result;
  }
  returned_disposition founded{};
  if (!structure::disposition_law::try_found(winding_quantum, founded)) {
    result.disposition = structure::disposition_law::stand_open(
        input.test, receipt, input.receiver);
    return result;
  }
  result.disposition = founded;
  result.groove_rebased = false;
  result.next_groove = precess(input.standing_winding, winding_quantum);
  return result;
}

/// RIDE is cheap because the terrain already paid; FOUND pays curvature. The
/// asymmetry is the law, not an optimization, and it is exposed so a caller
/// cannot price the two the same.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool pays_curvature(
    const swing_return& value) noexcept {
  return value.disposition.state == disposition::found;
}

}  // namespace swing_law
}  // namespace holonics::body

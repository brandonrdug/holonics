#pragma once

#include <cstdint>

#include <holonics/structure/local_transport.hpp>

namespace holonics::structure {

/// `Chi` is the ORDERED PAIR of parallel transports
///
/// ```text
///     Chi = ( T_a12 . T_a01 ,  T_a02 )
/// ```
///
/// **This pair is the general object.** A residual requires an additive carrier.
/// A holonomy defect requires invertibility. Winding, rank, a matrix, and the
/// projective cross-ratio are projections available only after the required
/// chart exists. A projective cross-ratio is one such chart; it is not the
/// definition of `Chi` in every medium.
///
/// Every projection below therefore refuses unless its chart was declared by the
/// source of both transports. The pair itself is always retained: a refused
/// projection loses nothing.
struct chi_pair final {
  local_transport composed{};
  local_transport direct{};
};

enum class chi_projection : std::uint8_t {
  residual,
  holonomy_defect,
  cross_ratio
};

enum class chi_state : std::uint8_t {
  available,
  chart_undeclared,
  not_parallel,
  unadmitted
};

struct chi_projection_receipt final {
  chi_state state{chi_state::unadmitted};
  chi_projection requested{chi_projection::residual};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool available() const noexcept {
    return state == chi_state::available;
  }
};

namespace chi_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool admitted(const chi_pair& pair) noexcept {
  return transport_law::parallel(pair.composed, pair.direct);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr transport_property required_chart(
    chi_projection projection) noexcept {
  switch (projection) {
    case chi_projection::residual: return transport_property::additive;
    case chi_projection::holonomy_defect: return transport_property::invertible;
    case chi_projection::cross_ratio: return transport_property::projective_chart;
  }
  return transport_property::additive;
}

/// May this projection be taken? Both transports must declare the chart the
/// projection needs; one alone is not enough, because the projection compares
/// them.
[[nodiscard]] HOLONICS_CALLABLE constexpr chi_projection_receipt project(
    const chi_pair& pair,
    chi_projection projection) noexcept {
  chi_projection_receipt receipt{};
  receipt.requested = projection;
  if (!transport_law::admitted(pair.composed) ||
      !transport_law::admitted(pair.direct)) {
    receipt.state = chi_state::unadmitted;
    return receipt;
  }
  if (!transport_law::parallel(pair.composed, pair.direct)) {
    receipt.state = chi_state::not_parallel;
    return receipt;
  }
  const transport_property chart = required_chart(projection);
  if (!transport_law::carries(pair.composed.declaration, chart) ||
      !transport_law::carries(pair.direct.declaration, chart)) {
    receipt.state = chi_state::chart_undeclared;
    return receipt;
  }
  receipt.state = chi_state::available;
  return receipt;
}

/// Identity of the two paths as transports. This is the only comparison
/// available without a declared chart, and it is a comparison of the ordered
/// pair's members, never of an unformed scalar.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool paths_identical(
    const chi_pair& pair) noexcept {
  return admitted(pair) && pair.composed.identity == pair.direct.identity;
}

/// The pair is retained whole across a refusal. A caller that could not project
/// still holds both transports and may declare a chart later.
[[nodiscard]] HOLONICS_CALLABLE constexpr chi_pair retained(
    const chi_pair& pair) noexcept {
  return pair;
}

}  // namespace chi_law
}  // namespace holonics::structure

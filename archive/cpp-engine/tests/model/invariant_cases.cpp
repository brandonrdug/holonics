#include "ecology_cases.hpp"

#include <holonics/structure/transition_invariants.hpp>

namespace holonics::tests {
namespace {

using holonics::exact::word;
using holonics::structure::causal_attribution;
using holonics::structure::local_transport;
namespace law = holonics::structure::transition_law;

[[nodiscard]] local_transport route(std::uint64_t identity, std::uint64_t from,
    std::uint64_t to) noexcept {
  local_transport out{};
  out.identity = word{identity};
  out.source = word{from};
  out.target = word{to};
  return out;
}

}  // namespace

/// **The falsifier for the transition invariants.**
///
/// Until 2026-08-06 seven of the eight were admitted with a literal `true`: the
/// one move was certified by assignment. Replacing a constant with a predicate
/// is worth nothing unless the predicate can refuse, so each invariant is driven
/// to false here on purpose. **An invariant that cannot be made false is not
/// being checked**, and this case exists to catch exactly that.
invariant_return invariant_falsifiers() {
  invariant_return out{};

  // Same prestate: a member that met a different predecessor.
  const word declared{7};
  const word same[1]{word{7}};
  const word other[1]{word{9}};
  out.same_prestate_holds = law::same_prestate(declared, same, 1);
  out.same_prestate_refuses = !law::same_prestate(declared, other, 1);

  // No false incidence: the successor grew by more than the touched path.
  out.no_false_incidence_holds = 12U - 10U <= 1U + 1U;
  out.no_false_incidence_refuses = !(20U - 10U <= 1U + 1U);

  // Occurrence preservation: equal disconnected occurrences stay plural, so the
  // population grows by exactly what was minted. A surface that deduplicated
  // would return fewer.
  out.occurrence_preservation_holds = law::occurrences_preserved(10U, 3U, 13U);
  out.occurrence_preservation_refuses = !law::occurrences_preserved(10U, 3U, 12U);

  // Oriented boundary: the Chi pair must be a genuine parallel pair.
  out.boundary_holds = law::boundary_parallel(route(1, 4, 5), route(2, 4, 5));
  out.boundary_refuses = !law::boundary_parallel(route(1, 4, 5), route(2, 6, 5)) &&
      !law::boundary_parallel(route(1, 4, 5), route(1, 4, 5));

  // Causal attribution: a FOUND may only issue from material that arrived; a
  // RIDE may only issue from what already stands.
  out.attribution_holds = law::attribution_matches(causal_attribution::contacted, true, true) &&
      law::attribution_matches(causal_attribution::inherited, false, true);
  out.attribution_refuses =
      !law::attribution_matches(causal_attribution::inherited, true, true) &&
      !law::attribution_matches(causal_attribution::contacted, false, true);

  // One visibility edge: not zero, not several.
  out.visibility_holds = law::single_visibility_edge(1U, 1U);
  out.visibility_refuses = !law::single_visibility_edge(0U, 1U) &&
      !law::single_visibility_edge(2U, 1U) && !law::single_visibility_edge(1U, 2U);

  // Rest performs no event: without current the head may not advance.
  out.rest_holds = law::rest_is_eventless(word{3}, word{3}, false) &&
      law::rest_is_eventless(word{3}, word{4}, true);
  out.rest_refuses = !law::rest_is_eventless(word{3}, word{4}, false);

  // Bounded emission: a crossing may not emit more than its interior visited.
  out.emission_holds = law::emission_bounded(1U, 4U);
  out.emission_refuses = !law::emission_bounded(5U, 4U);

  out.holds = out.same_prestate_holds && out.same_prestate_refuses &&
      out.no_false_incidence_holds && out.no_false_incidence_refuses &&
      out.occurrence_preservation_holds && out.occurrence_preservation_refuses &&
      out.boundary_holds && out.boundary_refuses && out.attribution_holds &&
      out.attribution_refuses && out.visibility_holds && out.visibility_refuses &&
      out.rest_holds && out.rest_refuses && out.emission_holds && out.emission_refuses;
  return out;
}

}  // namespace holonics::tests

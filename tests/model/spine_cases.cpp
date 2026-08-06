#include "spine_cases.hpp"

#include <holonics/current/information_receipt.hpp>
#include <holonics/receiver/receiver_current_law.hpp>
#include <holonics/structure/branch_lineage.hpp>
#include <holonics/structure/directed_dependency.hpp>
#include <holonics/structure/relation_atlas.hpp>
#include <holonics/structure/sparse_ordinal_atlas.hpp>

namespace holonics::tests {
namespace {

using holonics::exact::spine_deed_input;
using holonics::exact::spine_deed_output;
using holonics::exact::word;
using holonics::structure::chi_projection;
using holonics::structure::chi_state;
using holonics::structure::disposition;
using holonics::structure::transport_property;

constexpr std::uint8_t projective =
    static_cast<std::uint8_t>(1U << static_cast<std::uint8_t>(transport_property::projective_chart));
constexpr std::uint8_t additive =
    static_cast<std::uint8_t>(1U << static_cast<std::uint8_t>(transport_property::additive));
constexpr std::uint8_t cross_ratio = static_cast<std::uint8_t>(chi_projection::cross_ratio);

spine_deed_input make(std::uint64_t composed, std::uint64_t direct, std::uint64_t capability,
    std::uint8_t declaration, bool hand_residual, bool body_layer) {
  return spine_deed_input{composed, direct, 10, 20, capability, 3, 9, 1,
      declaration, cross_ratio, hand_residual, body_layer};
}

}  // namespace

std::array<spine_deed_input, spine_case_count> spine_cases() {
  return {
      make(1, 1, 7, projective, false, false),   // 0 flat, production -> ride
      make(1, 2, 7, projective, false, false),   // 1 wound, production -> open, never found
      make(1, 2, 7, projective, false, true),    // 2 wound, body -> found with winding
      make(1, 1, 7, projective, false, true),    // 3 flat, body -> ride
      make(1, 1, 0, projective, false, false),   // 4 no interface capability
      make(1, 1, 7, 0, false, false),            // 5 chart undeclared
      make(1, 1, 7, additive, false, false),     // 6 wrong chart declared
      make(1, 1, 7, projective, true, false),    // 7 oriented hand residual
  };
}

std::array<std::string_view, spine_case_count> spine_case_names() {
  return {"flat-production-ride", "wound-production-open-not-found",
      "wound-body-found-with-winding", "flat-body-ride", "no-interface-capability",
      "chart-undeclared", "wrong-chart-declared", "oriented-hand-residual"};
}

bool swing_laws_hold(const std::array<spine_deed_output, spine_case_count>& out) {
  const auto is = [&](std::size_t slot, disposition state) {
    return out[slot].disposition == static_cast<std::uint8_t>(state);
  };
  const bool production_rides = is(0, disposition::ride) && out[0].groove_rebased;
  // THE production law: a re-comparison of exposed paths may never found.
  const bool production_never_founds = is(1, disposition::open) && out[1].winding == 0;
  // The body may found, deposits exactly one winding, and does NOT rebase at the cut.
  const bool body_founds =
      is(2, disposition::found) && out[2].winding == 1 && !out[2].groove_rebased;
  const bool body_rides = is(3, disposition::ride) && out[3].groove_rebased;
  const bool no_capability = is(4, disposition::open);
  const bool undeclared = is(5, disposition::open) &&
      out[5].refusal_state == static_cast<std::uint8_t>(chi_state::chart_undeclared);
  const bool wrong_chart = is(6, disposition::open) &&
      out[6].refusal_state == static_cast<std::uint8_t>(chi_state::chart_undeclared);
  const bool hand_residual = is(7, disposition::open);
  return production_rides && production_never_founds && body_founds && body_rides &&
      no_capability && undeclared && wrong_chart && hand_residual;
}

bool standing_shares_rather_than_copies(
    const std::array<spine_deed_output, spine_case_count>& out) {
  for (const auto& returned : out) {
    if (returned.population_before != 6 || returned.population_after != 6) {
      return false;
    }
    if (returned.path_copied == 0 || returned.path_copied >= returned.population_before) {
      return false;
    }
  }
  return true;
}

bool open_never_concludes(const std::array<spine_deed_output, spine_case_count>& out) {
  for (const auto& returned : out) {
    const bool open = returned.disposition == static_cast<std::uint8_t>(disposition::open);
    if (open && (returned.may_conclude || !returned.retains_pair)) {
      return false;
    }
  }
  return true;
}

}  // namespace holonics::tests

namespace holonics::tests {

bool carrier_laws_hold() {
  using namespace holonics::structure;
  // O: equal payloads remain two occurrences.
  const carried_occurrence<int> left{word{1}, {1}, {0}, {0}, {0}, 7};
  const carried_occurrence<int> right{word{2}, {1}, {0}, {0}, {0}, 7};
  const auto same = [](int l, int r) { return l == r; };
  if (occurrence_law::same_occurrence(left, right) ||
      !occurrence_law::plural_at_equal_payload(left, right, same)) {
    return false;
  }
  // I: opposed coefficients over the SAME face cancel; over equal-but-unglued faces they do not.
  const oriented_incidence a{word{9}, word{3}, incidence_sign::positive, 0};
  const oriented_incidence b{word{9}, word{3}, incidence_sign::negative, 1};
  const oriented_incidence c{word{9}, word{4}, incidence_sign::negative, 1};
  if (!incidence_law::cancels(a, b) || incidence_law::cancels(a, c) ||
      !incidence_law::distinct_basis(a, c)) {
    return false;
  }
  // D: a cycle at the declared cut is refused; dependency is not incidence.
  dependency_cut<8> cut{};
  if (!dependency_law::try_append(cut, directed_dependency{word{1}, word{2}}) ||
      !dependency_law::try_append(cut, directed_dependency{word{2}, word{3}})) {
    return false;
  }
  if (!dependency_law::acyclic_at_cut(cut)) { return false; }
  if (!dependency_law::try_append(cut, directed_dependency{word{3}, word{1}})) { return false; }
  if (dependency_law::acyclic_at_cut(cut)) { return false; }
  // T: composition inherits only jointly declared properties.
  transport_declaration invertible{};
  invertible = transport_law::declare(invertible, transport_property::invertible);
  const local_transport first{word{1}, word{10}, word{20}, invertible};
  const local_transport second{word{2}, word{20}, word{30}, {}};
  local_transport composite{};
  if (!transport_law::try_compose(first, second, word{3}, composite) ||
      transport_law::carries(composite.declaration, transport_property::invertible)) {
    return false;
  }
  // Chi: every projection refuses until its own chart is declared.
  const chi_pair pair{first, first};
  return chi_law::project(pair, chi_projection::residual).state == chi_state::chart_undeclared &&
      chi_law::project(pair, chi_projection::holonomy_defect).available() &&
      chi_law::project(pair, chi_projection::cross_ratio).state == chi_state::chart_undeclared;
}

bool substrate_laws_hold() {
  using namespace holonics::structure;
  sparse_ordinal_atlas<int, 64, 4> atlas{};
  const auto first = atlas.try_push(7);
  int departed = 0;
  if (!atlas.depart(first.ordinal, departed).accepted() || departed != 7) { return false; }
  const auto second = atlas.try_push(9);
  if (second.ordinal == first.ordinal) { return false; }          // ordinals never reused
  if (atlas.try_restore_horizon(0)) { return false; }             // horizon never retreats
  sparse_ordinal_atlas<int, 1, 1> tiny{};
  static_cast<void>(tiny.try_push(1));
  int recovered = 0;
  if (tiny.try_push_recover(42, recovered).accepted() || recovered != 42) { return false; }
  frozen_relation_atlas<int, int, 32, 4> frozen{};
  const relation<int, int> sorted[3] = {{1, 10}, {2, 20}, {5, 50}};
  const relation<int, int> unsorted[2] = {{9, 90}, {4, 40}};
  if (!frozen.try_append_state(sorted, 3) || frozen.try_append_state(unsorted, 2)) { return false; }
  const int* found = frozen.find(0, 5);
  if (found == nullptr || *found != 50) { return false; }
  branch_store<int, 16> branches{};
  const auto tip = branches.try_carry(no_ordinal, 1);
  const auto leftb = branches.try_carry(tip, 2);
  const auto rightb = branches.try_carry(tip, 3);
  return branches.common_prefix(leftb, rightb) == tip && branches.fork(tip).shares_prefix();
}

bool information_laws_hold() {
  using namespace holonics::current;
  // A wide equal-arrival population is carried exactly, not enumerated.
  holonics::receiver::receiver_current_law<300, 2200> law{};
  constexpr std::uint32_t width = 8;
  std::uint32_t layer[width]{};
  std::uint32_t next[width]{};
  for (std::uint32_t i = 0; i < width; ++i) { layer[i] = law.found_site(); }
  const std::uint32_t origin = layer[0];
  for (std::uint32_t d = 0; d < 30; ++d) {
    for (std::uint32_t i = 0; i < width; ++i) { next[i] = law.found_site(); }
    for (std::uint32_t a = 0; a < width; ++a) {
      for (std::uint32_t b = 0; b < width; ++b) {
        static_cast<void>(law.found_passage(layer[a], next[b]));
      }
    }
    for (std::uint32_t i = 0; i < width; ++i) { layer[i] = next[i]; }
  }
  const auto radiation = law.radiate_to_horizon(origin, 64);
  if (!radiation.returned() || law.at(layer[0]).population.used() < 2) { return false; }
  if (radiation.visited_passages > law.passages()) { return false; }
  // Minimal witness families: supersets refused, subsets evict.
  witness_atlas<8, 8> atlas{};
  witness_family<8> pair{};
  static_cast<void>(pair.members.try_insert(1));
  static_cast<void>(pair.members.try_insert(2));
  pair.closes = true;
  witness_family<8> superset = pair;
  static_cast<void>(superset.members.try_insert(3));
  witness_family<8> single{};
  static_cast<void>(single.members.try_insert(1));
  single.closes = true;
  if (!receipt_law::try_admit_minimal(atlas, pair) ||
      receipt_law::try_admit_minimal(atlas, superset) ||
      !receipt_law::try_admit_minimal(atlas, single) || atlas.used != 1) {
    return false;
  }
  if (!receipt_law::necessary(atlas, 1) || receipt_law::necessary(atlas, 2)) { return false; }
  atlas.selected = 0;
  // Restriction and base change are different events.
  causal_information_receipt<32, 8, 8> receipt{};
  for (std::uint64_t i = 1; i <= 5; ++i) {
    static_cast<void>(fiber_law::try_admit(receipt.before_contact, exact::word{i}, false));
  }
  for (std::uint64_t i = 1; i <= 3; ++i) {
    static_cast<void>(fiber_law::try_admit(receipt.after_world_return, exact::word{i}, false));
  }
  for (std::uint64_t i = 90; i <= 91; ++i) {
    static_cast<void>(fiber_law::try_admit(receipt.after_emanated_return, exact::word{i}, true));
  }
  receipt.witnesses = atlas;
  receipt.artifact_returned = true;
  receipt_law::classify_returns(receipt);
  if (receipt.world_return != return_mode::restriction ||
      receipt.answer_return != return_mode::base_change ||
      receipt.morphology != morphology_change::founded) {
    return false;
  }
  if (!receipt_law::complete(receipt)) { return false; }
  auto without_artifact = receipt;
  without_artifact.artifact_returned = false;
  if (receipt_law::complete(without_artifact)) { return false; }
  return fiber_law::sufficiency(3, 0) == return_mode::restriction &&
      fiber_law::sufficiency(3, 1) == return_mode::base_change;
}

}  // namespace holonics::tests

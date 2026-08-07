#include "ecology_cases.hpp"

#include <cstdint>

#include <holonics/codec/reflective_runtime.hpp>
#include <holonics/organ/source_incidence.hpp>
#include <holonics/organ/training_ecology.hpp>

namespace holonics::tests {
namespace {

using holonics::organ::no_state;
using holonics::organ::step_kind;
using holonics::organ::suffix_symbol;
using holonics::organ::symbol_kind;
using holonics::organ::transduction_fiber;

suffix_symbol germ_symbol(std::uint64_t word) {
  return suffix_symbol{symbol_kind::germ, word};
}

transduction_fiber two_step_fiber(std::uint64_t carried, std::uint64_t founded) {
  transduction_fiber fiber{};
  fiber.steps[0] = {step_kind::copy, carried};
  fiber.steps[1] = {step_kind::found, founded};
  fiber.used = 2;
  return fiber;
}

}  // namespace

bool suffix_laws_hold() {
  holonics::organ::suffix_automaton<512, 4096> automaton{};
  holonics::organ::source_incidence<512, 256> incidence{};
  const std::uint64_t first[4] = {1, 2, 3, 4};
  const std::uint64_t second[4] = {2, 3, 4, 5};
  const std::uint64_t third[4] = {1, 2, 3, 4};
  const std::uint64_t* paths[3] = {first, second, third};

  std::uint32_t symbols = 0;
  for (std::uint32_t source = 0; source < 3; ++source) {
    automaton.separate();
    for (std::uint32_t slot = 0; slot < 4; ++slot) {
      const std::uint32_t state = automaton.extend(germ_symbol(paths[source][slot]));
      if (state == no_state || !incidence.try_admit(state, source)) { return false; }
      symbols = symbols + 1U;
    }
    static_cast<void>(automaton.extend(
        suffix_symbol{symbol_kind::boundary, source}));
    symbols = symbols + 1U;
  }
  // At most two states are founded per symbol.
  if (automaton.states() > 2U * symbols + 1U) { return false; }
  if (!incidence.freeze(automaton)) { return false; }
  // Attribution is linear in states plus occurrences, never their product.
  if (incidence.linear_cost(automaton.states()) >= automaton.states() * 3U) { return false; }

  // Shared material retains every source that reached it.
  const suffix_symbol shared[3] = {germ_symbol(2), germ_symbol(3), germ_symbol(4)};
  std::uint32_t matched = 0;
  const std::uint32_t state = automaton.follow(shared, 3, matched);
  if (matched != 3 || !incidence.reaches(state, 0) || !incidence.reaches(state, 1)) {
    return false;
  }
  // A boundary prevents a material-only crossing between informant paths.
  const suffix_symbol crossing[2] = {germ_symbol(4), germ_symbol(1)};
  std::uint32_t crossed = 0;
  static_cast<void>(automaton.follow(crossing, 2, crossed));
  if (crossed == 2) { return false; }

  // Repeated testimony becomes multiplicity, not a second path.
  const suffix_symbol whole[4] = {germ_symbol(1), germ_symbol(2), germ_symbol(3),
      germ_symbol(4)};
  std::uint32_t whole_matched = 0;
  const std::uint32_t end = automaton.follow(whole, 4, whole_matched);
  if (whole_matched != 4 || automaton.at(end)->material_end_multiplicity < 2) {
    return false;
  }
  // Continuations are exposed whole, unranked.
  holonics::organ::suffix_transition exposed[16]{};
  return automaton.continuations(state, exposed, 16) != 0;
}

bool training_laws_hold() {
  using holonics::organ::training_state;
  // Asked for one; the owner refuses to be constructed below two.
  holonics::organ::training_ecology<64> ecology{1, 8};
  if (ecology.minimum_recurrence() != 2) { return false; }

  const transduction_fiber fiber = two_step_fiber(10, 20);
  const auto first = ecology.propose(&fiber, 1);
  if (ecology.commit(first) != training_state::admitted) { return false; }
  // One observation is testimony, not a route.
  if (ecology.conducts(fiber) || ecology.observed(fiber) != 1) { return false; }

  // A stale proposal refuses and leaves the ecology untouched.
  const auto second = ecology.propose(&fiber, 1);
  if (ecology.commit(first) != training_state::stale_generation) { return false; }
  if (ecology.commit(second) != training_state::admitted) { return false; }
  if (!ecology.conducts(fiber) || ecology.active() != 1) { return false; }

  // The template budget is a refusal boundary, never a ranking.
  transduction_fiber crowd[16]{};
  for (std::uint32_t slot = 0; slot < 16; ++slot) {
    crowd[slot] = two_step_fiber(slot, 1);
  }
  if (ecology.propose(crowd, 16).state != training_state::template_budget_refused) {
    return false;
  }

  // Ablation removes structure; the route stops conducting.
  return ecology.ablate(fiber) && !ecology.conducts(fiber) &&
      ecology.observed(fiber) == 0 && ecology.active() == 0;
}

bool reflective_laws_hold() {
  holonics::codec::reflective_runtime<32, 32> runtime{};
  const std::uint32_t parent = runtime.mount_codec(0xAA, 1);
  const std::uint32_t carried = runtime.open_continuation(parent, 0xEE);
  const std::uint32_t reflected = runtime.reflect(carried, 7);
  const std::uint32_t child = runtime.revise_and_resume(reflected, 0xBB);
  if (child == holonics::codec::no_codec) { return false; }
  // The SAME continuation resumed, under a parented child, environment intact.
  if (runtime.continuation(carried)->codec != child ||
      runtime.continuation(carried)->environment != 0xEE) { return false; }
  if (runtime.codec(child)->parent_count != 1 ||
      runtime.codec(child)->parents[0] != parent) { return false; }
  // The parent is retained and still readable.
  if (runtime.codec(parent)->program != 0xAA || !runtime.descends_from(child, parent)) {
    return false;
  }
  // A correction that changed nothing must not manufacture lineage.
  const std::uint32_t again = runtime.reflect(carried, 8);
  const std::uint32_t before = runtime.codecs();
  return runtime.resume_unchanged(again) && runtime.codecs() == before;
}

}  // namespace holonics::tests

#include <holonics/event/agentic_mouth.hpp>
#include <holonics/event/research_ecology.hpp>

namespace holonics::tests {

bool surface_laws_hold() {
  using namespace holonics::organ;
  token_transport carried{};
  carried.germ = 7;
  carried.matched_length[0] = 3;   // lexical
  carried.recurrence[0] = 2;
  carried.matched_length[1] = 5;   // clause-lexical, longer
  carried.recurrence[1] = 1;
  if (morphological_law::greatest_productive(carried) != 5) { return false; }
  if (morphological_law::supporting_count(carried) != 2) { return false; }
  // Absent morphology emits nothing rather than inventing a continuation.
  token_transport bare{};
  bare.germ = 7;
  if (morphological_law::carried(bare)) { return false; }
  surface_generation generation{};
  if (morphological_law::try_emit(generation, bare)) { return false; }
  if (!morphological_law::try_emit(generation, carried) || generation.token_count != 1) {
    return false;
  }
  // Same visible germ, different supporting scales, remains a different transport.
  token_transport other = carried;
  other.recurrence[1] = 0;
  if (morphological_law::same_transport(carried, other)) { return false; }
  // Observer exhaustion is not linguistic rest.
  if (morphological_law::close(0, true) != response_rest::observation_aperture_exhausted) {
    return false;
  }
  return morphological_law::close(0, false) == response_rest::closed &&
      morphological_law::close(2, false) == response_rest::obstructed;
}

bool relational_laws_hold() {
  using namespace holonics::event;
  relational_channel channel{};
  // One return is co-presence, not contact.
  if (relational_law::admit_return(channel, 99, 1) != channel_conduct::copresent) {
    return false;
  }
  // A repeat through the SAME source pair advances recurrence but does not close.
  if (relational_law::admit_return(channel, 99, 1) != channel_conduct::copresent ||
      channel.recurrence_population != 2) { return false; }
  // A second, distinct source pair closes it as caused.
  if (relational_law::admit_return(channel, 99, 2) != channel_conduct::caused) {
    return false;
  }
  // A changed junction phase reopens rather than accumulating.
  if (relational_law::admit_return(channel, 100, 3) != channel_conduct::open) {
    return false;
  }
  // Transport words are ordered and noncommuting.
  thought_current left{};
  thought_current right{};
  if (!relational_law::try_extend(left, 1, false) ||
      !relational_law::try_extend(left, 2, false) ||
      !relational_law::try_extend(right, 2, false) ||
      !relational_law::try_extend(right, 1, false)) { return false; }
  if (relational_law::same_word(left, right)) { return false; }
  // A closed route returning a changed frame carries holonomy.
  thought_current loop{};
  static_cast<void>(relational_law::try_extend(loop, 5, false));
  static_cast<void>(relational_law::try_extend(loop, 6, false));
  static_cast<void>(relational_law::try_extend(loop, 5, true));
  return relational_law::carries_holonomy(loop);
}

bool mouth_laws_hold() {
  using namespace holonics::event;
  // A question needing a world deed opens one and the turn awaits its return.
  const auto opened = mouth_law::respond(turn_state::rest, mouth_occurrence::question, true);
  if (opened != mouth_consequence::deed) { return false; }
  const turn_state awaiting = mouth_law::advance(turn_state::rest, opened);
  if (awaiting != turn_state::awaiting_world_return) { return false; }
  // A second question while awaiting cannot answer; it clarifies.
  if (mouth_law::respond(awaiting, mouth_occurrence::question, false) !=
      mouth_consequence::answer) {
    if (mouth_law::respond(awaiting, mouth_occurrence::question, false) !=
        mouth_consequence::clarification) { return false; }
  }
  // A world return is admissible only while one is awaited.
  if (mouth_law::respond(awaiting, mouth_occurrence::world_return, false) !=
      mouth_consequence::answer) { return false; }
  if (mouth_law::respond(turn_state::rest, mouth_occurrence::world_return, false) !=
      mouth_consequence::clarification) { return false; }
  // Retained ports make a crossing inadmissible.
  mouth_crossing crossing{};
  crossing.ports_retained = true;
  if (mouth_law::admissible(crossing)) { return false; }
  crossing.ports_retained = false;
  // A residual keeps its direction.
  return mouth_law::admissible(crossing) &&
      mouth_law::residual_directed(codec_residual{3, 1}) &&
      !mouth_law::residual_directed(codec_residual{2, 2});
}

bool formal_laws_hold() {
  using namespace holonics::event;
  // Mounting installs motions and zero mathematics.
  if (!formal_law::mount_clean(proof_motion_count, 0) ||
      formal_law::mount_clean(proof_motion_count, 1)) { return false; }
  checker_crossing crossing{};
  crossing.generated = 4;
  // An incomplete population cannot cultivate.
  if (!formal_law::try_admit_return(crossing,
          checker_return{0, checker_outcome::obstructed, proof_motion::direct, 10})) {
    return false;
  }
  if (formal_law::may_cultivate(crossing)) { return false; }
  static_cast<void>(formal_law::try_admit_return(crossing,
      checker_return{1, checker_outcome::obstructed, proof_motion::rewrite, 11}));
  static_cast<void>(formal_law::try_admit_return(crossing,
      checker_return{2, checker_outcome::obstructed, proof_motion::introduce_fact, 12}));
  if (formal_law::may_cultivate(crossing)) { return false; }
  static_cast<void>(formal_law::try_admit_return(crossing,
      checker_return{3, checker_outcome::accepted, proof_motion::contrapose, 13}));
  if (!formal_law::may_cultivate(crossing) || crossing.accepted != 1 ||
      crossing.obstructed != 3) { return false; }
  // Obstruction causes deeper motion: three obstructed paths license three pairs.
  if (formal_law::compositions_caused(crossing) != 3) { return false; }
  // Selection refuses rather than substituting a reachable target.
  return formal_law::select_target(true, true) == target_state::selected &&
      formal_law::select_target(false, true) == target_state::open &&
      formal_law::select_target(true, false) == target_state::open;
}

bool research_laws_hold() {
  using namespace holonics::event;
  contact_front front{};
  // A front crosses only as a validated whole.
  if (research_law::may_cross(front)) { return false; }
  if (!research_law::try_admit(front, research_leader{1, 100, 7, false, false}) ||
      !research_law::try_admit(front, research_leader{2, 100, 8, false, true})) {
    return false;
  }
  // A duplicate leader is refused.
  if (research_law::try_admit(front, research_leader{1, 100, 9, false, false})) {
    return false;
  }
  front.validated = true;
  if (!research_law::may_cross(front)) { return false; }
  // Only still-open currents that reached a face owe bridge leaders.
  if (research_law::bridge_leaders_owed(front) != 1) { return false; }
  // Rest is the absence of novel source and unvisited bridge, not a round count.
  if (research_law::rest_state(1, 0) != research_rest::novel_source_remains ||
      research_law::rest_state(0, 1) != research_rest::bridge_region_unvisited ||
      research_law::rest_state(0, 0) != research_rest::rested) { return false; }
  // Causal exclusion is by identity, so a rerun cannot inherit its own answer.
  const std::uint64_t excluded[1] = {42};
  return !research_law::source_admitted(42, excluded, 1) &&
      research_law::source_admitted(43, excluded, 1);
}

}  // namespace holonics::tests


namespace holonics::tests {

ablation_return cultivation_ablation() {
  // CUT 5, 2026-08-06. This returned 9*8=72 and 7*9=63 because C++ multiplies.
  // `product_route()` was nullary and constexpr -- one global constant fiber, so the
  // "two distinct developmental passages" were the same constant twice, and no operand
  // pair was ever supplied to the ecology by any path in the repository. The grade it
  // carried is withdrawn from CLAUDE.md section 5 in the same commit.
  return ablation_return{};

}

}  // namespace holonics::tests

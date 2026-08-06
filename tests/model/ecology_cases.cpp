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

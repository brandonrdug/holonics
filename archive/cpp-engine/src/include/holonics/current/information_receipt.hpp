#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/current/continuation_fiber.hpp>

namespace holonics::current {

/// A witness family: the set of informants that closes a demanded deed.
template<std::size_t Capacity>
struct witness_family final {
  static_assert(Capacity > 0);
  structure::local_set<std::uint64_t, Capacity> members{};
  bool closes{};
};

/// Every inclusion-minimal closed family, and which one was selected.
/// **Equal generated surfaces do not collapse distinct witness families**: two
/// families that produced the same text are still two families.
template<std::size_t FamilyCapacity, std::size_t MemberCapacity>
struct witness_atlas final {
  witness_family<MemberCapacity> families[FamilyCapacity]{};
  std::uint32_t used{};
  std::uint32_t selected{structure::no_ordinal};
};

/// Logical work. Traversal, bytes, computation, memory, communication, and
/// elapsed time remain separately attributable; none is derived from another.
///
/// `causal_span` is the layer count and `exposed_parallel_width` the widest
/// layer of one deterministic layering — the max-plus front in its implemented
/// form. It is **not** permission to infer energy from elapsed time.
struct logical_work final {
  std::uint64_t leaders{};
  std::uint64_t causal_waves{};
  std::uint64_t returned_sections{};
  std::uint64_t omitted_sections{};
  std::uint64_t candidate_visits{};
  std::uint64_t committed_passages{};
  std::uint64_t peak_front{};
  std::uint64_t causal_span{};
  std::uint64_t exposed_parallel_width{};
};

/// The complete causal-information receipt one serious deed owes.
///
/// The fiber is sampled at **three** times: before exterior contact, after the
/// world returns, and after the emanated answer itself returns as a caused
/// passage. A receipt with fewer than three is incomplete.
///
/// Obstruction is carried **complete**. There is no scalar confidence anywhere
/// in this structure, and physical telemetry lives in the experiment receipt
/// because it may vary between runs and **may not alter deterministic answer
/// equality**.
template<std::size_t FiberCapacity, std::size_t FamilyCapacity, std::size_t MemberCapacity>
struct causal_information_receipt final {
  continuation_fiber<FiberCapacity> before_contact{};
  continuation_fiber<FiberCapacity> after_world_return{};
  continuation_fiber<FiberCapacity> after_emanated_return{};
  witness_atlas<FamilyCapacity, MemberCapacity> witnesses{};
  logical_work work{};
  return_mode world_return{return_mode::unchanged};
  return_mode answer_return{return_mode::unchanged};
  morphology_change morphology{morphology_change::unchanged};
  exact::word obstruction{};
  bool artifact_returned{};
};

namespace receipt_law {

/// Admit a family only if it closes and is not a superset of one already
/// admitted; drop any admitted family that the newcomer is a subset of. What
/// remains is the inclusion-minimal set.
template<std::size_t FamilyCapacity, std::size_t MemberCapacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_admit_minimal(
    witness_atlas<FamilyCapacity, MemberCapacity>& atlas,
    const witness_family<MemberCapacity>& candidate) noexcept {
  if (!candidate.closes) {
    return false;
  }
  for (std::uint32_t slot = 0; slot < atlas.used; ++slot) {
    if (candidate.members.includes(atlas.families[slot].members)) {
      return false;
    }
  }
  std::uint32_t kept = 0;
  for (std::uint32_t slot = 0; slot < atlas.used; ++slot) {
    if (!atlas.families[slot].members.includes(candidate.members)) {
      atlas.families[kept] = atlas.families[slot];
      kept = kept + 1U;
    }
  }
  atlas.used = kept;
  if (atlas.used >= FamilyCapacity) {
    return false;
  }
  atlas.families[atlas.used] = candidate;
  atlas.used = atlas.used + 1U;
  return true;
}

/// Is an informant necessary for this deed? It is necessary when it occurs in
/// **every** minimal family, possible when it occurs in at least one, and
/// irrelevant to this deed when it occurs in none. No absolute semantic label is
/// required or produced.
template<std::size_t FamilyCapacity, std::size_t MemberCapacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool necessary(
    const witness_atlas<FamilyCapacity, MemberCapacity>& atlas,
    std::uint64_t informant) noexcept {
  if (atlas.used == 0) {
    return false;
  }
  for (std::uint32_t slot = 0; slot < atlas.used; ++slot) {
    if (!atlas.families[slot].members.contains(informant)) {
      return false;
    }
  }
  return true;
}

template<std::size_t FamilyCapacity, std::size_t MemberCapacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool possible(
    const witness_atlas<FamilyCapacity, MemberCapacity>& atlas,
    std::uint64_t informant) noexcept {
  for (std::uint32_t slot = 0; slot < atlas.used; ++slot) {
    if (atlas.families[slot].members.contains(informant)) {
      return true;
    }
  }
  return false;
}

/// A deed's receipt is complete only when all three fibers were sampled, a
/// minimal family was selected, the artifact itself came back, and any failure
/// to close is carried as a complete obstruction rather than omitted.
template<std::size_t FiberCapacity, std::size_t FamilyCapacity, std::size_t MemberCapacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool complete(
    const causal_information_receipt<FiberCapacity, FamilyCapacity, MemberCapacity>&
        receipt) noexcept {
  const bool sampled = receipt.before_contact.used != 0 &&
      receipt.after_world_return.used != 0 && receipt.after_emanated_return.used != 0;
  const bool witnessed = receipt.witnesses.used != 0 &&
      receipt.witnesses.selected < receipt.witnesses.used;
  const bool closed_or_obstructed = receipt.after_emanated_return.closed != 0 ||
      receipt.obstruction.value() != 0;
  return sampled && witnessed && receipt.artifact_returned && closed_or_obstructed;
}

/// Classify both returns and the morphology change from the three samples.
template<std::size_t FiberCapacity, std::size_t FamilyCapacity, std::size_t MemberCapacity>
HOLONICS_CALLABLE constexpr void classify_returns(
    causal_information_receipt<FiberCapacity, FamilyCapacity, MemberCapacity>&
        receipt) noexcept {
  receipt.world_return =
      fiber_law::classify(receipt.before_contact, receipt.after_world_return);
  receipt.answer_return =
      fiber_law::classify(receipt.after_world_return, receipt.after_emanated_return);
  if (receipt.world_return == return_mode::base_change ||
      receipt.answer_return == return_mode::base_change) {
    receipt.morphology = morphology_change::founded;
    return;
  }
  if (receipt.world_return == return_mode::restriction ||
      receipt.answer_return == return_mode::restriction) {
    receipt.morphology = morphology_change::extended;
    return;
  }
  receipt.morphology = morphology_change::unchanged;
}

}  // namespace receipt_law
}  // namespace holonics::current

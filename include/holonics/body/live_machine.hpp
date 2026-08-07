#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/body/standing_surface.hpp>
#include <holonics/body/swing.hpp>
#include <holonics/structure/causal_membrane.hpp>
#include <holonics/structure/local_population.hpp>

namespace holonics::body {

/// One live lineage: its own channel, its carried groove, and its tip in the
/// standing surface. A lineage is the live current's carried identity.
struct live_lineage final {
  exact::word channel{};
  exact::word groove{};
  exact::word winding{};
  std::uint32_t tip{structure::no_ordinal};
};

struct live_memory final {
  std::uint32_t standing_nodes{};
  std::uint32_t lineages{};
  std::uint32_t aperture_entries{};
  std::uint64_t standing_octets{};
};

/// The continuing body.
///
/// Owns one standing surface, the live lineages, and a **rebuildable incidence
/// aperture that is absent from rest, from radiation, and from identity**. The
/// aperture is a substrate cache: it may be discarded and rebuilt, and it may
/// never make a completed causal event appear refused.
///
/// **Not clonable.** There is no fork that duplicates a live body; plurality is
/// branches over shared immutable standing.
template<class Form, std::size_t StandingCapacity, std::size_t LineageCapacity>
class live_machine final {
 public:
  using holonics_membrane = structure::membrane_marker;
  using standing_type = standing_surface<Form, StandingCapacity>;

  HOLONICS_CALLABLE explicit live_machine(exact::word owner_seed) noexcept
      : head_(owner_seed), lineage_seed_(owner_seed.value() + 1'000'000U) {}
  live_machine(const live_machine&) = delete;
  live_machine& operator=(const live_machine&) = delete;
  live_machine(live_machine&&) = delete;
  live_machine& operator=(live_machine&&) = delete;

  [[nodiscard]] HOLONICS_CALLABLE constexpr const standing_type& standing() const noexcept {
    return standing_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr exact::word head() const noexcept {
    return head_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t root() const noexcept {
    return root_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t lineage_count() const noexcept {
    return lineages_used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const live_lineage* lineage(
      std::uint32_t slot) const noexcept {
    return slot < lineages_used_ ? &lineages_[slot] : nullptr;
  }

  /// Attach a lineage. Its channel is minted by this owner; it is never derived
  /// from an address, a lane, or an arrival number.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t attach() noexcept {
    if (lineages_used_ >= LineageCapacity) {
      return structure::no_ordinal;
    }
    lineages_[lineages_used_] = live_lineage{
        exact::word{lineage_seed_ + lineages_used_}, exact::word{}, exact::word{}, root_};
    const std::uint32_t minted = lineages_used_;
    lineages_used_ = lineages_used_ + 1U;
    return minted;
  }

  /// Receive one occurrence against a declared predecessor. The crossing commits
  /// only when the transition grade is complete **and** the staged predecessor
  /// is still the current head; otherwise the body is returned untouched.
  [[nodiscard]] HOLONICS_CALLABLE structure::membrane_crossing<swing_return> receive(
      std::uint32_t lineage_slot,
      const swing_input& input,
      structure::chi_projection projection,
      exact::word winding_quantum,
      exact::word staged_predecessor,
      const standing_cell<Form>& placed) noexcept {
    structure::membrane_crossing<swing_return> crossing{};
    crossing.predecessor = head_;
    if (lineage_slot >= lineages_used_ ||
        !structure::membrane_law::may_commit(staged_predecessor, head_)) {
      return crossing;
    }
    crossing.value = swing_law::cross(input, projection, winding_quantum);
    crossing.disposition = crossing.value.disposition;
    // The standing does the work first, because a grader that has not seen the
    // work cannot grade it. A refused grade leaves `root_` where it was, so the
    // minted nodes become unreferenced residue and no completed event is undone.
    const std::uint32_t population_before = standing_.used();
    std::uint32_t copied = 0;
    const std::uint32_t next_root = standing_.replace(root_, placed, copied);
    if (next_root == structure::no_ordinal) {
      crossing.grade.refused_at =
          static_cast<std::uint8_t>(structure::transition_invariant::bounded_emission);
      return crossing;
    }
    const exact::word head_after{head_.value() + 1U};
    crossing.grade = grade_transition(crossing.value, staged_predecessor, head_,
        head_, head_after, population_before, standing_.used(), copied, 1U, 1U,
        structure::causal_attribution::contacted);
    if (!crossing.grade.complete()) {
      return crossing;
    }
    root_ = next_root;
    aperture_entries_ = aperture_entries_ + copied;
    live_lineage& carried = lineages_[lineage_slot];
    carried.tip = root_;
    carried.groove = crossing.value.next_groove;
    if (swing_law::pays_curvature(crossing.value)) {
      carried.winding = exact::word{carried.winding.value() + winding_quantum.value()};
    }
    head_ = exact::word{head_.value() + 1U};
    crossing.successor = head_;
    return crossing;
  }

  /// Rest performs no event: waiting or remounting without new current leaves
  /// the head where it was.
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool rest_is_eventless(
      exact::word head_before) const noexcept {
    return structure::transition_law::rest_is_eventless(head_before, head_, false);
  }

  /// Discard the rebuildable aperture. Standing, lineages, and head are
  /// untouched, and no completed event becomes refused by doing this.
  HOLONICS_CALLABLE constexpr void discard_aperture() noexcept {
    aperture_entries_ = 0;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr live_memory memory() const noexcept {
    return live_memory{standing_.used(), lineages_used_, aperture_entries_,
        static_cast<std::uint64_t>(standing_.used()) * sizeof(typename standing_type::node)};
  }

 private:
  /// Grade one crossing against the states it actually passed through.
  ///
  /// Until 2026-08-06 this took only the return and admitted **seven of the
  /// eight** invariants with a literal `true`: the one move was certified by
  /// assignment. A grader that receives only a return cannot check a transition,
  /// so it now receives the prestate, the placement, and the work the standing
  /// did. Every bit below is computed, and every one can be false.
  [[nodiscard]] HOLONICS_CALLABLE static constexpr structure::transition_grade
  grade_transition(
      const swing_return& returned,
      exact::word declared_predecessor,
      exact::word met_predecessor,
      exact::word head_before,
      exact::word head_after,
      std::uint32_t population_before,
      std::uint32_t population_after,
      std::uint32_t copied,
      std::uint32_t placements,
      std::uint32_t advanced_lineages,
      structure::causal_attribution attribution) noexcept {
    using structure::transition_invariant;
    namespace law = structure::transition_law;
    structure::transition_grade grade{};
    const bool concluded = returned.disposition.concluded();
    const bool founded =
        returned.disposition.state == structure::disposition::found;
    const exact::word met[1]{met_predecessor};
    grade = law::admit(grade, transition_invariant::same_prestate_atomicity,
        law::same_prestate(declared_predecessor, met, 1));
    // No false incidence: the successor grew by exactly the cells the
    // replacement minted along the touched path, and by nothing else.
    grade = law::admit(grade, transition_invariant::no_false_incidence,
        population_after >= population_before &&
            population_after - population_before <= copied + placements);
    // The population must grow by exactly what the replacement minted. Passing
    // the observed difference as the caused count would make this tautological,
    // which is how a predicate becomes a constant without looking like one.
    grade = law::admit(grade, transition_invariant::occurrence_preservation,
        law::occurrences_preserved(population_before, copied + placements,
            population_after));
    grade = law::admit(grade, transition_invariant::oriented_boundary_validity,
        law::boundary_parallel(returned.retained.composed, returned.retained.direct));
    grade = law::admit(grade, transition_invariant::causal_attribution,
        law::attribution_matches(attribution, founded, concluded));
    grade = law::admit(grade, transition_invariant::one_visibility_edge,
        law::single_visibility_edge(placements, advanced_lineages));
    grade = law::admit(grade, transition_invariant::rest_performs_no_event,
        law::rest_is_eventless(head_before, head_after, concluded));
    grade = law::admit(grade, transition_invariant::bounded_emission,
        law::emission_bounded(placements, population_before + copied));
    return grade;
  }

  standing_type standing_{};
  live_lineage lineages_[LineageCapacity]{};
  exact::word head_{};
  std::uint64_t lineage_seed_{};
  std::uint32_t root_{structure::no_ordinal};
  std::uint32_t lineages_used_{};
  std::uint32_t aperture_entries_{};
};

}  // namespace holonics::body

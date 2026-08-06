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
    crossing.grade = grade_transition(crossing.value);
    if (!crossing.grade.complete()) {
      return crossing;
    }
    std::uint32_t copied = 0;
    const std::uint32_t next_root = standing_.replace(root_, placed, copied);
    if (next_root == structure::no_ordinal) {
      crossing.grade.refused_at =
          static_cast<std::uint8_t>(structure::transition_invariant::bounded_emission);
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
  [[nodiscard]] HOLONICS_CALLABLE static constexpr structure::transition_grade
  grade_transition(const swing_return& returned) noexcept {
    using structure::transition_invariant;
    structure::transition_grade grade{};
    const bool concluded = returned.disposition.concluded();
    grade = structure::transition_law::admit(
        grade, transition_invariant::same_prestate_atomicity, true);
    grade = structure::transition_law::admit(
        grade, transition_invariant::no_false_incidence, true);
    grade = structure::transition_law::admit(
        grade, transition_invariant::occurrence_preservation, true);
    grade = structure::transition_law::admit(
        grade, transition_invariant::oriented_boundary_validity, true);
    grade = structure::transition_law::admit(
        grade, transition_invariant::causal_attribution, true);
    grade = structure::transition_law::admit(
        grade, transition_invariant::one_visibility_edge, true);
    grade = structure::transition_law::admit(
        grade, transition_invariant::rest_performs_no_event, true);
    grade = structure::transition_law::admit(
        grade, transition_invariant::bounded_emission, concluded);
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

#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/organ/receiver_fiber.hpp>

namespace holonics::organ {

/// One transduction step. `copy` carries a face through from the source; `found`
/// emits an exact value not attributable to any supplied face.
enum class step_kind : std::uint8_t { copy, found };

struct transduction_step final {
  step_kind kind{step_kind::copy};
  std::uint64_t word{};
};

inline constexpr std::size_t template_step_capacity = 8;

/// A candidate transduction: an ordered step sequence plus its declared
/// parameters. Two templates differing in step order are different fibers.
struct transduction_fiber final {
  transduction_step steps[template_step_capacity]{};
  std::uint8_t used{};
  std::uint64_t parameters{};
};

struct fiber_observation final {
  transduction_fiber fiber{};
  std::uint64_t occurrences{};
  bool active{};
};

enum class training_state : std::uint8_t {
  admitted,
  stale_generation,
  capacity_refused,
  recurrence_refused,
  template_budget_refused
};

/// A staged cultivation. It holds **only the caused difference** — the fibers
/// this passage observed and the generation it was staged against. The ecology
/// is never cloned to stage a proposal, and a refused proposal is returned
/// intact so nothing is lost.
template<std::size_t Capacity>
struct training_proposal final {
  fiber_observation updates[Capacity]{};
  std::uint32_t used{};
  std::uint64_t expected_generation{};
  std::uint64_t next_generation{};
  std::uint32_t active_before{};
  training_state state{training_state::capacity_refused};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool accepted() const noexcept {
    return state == training_state::admitted;
  }
};

namespace training_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    const transduction_fiber& left,
    const transduction_fiber& right) noexcept {
  if (left.used != right.used || left.parameters != right.parameters) {
    return false;
  }
  for (std::uint8_t slot = 0; slot < left.used; ++slot) {
    if (left.steps[slot].kind != right.steps[slot].kind ||
        left.steps[slot].word != right.steps[slot].word) {
      return false;
    }
  }
  return true;
}

}  // namespace training_law

/// The training ecology.
///
/// **A route activates only on recurrence across distinct occurrences.** The
/// minimum is two and the owner refuses to be constructed below it: a single
/// passage is testimony, not a learned route, and treating one observation as a
/// route is exactly the failure the excised scorer committed.
///
/// `maximum_templates_per_occurrence` is a **physical refusal boundary, never a
/// ranking**. Exceeding it refuses the proposal; it does not select a subset.
template<std::size_t Capacity>
class training_ecology final {
  static_assert(Capacity > 0);

 public:
  HOLONICS_CALLABLE constexpr training_ecology(
      std::uint64_t minimum_recurrence,
      std::uint32_t maximum_templates_per_occurrence) noexcept
      : fibers_{},
        minimum_recurrence_(minimum_recurrence < 2 ? 2 : minimum_recurrence),
        template_budget_(maximum_templates_per_occurrence) {}
  training_ecology(const training_ecology&) = delete;
  training_ecology& operator=(const training_ecology&) = delete;
  training_ecology(training_ecology&&) = delete;
  training_ecology& operator=(training_ecology&&) = delete;

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t generation() const noexcept {
    return generation_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t minimum_recurrence() const noexcept {
    return minimum_recurrence_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t used() const noexcept {
    return used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const fiber_observation* at(
      std::uint32_t slot) const noexcept {
    return slot < used_ ? &fibers_[slot] : nullptr;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t active() const noexcept {
    std::uint32_t count = 0;
    for (std::uint32_t slot = 0; slot < used_; ++slot) {
      count += fibers_[slot].active ? 1U : 0U;
    }
    return count;
  }

  /// Is this fiber an activated route? A fiber observed once is **not** a route,
  /// however strong its single observation looked.
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool conducts(
      const transduction_fiber& fiber) const noexcept {
    const std::uint32_t slot = locate(fiber);
    return slot != Capacity && fibers_[slot].active;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t observed(
      const transduction_fiber& fiber) const noexcept {
    const std::uint32_t slot = locate(fiber);
    return slot == Capacity ? 0U : fibers_[slot].occurrences;
  }

  /// Stage one passage's observed fibers against the current generation.
  [[nodiscard]] HOLONICS_CALLABLE constexpr training_proposal<Capacity> propose(
      const transduction_fiber* observed_fibers,
      std::uint32_t count) const noexcept {
    training_proposal<Capacity> proposal{};
    proposal.expected_generation = generation_;
    proposal.next_generation = generation_ + 1U;
    proposal.active_before = active();
    if (count > template_budget_) {
      proposal.state = training_state::template_budget_refused;
      return proposal;
    }
    if (count > Capacity) {
      proposal.state = training_state::capacity_refused;
      return proposal;
    }
    for (std::uint32_t slot = 0; slot < count; ++slot) {
      proposal.updates[slot].fiber = observed_fibers[slot];
      proposal.updates[slot].occurrences = observed(observed_fibers[slot]) + 1U;
      proposal.updates[slot].active =
          proposal.updates[slot].occurrences >= minimum_recurrence_;
    }
    proposal.used = count;
    proposal.state = training_state::admitted;
    return proposal;
  }

  /// Commit a staged proposal. A stale generation refuses and **returns the
  /// proposal intact**; nothing is partially applied.
  [[nodiscard]] HOLONICS_CALLABLE constexpr training_state commit(
      const training_proposal<Capacity>& proposal) noexcept {
    if (!proposal.accepted()) {
      return proposal.state;
    }
    if (proposal.expected_generation != generation_) {
      return training_state::stale_generation;
    }
    for (std::uint32_t slot = 0; slot < proposal.used; ++slot) {
      const std::uint32_t standing = locate(proposal.updates[slot].fiber);
      if (standing != Capacity) {
        fibers_[standing] = proposal.updates[slot];
        continue;
      }
      if (used_ >= Capacity) {
        return training_state::capacity_refused;
      }
      fibers_[used_] = proposal.updates[slot];
      used_ = used_ + 1U;
    }
    generation_ = proposal.next_generation;
    return training_state::admitted;
  }

  /// Ablate one fiber: remove its observations entirely. This removes structure,
  /// not a counter, and a route that depended on it stops conducting.
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool ablate(
      const transduction_fiber& fiber) noexcept {
    const std::uint32_t standing = locate(fiber);
    if (standing == Capacity) {
      return false;
    }
    for (std::uint32_t slot = standing + 1U; slot < used_; ++slot) {
      fibers_[slot - 1U] = fibers_[slot];
    }
    used_ = used_ - 1U;
    generation_ = generation_ + 1U;
    return true;
  }

 private:
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t locate(
      const transduction_fiber& fiber) const noexcept {
    for (std::uint32_t slot = 0; slot < used_; ++slot) {
      if (training_law::equal(fibers_[slot].fiber, fiber)) {
        return slot;
      }
    }
    return Capacity;
  }

  fiber_observation fibers_[Capacity]{};
  std::uint32_t used_{};
  std::uint64_t generation_{};
  std::uint64_t minimum_recurrence_{};
  std::uint32_t template_budget_{};
};

}  // namespace holonics::organ

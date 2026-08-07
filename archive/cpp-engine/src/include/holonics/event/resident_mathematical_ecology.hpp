#pragma once

#include <cstddef>
#include <cstdint>
#include <type_traits>

#include <holonics/body/continuing_body.hpp>
#include <holonics/organ/mathematical_law.hpp>
#include <holonics/receiver/mathematical_question.hpp>

namespace holonics::event {

class resident_mathematical_ecology final {
 public:
  resident_mathematical_ecology() = delete;
  resident_mathematical_ecology(const resident_mathematical_ecology&) = delete;
  resident_mathematical_ecology& operator=(const resident_mathematical_ecology&) = delete;
  resident_mathematical_ecology(resident_mathematical_ecology&&) = delete;
  resident_mathematical_ecology& operator=(resident_mathematical_ecology&&) = delete;

  HOLONICS_CALLABLE resident_mathematical_ecology(
      const organ::mathematical_foundation& foundation,
      std::uint64_t body_seed,
      const body::rest_region* regions,
      bool source_detached) noexcept
      : foundation_(foundation), body_(body_seed, regions), source_detached_(source_detached),
        obstruction_(organ::valid_mathematical_foundation(foundation)
            ? organ::mathematical_obstruction::none
            : organ::mathematical_obstruction::invalid_foundation) {}

  [[nodiscard]] HOLONICS_CALLABLE organ::mathematical_obstruction obstruction() const noexcept {
    return obstruction_;
  }
  [[nodiscard]] HOLONICS_CALLABLE exact::word head() const noexcept { return body_.head(); }
  [[nodiscard]] HOLONICS_CALLABLE bool can_continue() const noexcept { return body_.can_open(); }
  [[nodiscard]] HOLONICS_CALLABLE const organ::mathematical_foundation& foundation() const noexcept {
    return foundation_;
  }
  [[nodiscard]] HOLONICS_CALLABLE organ::mathematical_neighborhood_receipt reconstruct(
      const receiver::mathematical_question& question) const noexcept {
    if (obstruction_ != organ::mathematical_obstruction::none) {
      return {};
    }
    const organ::mathematical_goal goal{question.identity, question.receiver,
        question.anchor_slot, question.target_type, question.hypothesis_type,
        question.metavariable, question.request_generated_closure};
    return organ::reconstruct_mathematical_neighborhood(
        foundation_, body_.head(), goal, source_detached_);
  }

 private:
  organ::mathematical_foundation foundation_{};
  body::continuing_body body_;
  bool source_detached_{};
  organ::mathematical_obstruction obstruction_{organ::mathematical_obstruction::invalid_foundation};
};

static_assert(std::is_trivially_destructible_v<resident_mathematical_ecology>);

}  // namespace holonics::event

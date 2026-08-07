#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/organ/training_ecology.hpp>

namespace holonics::event {

/// The five inherited proof motions. Mounting installs these and **zero
/// mathematics**; every declaration the body later owns arrives through training
/// and is retained as changed morphology, never as a retained source face.
enum class proof_motion : std::uint8_t {
  close,
  direct,
  rewrite,
  introduce_fact,
  recur_apply,
  contrapose
};

inline constexpr std::size_t proof_motion_count = 6;

/// What an exterior checker returned for one generated passage.
enum class checker_outcome : std::uint8_t { accepted, obstructed, unreturned };

struct checker_return final {
  std::uint32_t candidate{};
  checker_outcome outcome{checker_outcome::unreturned};
  proof_motion motion{proof_motion::close};
  std::uint64_t declaration{};
};

/// A crossing to the exterior checker.
///
/// **An incomplete population cannot cultivate.** Until every generated
/// candidate has returned, the crossing is open and nothing it carries may
/// change standing — a partial family would let an unreturned candidate's
/// absence read as a refusal.
struct checker_crossing final {
  checker_return returns[64]{};
  std::uint32_t generated{};
  std::uint32_t returned_count{};
  std::uint32_t accepted{};
  std::uint32_t obstructed{};
};

/// Target selection returns a receipt or stands open. **There is no substitute
/// target and no partial-score selection**: a body that cannot reach a target
/// says so.
enum class target_state : std::uint8_t { selected, open };

namespace formal_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_admit_return(
    checker_crossing& crossing,
    const checker_return& returned) noexcept {
  if (crossing.returned_count >= 64 || returned.outcome == checker_outcome::unreturned) {
    return false;
  }
  crossing.returns[crossing.returned_count] = returned;
  crossing.returned_count = crossing.returned_count + 1U;
  if (returned.outcome == checker_outcome::accepted) {
    crossing.accepted = crossing.accepted + 1U;
  } else {
    crossing.obstructed = crossing.obstructed + 1U;
  }
  return true;
}

/// Complete exactly when every generated candidate returned.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool complete(
    const checker_crossing& crossing) noexcept {
  return crossing.generated != 0 && crossing.returned_count == crossing.generated;
}

/// May this crossing cultivate the body?
[[nodiscard]] HOLONICS_CALLABLE constexpr bool may_cultivate(
    const checker_crossing& crossing) noexcept {
  return complete(crossing);
}

/// **Obstruction causes deeper motion.** An obstructed one-organ path is
/// retained and licenses composition; discarding it would throw away the only
/// evidence that the single organ was insufficient.
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t compositions_caused(
    const checker_crossing& crossing) noexcept {
  if (!complete(crossing) || crossing.obstructed < 2) {
    return 0;
  }
  return crossing.obstructed * (crossing.obstructed - 1U) / 2U;
}

/// Selection refuses rather than falling back.
[[nodiscard]] HOLONICS_CALLABLE constexpr target_state select_target(
    bool reached,
    bool source_absent) noexcept {
  return reached && source_absent ? target_state::selected : target_state::open;
}

/// Mounting installs motions and nothing else. A mount that retained a source
/// face has already contaminated the body it was meant to prepare.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool mount_clean(
    std::uint32_t motions_installed,
    std::uint32_t retained_source_faces) noexcept {
  return motions_installed == proof_motion_count && retained_source_faces == 0;
}

}  // namespace formal_law
}  // namespace holonics::event

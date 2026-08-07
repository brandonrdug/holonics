#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::body {
inline constexpr std::uint32_t no_deposit = 0xFFFF'FFFFU;

/// One returned organ, standing in the body.
///
/// `caused_by` names the organ whose return made this one reachable, by
/// **identity rather than by ordinal**, so that removing a predecessor cannot be
/// undone by the population shifting underneath it.
struct returned_organ final {
  exact::word identity{};
  exact::word caused_by{};
  std::uint32_t word_start{};
  std::uint32_t word_count{};
};

/// The standing a mathematical return deposits into.
///
/// **This is the join the body did not have.** A mathematical deed added to a
/// per-region counter and did nothing else, so its return could condition no
/// later conduct: a count cannot be reached, composed, or ablated. Here a return
/// deposits its exact words under an identity, a later current **reaches** them,
/// and excluding the deposit removes the reach by removing structure. The
/// counter itself was excised on 2026-08-07.
///
/// Exclusion cascades along `caused_by`. An organ that was only reachable
/// because an earlier return stood falls with it, which is what makes the
/// ablation structural rather than a mark on one entry.
template<std::size_t OrganCapacity, std::size_t WordCapacity>
class returned_standing final {
  static_assert(OrganCapacity > 0 && WordCapacity > 0);

 public:
  HOLONICS_CALLABLE constexpr returned_standing() noexcept : organs_{}, words_{} {}
  returned_standing(const returned_standing&) = delete;
  returned_standing& operator=(const returned_standing&) = delete;
  returned_standing(returned_standing&&) = delete;
  returned_standing& operator=(returned_standing&&) = delete;

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t standing() const noexcept {
    return organs_used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t deposits() const noexcept {
    return deposits_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t exclusions() const noexcept {
    return exclusions_;
  }
  /// The standing's own revision. It advances on every founding and every
  /// departure and on nothing else, so a resident chart may use it as a **cache
  /// hint and never as the answer** — an exact logical comparison always wins.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t revision() const noexcept {
    return revision_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t words_used() const noexcept {
    return words_used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t word_slot(
      std::uint32_t slot) const noexcept {
    return slot < words_used_ ? words_[slot] : 0;
  }
  /// Found one organ directly from a rested image. Used only by the rest law.
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool try_restore(
      const returned_organ& organ,
      const std::uint64_t* words,
      std::uint32_t count) noexcept {
    if (organs_used_ >= OrganCapacity || words_used_ + count > WordCapacity) {
      return false;
    }
    for (std::uint32_t slot = 0; slot < count; ++slot) {
      words_[words_used_ + slot] = words[slot];
    }
    organs_[organs_used_] = returned_organ{organ.identity, organ.caused_by,
        words_used_, count};
    words_used_ = words_used_ + count;
    organs_used_ = organs_used_ + 1U;
    revision_ = revision_ + 1U;
    return true;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const returned_organ* at(
      std::uint32_t slot) const noexcept {
    return slot < organs_used_ ? &organs_[slot] : nullptr;
  }

  /// Deposit one return. A repeated identity refuses: a return is founded once
  /// and later current rides it, so re-depositing would be founding what
  /// already stands.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t deposit(
      exact::word identity,
      const std::uint64_t* words,
      std::uint32_t count,
      exact::word caused_by) noexcept {
    if (identity.value() == 0 || words == nullptr || count == 0 ||
        organs_used_ >= OrganCapacity || words_used_ + count > WordCapacity ||
        reach(identity) != nullptr) {
      return no_deposit;
    }
    if (caused_by.value() != 0 && reach(caused_by) == nullptr) {
      return no_deposit;
    }
    for (std::uint32_t slot = 0; slot < count; ++slot) {
      words_[words_used_ + slot] = words[slot];
    }
    organs_[organs_used_] = returned_organ{identity, caused_by, words_used_, count};
    words_used_ = words_used_ + count;
    const std::uint32_t minted = organs_used_;
    organs_used_ = organs_used_ + 1U;
    deposits_ = deposits_ + 1U;
    revision_ = revision_ + 1U;
    return minted;
  }

  /// Does this identity stand? A later current reaches its return through this
  /// and through nothing else.
  [[nodiscard]] HOLONICS_CALLABLE constexpr const returned_organ* reach(
      exact::word identity) const noexcept {
    for (std::uint32_t slot = 0; slot < organs_used_; ++slot) {
      if (organs_[slot].identity == identity) {
        return &organs_[slot];
      }
    }
    return nullptr;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t word_at(
      const returned_organ& organ,
      std::uint32_t slot) const noexcept {
    return slot < organ.word_count ? words_[organ.word_start + slot] : 0;
  }

  /// Remove one return and everything that stood only because of it.
  ///
  /// The entry leaves the population; it is not marked. Its words become
  /// unreachable residue in the arena, since nothing addresses them once the
  /// organ is gone. Returns how many organs fell, cascade included.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t exclude(
      exact::word identity) noexcept {
    std::uint32_t fallen = 0;
    for (std::uint32_t pass = 0; pass <= OrganCapacity; ++pass) {
      const std::uint32_t found = locate(identity);
      if (found == OrganCapacity) {
        break;
      }
      exact::word orphaned[OrganCapacity]{};
      std::uint32_t orphan_count = 0;
      for (std::uint32_t slot = 0; slot < organs_used_; ++slot) {
        if (organs_[slot].caused_by == identity && orphan_count < OrganCapacity) {
          orphaned[orphan_count] = organs_[slot].identity;
          orphan_count = orphan_count + 1U;
        }
      }
      for (std::uint32_t slot = found + 1U; slot < organs_used_; ++slot) {
        organs_[slot - 1U] = organs_[slot];
      }
      organs_used_ = organs_used_ - 1U;
      exclusions_ = exclusions_ + 1U;
      revision_ = revision_ + 1U;
      fallen = fallen + 1U;
      for (std::uint32_t slot = 0; slot < orphan_count; ++slot) {
        fallen = fallen + exclude(orphaned[slot]);
      }
      break;
    }
    return fallen;
  }

 private:
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t locate(
      exact::word identity) const noexcept {
    for (std::uint32_t slot = 0; slot < organs_used_; ++slot) {
      if (organs_[slot].identity == identity) {
        return slot;
      }
    }
    return OrganCapacity;
  }

  returned_organ organs_[OrganCapacity]{};
  std::uint64_t words_[WordCapacity]{};
  std::uint32_t organs_used_{};
  std::uint32_t words_used_{};
  std::uint64_t deposits_{};
  std::uint64_t exclusions_{};
  std::uint64_t revision_{};
};

}  // namespace holonics::body

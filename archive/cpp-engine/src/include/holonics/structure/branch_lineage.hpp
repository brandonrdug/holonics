#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/relation_atlas.hpp>

namespace holonics::structure {

/// Proof that a fork shares its prefix rather than copying it.
struct branch_fork_receipt final {
  std::uint32_t shared_events{};
  std::uint32_t parent_extent{};
  std::uint32_t child_extent{};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool shares_prefix() const noexcept {
    return shared_events == parent_extent && child_extent == parent_extent;
  }
};

/// A branch lineage over a shared immutable event store.
///
/// **Not clonable, and forking is the only plurality constructor.** Plural
/// conduct uses branches over shared immutable structure; it never duplicates a
/// live body. A handle that carries an event is consumed by doing so, so no two
/// handles can extend the same tip.
template<class Event, std::size_t Capacity>
class branch_store final {
  static_assert(Capacity > 0);

 public:
  struct node final {
    Event event{};
    std::uint32_t prior{no_ordinal};
    std::uint32_t extent{};
  };

  HOLONICS_CALLABLE constexpr branch_store() noexcept : nodes_{} {}
  branch_store(const branch_store&) = delete;
  branch_store& operator=(const branch_store&) = delete;
  branch_store(branch_store&&) = delete;
  branch_store& operator=(branch_store&&) = delete;

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t used() const noexcept {
    return used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const node* at(
      std::uint32_t tip) const noexcept {
    return tip < used_ ? &nodes_[tip] : nullptr;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t extent_of(
      std::uint32_t tip) const noexcept {
    return tip < used_ ? nodes_[tip].extent : 0U;
  }

  /// Extend a tip. Returns the new tip, or `no_ordinal` on refusal with the
  /// store unchanged.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t try_carry(
      std::uint32_t tip,
      const Event& event) noexcept {
    if (used_ >= Capacity) {
      return no_ordinal;
    }
    const std::uint32_t prior_extent = tip == no_ordinal ? 0U : extent_of(tip);
    nodes_[used_] = node{event, tip, prior_extent + 1U};
    const std::uint32_t minted = used_;
    used_ = used_ + 1U;
    return minted;
  }

  /// Fork: both branches continue from the same tip, sharing every prior event.
  /// Nothing is copied and the receipt says so.
  [[nodiscard]] HOLONICS_CALLABLE constexpr branch_fork_receipt fork(
      std::uint32_t tip) const noexcept {
    const std::uint32_t extent = tip == no_ordinal ? 0U : extent_of(tip);
    return branch_fork_receipt{extent, extent, extent};
  }

  /// Is `candidate` an ancestor of `tip`? Bounded by the store, so a malformed
  /// chain terminates.
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool descends_from(
      std::uint32_t tip,
      std::uint32_t candidate) const noexcept {
    std::uint32_t walk = tip;
    for (std::uint32_t step = 0; step <= used_; ++step) {
      if (walk == candidate) {
        return true;
      }
      if (walk == no_ordinal || walk >= used_) {
        return false;
      }
      walk = nodes_[walk].prior;
    }
    return false;
  }

  /// The nearest shared ancestor of two tips: the retained prefix two branches
  /// hold in common.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t common_prefix(
      std::uint32_t left,
      std::uint32_t right) const noexcept {
    std::uint32_t walk = left;
    for (std::uint32_t step = 0; step <= used_; ++step) {
      if (walk == no_ordinal) {
        return no_ordinal;
      }
      if (descends_from(right, walk)) {
        return walk;
      }
      if (walk >= used_) {
        return no_ordinal;
      }
      walk = nodes_[walk].prior;
    }
    return no_ordinal;
  }

 private:
  node nodes_[Capacity]{};
  std::uint32_t used_{};
};

}  // namespace holonics::structure

#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/sparse_ordinal_atlas.hpp>

namespace holonics::body {

/// A chart-local address. Standing is keyed by the receiver's own address, never
/// by a global position, a byte offset, or an arrival number.
struct chart_address final {
  std::uint64_t chart{};
  std::uint64_t grip{};

  friend HOLONICS_CALLABLE constexpr bool operator==(
      chart_address, chart_address) noexcept = default;
};

[[nodiscard]] HOLONICS_CALLABLE constexpr bool precedes(
    chart_address left,
    chart_address right) noexcept {
  return left.chart != right.chart ? left.chart < right.chart : left.grip < right.grip;
}

/// One standing cell: its address and the regional form standing there.
template<class Form>
struct standing_cell final {
  chart_address address{};
  Form form{};
};

/// **Persistent standing over shared immutable structure.**
///
/// A cellular replacement copies only the touched root-to-leaf path and shares
/// every untouched body. Branches therefore hold shared immutable standing and
/// own only their local differences; nothing here duplicates a live surface, and
/// there is no clone by which it could.
///
/// **Standing contains no absolute clock.** Receiver chronology validates and
/// orients an occurrence upstream and departs before the cell is placed.
template<class Form, std::size_t Capacity>
class standing_surface final {
  static_assert(Capacity > 0);

 public:
  struct node final {
    standing_cell<Form> cell{};
    std::uint32_t lower{structure::no_ordinal};
    std::uint32_t higher{structure::no_ordinal};
  };

  HOLONICS_CALLABLE constexpr standing_surface() noexcept : nodes_{} {}
  standing_surface(const standing_surface&) = delete;
  standing_surface& operator=(const standing_surface&) = delete;
  standing_surface(standing_surface&&) = delete;
  standing_surface& operator=(standing_surface&&) = delete;

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t used() const noexcept {
    return used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const node* at(
      std::uint32_t ordinal) const noexcept {
    return ordinal < used_ ? &nodes_[ordinal] : nullptr;
  }

  /// The form standing at an address in the surface rooted at `root`.
  [[nodiscard]] HOLONICS_CALLABLE constexpr const Form* form_at(
      std::uint32_t root,
      chart_address address) const noexcept {
    std::uint32_t walk = root;
    for (std::uint32_t step = 0; step <= used_; ++step) {
      if (walk >= used_) {
        return nullptr;
      }
      if (nodes_[walk].cell.address == address) {
        return &nodes_[walk].cell.form;
      }
      walk = precedes(address, nodes_[walk].cell.address) ? nodes_[walk].lower
                                                          : nodes_[walk].higher;
    }
    return nullptr;
  }

  /// Place or replace one cell, returning the root of the successor surface.
  /// Only the path from the root to the changed cell is copied; every other
  /// subtree is shared with the predecessor by ordinal.
  ///
  /// Returns `no_ordinal` on capacity refusal, leaving the predecessor intact.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t replace(
      std::uint32_t root,
      const standing_cell<Form>& cell,
      std::uint32_t& copied) noexcept {
    copied = 0;
    return replace_from(root, cell, copied, 0);
  }

  /// How many cells stand in the surface rooted here.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t population(
      std::uint32_t root) const noexcept {
    if (root >= used_) {
      return 0;
    }
    return 1U + population(nodes_[root].lower) + population(nodes_[root].higher);
  }

 private:
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t mint(
      const standing_cell<Form>& cell,
      std::uint32_t lower,
      std::uint32_t higher) noexcept {
    if (used_ >= Capacity) {
      return structure::no_ordinal;
    }
    nodes_[used_] = node{cell, lower, higher};
    const std::uint32_t minted = used_;
    used_ = used_ + 1U;
    return minted;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t replace_from(
      std::uint32_t root,
      const standing_cell<Form>& cell,
      std::uint32_t& copied,
      std::uint32_t depth) noexcept {
    if (depth > Capacity) {
      return structure::no_ordinal;
    }
    if (root >= used_) {
      const std::uint32_t minted = mint(cell, structure::no_ordinal, structure::no_ordinal);
      copied = minted == structure::no_ordinal ? copied : copied + 1U;
      return minted;
    }
    const node existing = nodes_[root];
    if (existing.cell.address == cell.address) {
      const std::uint32_t minted = mint(cell, existing.lower, existing.higher);
      copied = minted == structure::no_ordinal ? copied : copied + 1U;
      return minted;
    }
    if (precedes(cell.address, existing.cell.address)) {
      const std::uint32_t lower = replace_from(existing.lower, cell, copied, depth + 1U);
      if (lower == structure::no_ordinal) {
        return structure::no_ordinal;
      }
      const std::uint32_t minted = mint(existing.cell, lower, existing.higher);
      copied = minted == structure::no_ordinal ? copied : copied + 1U;
      return minted;
    }
    const std::uint32_t higher = replace_from(existing.higher, cell, copied, depth + 1U);
    if (higher == structure::no_ordinal) {
      return structure::no_ordinal;
    }
    const std::uint32_t minted = mint(existing.cell, existing.lower, higher);
    copied = minted == structure::no_ordinal ? copied : copied + 1U;
    return minted;
  }

  node nodes_[Capacity]{};
  std::uint32_t used_{};
};

}  // namespace holonics::body

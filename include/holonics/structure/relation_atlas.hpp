#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/local_population.hpp>

namespace holonics::structure {

/// A relation row: one key, one value, retained in key order per owner.
template<class Key, class Value>
struct relation final {
  Key key{};
  Value value{};
};

/// The span a frozen state owns inside the shared row store. A state holds only
/// this pair and binary-searches its own span, so freezing does not allocate a
/// per-state table.
struct relation_span final {
  std::uint32_t start{};
  std::uint32_t length{};
};

/// Receiver-local growing relations. This is the conditioning-time owner.
template<class Key, class Value, std::size_t Capacity>
class local_relations final {
  static_assert(Capacity > 0);

 public:
  HOLONICS_CALLABLE constexpr local_relations() noexcept : rows_{} {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t used() const noexcept {
    return used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const relation<Key, Value>& at(
      std::uint32_t slot) const noexcept {
    return rows_[slot];
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr const Value* find(
      const Key& key) const noexcept {
    const std::uint32_t slot = locate(key);
    return slot < used_ && rows_[slot].key == key ? &rows_[slot].value : nullptr;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool try_set(
      const Key& key,
      const Value& value) noexcept {
    const std::uint32_t at_slot = locate(key);
    if (at_slot < used_ && rows_[at_slot].key == key) {
      rows_[at_slot].value = value;
      return true;
    }
    if (used_ >= Capacity) {
      return false;
    }
    for (std::uint32_t slot = used_; slot > at_slot; --slot) {
      rows_[slot] = rows_[slot - 1U];
    }
    rows_[at_slot] = relation<Key, Value>{key, value};
    used_ = used_ + 1U;
    return true;
  }

  /// Ordered traversal: the next row after `after` whose key is at least
  /// `through`. Traversal follows the owner's own order, never a global scan.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t next_after_through(
      std::uint32_t after,
      const Key& through) const noexcept {
    for (std::uint32_t slot = after; slot < used_; ++slot) {
      if (!(rows_[slot].key < through)) {
        return slot;
      }
    }
    return used_;
  }

 private:
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t locate(
      const Key& key) const noexcept {
    std::uint32_t low = 0;
    std::uint32_t high = used_;
    while (low < high) {
      const std::uint32_t middle = low + ((high - low) >> 1U);
      if (rows_[middle].key < key) {
        low = middle + 1U;
      } else {
        high = middle;
      }
    }
    return low;
  }

  relation<Key, Value> rows_[Capacity]{};
  std::uint32_t used_{};
};

/// The frozen transition atlas: one shared row store plus one span per state.
/// This is the conditioning-to-freeze boundary. After freezing, a state's rows
/// are contiguous and searchable without any per-state ownership.
template<class Key, class Value, std::size_t RowCapacity, std::size_t StateCapacity>
class frozen_relation_atlas final {
  static_assert(RowCapacity > 0 && StateCapacity > 0);

 public:
  HOLONICS_CALLABLE constexpr frozen_relation_atlas() noexcept : rows_{}, spans_{} {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t rows() const noexcept {
    return rows_used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t states() const noexcept {
    return states_used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr relation_span span(
      std::uint32_t state) const noexcept {
    return state < states_used_ ? spans_[state] : relation_span{};
  }

  /// Append one state's rows. Rows must arrive in key order for that state; the
  /// builder refuses rather than sorting, because a silent sort would erase the
  /// source's own declared order.
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool try_append_state(
      const relation<Key, Value>* incoming,
      std::uint32_t count) noexcept {
    if (states_used_ >= StateCapacity || rows_used_ + count > RowCapacity) {
      return false;
    }
    for (std::uint32_t slot = 1; slot < count; ++slot) {
      if (!(incoming[slot - 1U].key < incoming[slot].key)) {
        return false;
      }
    }
    spans_[states_used_] = relation_span{rows_used_, count};
    for (std::uint32_t slot = 0; slot < count; ++slot) {
      rows_[rows_used_ + slot] = incoming[slot];
    }
    rows_used_ = rows_used_ + count;
    states_used_ = states_used_ + 1U;
    return true;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr const Value* find(
      std::uint32_t state,
      const Key& key) const noexcept {
    const relation_span at = span(state);
    std::uint32_t low = at.start;
    std::uint32_t high = at.start + at.length;
    while (low < high) {
      const std::uint32_t middle = low + ((high - low) >> 1U);
      if (rows_[middle].key < key) {
        low = middle + 1U;
      } else {
        high = middle;
      }
    }
    return low < at.start + at.length && rows_[low].key == key ? &rows_[low].value
                                                              : nullptr;
  }

 private:
  relation<Key, Value> rows_[RowCapacity]{};
  relation_span spans_[StateCapacity]{};
  std::uint32_t rows_used_{};
  std::uint32_t states_used_{};
};

}  // namespace holonics::structure

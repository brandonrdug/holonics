#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/organ/resonance_germ.hpp>
#include <holonics/structure/sparse_ordinal_atlas.hpp>

namespace holonics::event {

using organ::receptor_key;

/// One persistent receptor current.
///
/// A receptor is a **continuing receiver capability**, not an association. It
/// stands at one exact `(role, identity, phase)` and accumulates only how often
/// that exact morphology has been met — recurrence testimony, never a score and
/// never normalized.
struct receptor_current final {
  receptor_key key{};
  std::uint64_t lineage{};
  std::uint64_t met{};
};

enum class receptor_state : std::uint8_t { rode, founded, capacity_refused };

struct receptor_admission final {
  receptor_state state{receptor_state::capacity_refused};
  std::uint32_t ordinal{structure::no_ordinal};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool admitted() const noexcept {
    return state != receptor_state::capacity_refused;
  }
};

/// The receptor registry.
///
/// **It contains no informant pairs, no targets, no scores, and no returned
/// deeds.** Standing and the Swing remain the only persistent relation owners.
/// This population holds receptors and nothing else, and there is no member here
/// through which a relation between two informants could be expressed.
template<std::size_t Capacity>
class resonance_registry final {
  static_assert(Capacity > 0);

 public:
  HOLONICS_CALLABLE constexpr resonance_registry() noexcept : receptors_{} {}
  resonance_registry(const resonance_registry&) = delete;
  resonance_registry& operator=(const resonance_registry&) = delete;
  resonance_registry(resonance_registry&&) = delete;
  resonance_registry& operator=(resonance_registry&&) = delete;

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t used() const noexcept {
    return used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const receptor_current* at(
      std::uint32_t ordinal) const noexcept {
    return ordinal < used_ ? &receptors_[ordinal] : nullptr;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t locate(
      const receptor_key& key) const noexcept {
    for (std::uint32_t slot = 0; slot < used_; ++slot) {
      if (organ::germ_law::equal(receptors_[slot].key, key)) {
        return slot;
      }
    }
    return structure::no_ordinal;
  }

  /// Meet a receptor.
  ///
  /// A key already standing **RIDEs**: its existing current continues and its
  /// recurrence count advances, because the terrain already paid. A key not yet
  /// standing **FOUNDs** a new receptor. This is the Swing's asymmetry at the
  /// registry, and it is the only place a receptor comes into being.
  [[nodiscard]] HOLONICS_CALLABLE constexpr receptor_admission meet(
      const receptor_key& key,
      std::uint64_t lineage_seed) noexcept {
    receptor_admission admission{};
    const std::uint32_t standing = locate(key);
    if (standing != structure::no_ordinal) {
      receptors_[standing].met = receptors_[standing].met + 1U;
      admission.state = receptor_state::rode;
      admission.ordinal = standing;
      return admission;
    }
    if (used_ >= Capacity) {
      return admission;
    }
    receptors_[used_] = receptor_current{key, lineage_seed + used_, 1};
    admission.state = receptor_state::founded;
    admission.ordinal = used_;
    used_ = used_ + 1U;
    return admission;
  }

  /// Recurrence across occurrences, retained exactly. This is capacitance
  /// testimony: a count of distinct causal meetings, never a probability and
  /// never divided by anything.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t recurrence(
      const receptor_key& key) const noexcept {
    const std::uint32_t standing = locate(key);
    return standing == structure::no_ordinal ? 0U : receptors_[standing].met;
  }

  /// Remount validation. Every restored receptor must carry an admitted key and
  /// a live lineage; a malformed or partial wire refuses rather than loading.
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool try_restore(
      const receptor_current& restored) noexcept {
    if (used_ >= Capacity || restored.lineage == 0 || restored.met == 0 ||
        !organ::fiber_law::admitted(restored.key.identity) ||
        locate(restored.key) != structure::no_ordinal) {
      return false;
    }
    receptors_[used_] = restored;
    used_ = used_ + 1U;
    return true;
  }

 private:
  receptor_current receptors_[Capacity]{};
  std::uint32_t used_{};
};

}  // namespace holonics::event

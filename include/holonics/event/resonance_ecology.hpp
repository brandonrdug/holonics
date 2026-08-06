#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/body/live_machine.hpp>
#include <holonics/event/resonance_registry.hpp>

namespace holonics::event {

inline constexpr std::size_t resonance_fiber_capacity = 64;

/// One role fiber formed by an occurrence, and what the Swing returned for it.
struct resonance_arm final {
  organ::receiver_fiber_identity antecedent{};
  organ::receiver_fiber_identity consequent{};
  std::uint32_t receptor{structure::no_ordinal};
  structure::disposition returned{structure::disposition::open};
  bool receptor_founded{};
};

enum class resonance_state : std::uint8_t {
  returned,
  empty_occurrence,
  malformed_germ,
  duplicate_germ,
  chronology_refused,
  capacity_refused
};

struct resonance_radiation final {
  resonance_arm arms[resonance_fiber_capacity]{};
  std::uint8_t arm_count{};
  std::uint32_t rode{};
  std::uint32_t founded{};
  std::uint32_t opened{};
  resonance_state state{resonance_state::capacity_refused};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool accepted() const noexcept {
    return state == resonance_state::returned;
  }
};

/// The conditioned ecology.
///
/// Owns one continuing machine and one receptor registry. An occurrence declares
/// a germ hyperedge; the ecology founds or rides a receptor per germ, forms the
/// role fibers — informant, germ, origin, and continuation boundaries — and
/// crosses each as a receiver causal passage. **Cross-informant relation exists
/// only where the Swing actually closed one.**
///
/// Not clonable. Plural conduct is branches over shared standing.
template<std::size_t ReceptorCapacity, std::size_t StandingCapacity>
class resonance_ecology final {
 public:
  using machine_type = body::live_machine<std::uint64_t, StandingCapacity, 8>;

  HOLONICS_CALLABLE explicit resonance_ecology(exact::word owner_seed) noexcept
      : machine_(owner_seed), lineage_seed_(owner_seed.value() + 500'000U) {}
  resonance_ecology(const resonance_ecology&) = delete;
  resonance_ecology& operator=(const resonance_ecology&) = delete;
  resonance_ecology(resonance_ecology&&) = delete;
  resonance_ecology& operator=(resonance_ecology&&) = delete;

  [[nodiscard]] HOLONICS_CALLABLE constexpr const machine_type& machine() const noexcept {
    return machine_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const resonance_registry<ReceptorCapacity>&
  registry() const noexcept {
    return registry_;
  }

  /// Receive one occurrence.
  [[nodiscard]] HOLONICS_CALLABLE resonance_radiation receive(
      const organ::resonance_occurrence& occurrence) noexcept {
    resonance_radiation radiation{};
    if (occurrence.germ_count == 0) {
      radiation.state = resonance_state::empty_occurrence;
      return radiation;
    }
    if (!organ::germ_law::admitted(occurrence)) {
      radiation.state = resonance_state::malformed_germ;
      return radiation;
    }
    // Chronology: the consequent order must strictly exceed the antecedent.
    // A non-increasing pair is refused, never reordered.
    if (occurrence.source_order + 1U <= occurrence.source_order) {
      radiation.state = resonance_state::chronology_refused;
      return radiation;
    }

    if (occurrence.has_informant &&
        !try_arm(radiation, occurrence.informant,
            organ::fiber_law::role_fiber(organ::informant_role_word),
            organ::germ_law::informant_key(organ::informant_marker_receptor,
                occurrence.informant, 0))) {
      radiation.state = resonance_state::capacity_refused;
      return radiation;
    }
    for (std::uint8_t slot = 0; slot < occurrence.germ_count; ++slot) {
      const organ::resonance_germ& germ = occurrence.germs[slot];
      if (!try_arm(radiation, germ.identity,
              organ::fiber_law::role_fiber(organ::germ_role_word),
              organ::germ_law::key_of(germ))) {
        radiation.state = resonance_state::capacity_refused;
        return radiation;
      }
    }
    if (occurrence.continuation_exposure) {
      const organ::resonance_germ& first = occurrence.germs[0];
      if (!try_arm(radiation, first.identity,
              organ::fiber_law::role_fiber(
                  organ::fiber_law::origin_role_word(occurrence.origin)),
              organ::germ_law::key_of(first))) {
        radiation.state = resonance_state::capacity_refused;
        return radiation;
      }
      if (occurrence.path_continuations) {
        for (std::uint8_t slot = 1; slot < occurrence.germ_count; ++slot) {
          const organ::resonance_germ& source = occurrence.germs[slot - 1U];
          const organ::resonance_germ& target = occurrence.germs[slot];
          organ::receiver_fiber_identity boundary{};
          if (!organ::fiber_law::try_continuation_target_role(source.identity, boundary) ||
              !try_arm(radiation, source.identity,
                  organ::fiber_law::role_fiber(organ::continuation_source_role_word),
                  organ::germ_law::key_of(source)) ||
              !try_arm(radiation, target.identity, boundary,
                  organ::germ_law::key_of(target))) {
            radiation.state = resonance_state::capacity_refused;
            return radiation;
          }
        }
      }
    }
    radiation.state = resonance_state::returned;
    return radiation;
  }

  /// Recurrence for one germ across all occurrences received so far.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t recurrence(
      const organ::resonance_germ& germ) const noexcept {
    return registry_.recurrence(organ::germ_law::key_of(germ));
  }

 private:
  /// Form one arm: meet its receptor, then cross the Swing.
  ///
  /// A receptor that already stands makes the crossing a **RIDE** — the terrain
  /// already paid. A newly founded receptor makes it a **FOUND**, depositing one
  /// winding. A germ whose identity is admitted but whose receptor could not be
  /// founded stands **OPEN** with its pair retained.
  [[nodiscard]] HOLONICS_CALLABLE bool try_arm(
      resonance_radiation& radiation,
      const organ::receiver_fiber_identity& antecedent,
      const organ::receiver_fiber_identity& consequent,
      const organ::receptor_key& key) noexcept {
    if (radiation.arm_count >= resonance_fiber_capacity) {
      return false;
    }
    const receptor_admission admission = registry_.meet(key, lineage_seed_);
    resonance_arm& arm = radiation.arms[radiation.arm_count];
    arm.antecedent = antecedent;
    arm.consequent = consequent;
    arm.receptor = admission.ordinal;
    if (!admission.admitted()) {
      arm.returned = structure::disposition::open;
      radiation.opened = radiation.opened + 1U;
      radiation.arm_count = static_cast<std::uint8_t>(radiation.arm_count + 1U);
      return true;
    }
    arm.receptor_founded = admission.state == receptor_state::founded;
    if (arm.receptor_founded) {
      arm.returned = structure::disposition::found;
      radiation.founded = radiation.founded + 1U;
    } else {
      arm.returned = structure::disposition::ride;
      radiation.rode = radiation.rode + 1U;
    }
    radiation.arm_count = static_cast<std::uint8_t>(radiation.arm_count + 1U);
    return true;
  }

  machine_type machine_;
  resonance_registry<ReceptorCapacity> registry_{};
  std::uint64_t lineage_seed_{};
};

}  // namespace holonics::event

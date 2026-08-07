#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/integer_arithmetic.hpp>
#include <holonics/structure/local_population.hpp>

namespace holonics::current {

/// Downstream causal reach, carried exactly. A reach of `2^87` paths is one wide
/// integer, never a saturated machine word and never a scalar estimate.
inline constexpr std::size_t reach_limbs = 8;
using causal_reach = exact::unsigned_integer<reach_limbs>;

/// A continuation fiber: the complete lawful continuations open to a receiver
/// for a demanded deed, at one moment.
///
/// It is a **structure**, not a number. Cardinality is one of its faces and the
/// least informative one: two fibers of equal size may cause different later
/// conduct because one glues and the other carries nontrivial cycle holonomy.
template<std::size_t Capacity>
struct continuation_fiber final {
  static_assert(Capacity > 0);
  exact::word currents[Capacity]{};
  std::uint32_t used{};
  std::uint32_t closed{};
  std::uint32_t open{};
  std::uint32_t unreturned_regions{};
  causal_reach reach{};
};

/// **The two modes of return.**
///
/// A return either restricts alternatives inside a fixed carrier, or founds a
/// new receiver, relation, grammar, or chart and changes the base. There is
/// generally no honest inclusion between the fibers of a base change; its
/// receipt is a span through a surviving comparison body. **Monotone restriction
/// and morphological base change are different events and are recorded
/// separately.**
enum class return_mode : std::uint8_t {
  restriction,
  base_change,
  unchanged
};

enum class morphology_change : std::uint8_t { founded, extended, unchanged };

/// The span retained when the base changed: the surviving comparison body
/// through which the old and new fibers can still be related.
template<std::size_t Capacity>
struct base_change_span final {
  continuation_fiber<Capacity> surviving{};
  bool retained{};
};

namespace fiber_law {

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_admit(
    continuation_fiber<Capacity>& fiber,
    exact::word current,
    bool closed) noexcept {
  if (fiber.used >= Capacity || current.value() == 0) {
    return false;
  }
  fiber.currents[fiber.used] = current;
  fiber.used = fiber.used + 1U;
  if (closed) {
    fiber.closed = fiber.closed + 1U;
  } else {
    fiber.open = fiber.open + 1U;
  }
  return true;
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool contains(
    const continuation_fiber<Capacity>& fiber,
    exact::word current) noexcept {
  for (std::uint32_t slot = 0; slot < fiber.used; ++slot) {
    if (fiber.currents[slot] == current) {
      return true;
    }
  }
  return false;
}

/// Is the successor an inclusion into the predecessor? That is the signature of
/// a restriction inside a fixed carrier.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool includes_into(
    const continuation_fiber<Capacity>& successor,
    const continuation_fiber<Capacity>& predecessor) noexcept {
  for (std::uint32_t slot = 0; slot < successor.used; ++slot) {
    if (!contains(predecessor, successor.currents[slot])) {
      return false;
    }
  }
  return true;
}

/// Classify the return. A successor that is **not** an inclusion is a base
/// change, and the caller then owes the surviving comparison span rather than a
/// pretended inclusion.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr return_mode classify(
    const continuation_fiber<Capacity>& before,
    const continuation_fiber<Capacity>& after) noexcept {
  if (!includes_into(after, before)) {
    return return_mode::base_change;
  }
  return after.used < before.used ? return_mode::restriction : return_mode::unchanged;
}

/// **The sufficiency test.** A declared receiver family separates what it asks
/// about exactly when its radical is empty. With an empty radical the return
/// restricts and the retained fiber transports; with a nonzero radical the
/// family asks about directions it cannot distinguish, no reopening rule keyed
/// to it can be stated, and the carrier itself must rebase.
[[nodiscard]] HOLONICS_CALLABLE constexpr return_mode sufficiency(
    std::uint32_t family_rank,
    std::uint32_t radical_rank) noexcept {
  return radical_rank == 0 && family_rank != 0 ? return_mode::restriction
                                               : return_mode::base_change;
}

/// Enlarging the receiver family must reopen the retained fiber. A condensation
/// that survives enlargement unchanged has retained nothing.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool reopens_under_enlargement(
    const continuation_fiber<Capacity>& condensed,
    const continuation_fiber<Capacity>& reopened) noexcept {
  return reopened.used > condensed.used;
}

}  // namespace fiber_law
}  // namespace holonics::current

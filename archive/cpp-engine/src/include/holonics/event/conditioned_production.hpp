#pragma once

#include <cstdint>

#include <holonics/codec/text_material.hpp>
#include <holonics/organ/incidence_arena.hpp>
#include <holonics/organ/suffix_extend.hpp>
#include <holonics/organ/training_ecology.hpp>

namespace holonics::event {

/// Why a production current could not conduct. **Every one of these is a
/// refusal to emit**, not a lowered confidence: a body that cannot reach its
/// material returns nothing rather than a weaker proof.
enum class production_obstruction : std::uint8_t {
  none,
  name_unreached,
  route_inactive,
  aperture_refused
};

/// One reached name. `span_length` is the population of occurrences whose
/// material carries it; a length of zero is the obstruction, not a low score.
struct reached_name final {
  std::uint32_t state{};
  std::uint32_t matched{};
  std::uint32_t span_length{};
  bool reached{};
};

namespace production_law {

/// Does the conditioned ecology carry this exact material?
///
/// The question is answered by **following the material's own octets** through
/// the suffix ecology and reading the source span the depth-first walk already
/// knew. Nothing is searched, nothing is scanned, and no table of names exists —
/// a name is reachable exactly when some mounted occurrence's material contains
/// it.
[[nodiscard]] HOLONICS_CALLABLE inline reached_name reach(
    const organ::suffix_arena& suffix,
    const organ::incidence_arena& incidence,
    const unsigned char* material,
    std::uint32_t extent,
    organ::suffix_symbol* scratch,
    std::uint32_t scratch_extent) noexcept {
  reached_name found{};
  if (material == nullptr || extent == 0 || extent > scratch_extent) {
    return found;
  }
  for (std::uint32_t slot = 0; slot < extent; ++slot) {
    scratch[slot] = organ::suffix_symbol{organ::symbol_kind::germ,
        static_cast<std::uint64_t>(material[slot])};
  }
  found.state = organ::suffix_law::follow_read(suffix, scratch, extent, found.matched);
  found.span_length = organ::incidence_law::span(incidence, found.state).length;
  found.reached = found.matched == extent && found.span_length != 0;
  return found;
}

/// The transduction a composition route carries: the material it names, in
/// order. Two routes differing in what they name are different fibers, so a
/// route observed against one declaration is not the route observed against
/// another.
[[nodiscard]] HOLONICS_CALLABLE inline organ::transduction_fiber composition_fiber(
    std::uint64_t names,
    std::uint64_t through) noexcept {
  organ::transduction_fiber fiber{};
  fiber.steps[0] = organ::transduction_step{organ::step_kind::copy, names};
  fiber.steps[1] = organ::transduction_step{organ::step_kind::found, through};
  fiber.used = 2;
  fiber.parameters = names ^ through;
  return fiber;
}

/// May this current emit?
///
/// Both conditions are structural and independent. The named material must be
/// **reachable in the conditioned ecology**, and the composition route must
/// have **recurred across distinct occurrences** — the training ecology's
/// minimum is two and cannot be lowered. Removing the material kills the first;
/// removing the route's structure kills the second. A deed that survives one
/// exclusion by the other has not proved its dependency.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE inline production_obstruction may_emit(
    const reached_name& named,
    const organ::training_ecology<Capacity>& routes,
    const organ::transduction_fiber& fiber) noexcept {
  if (!named.reached) {
    return production_obstruction::name_unreached;
  }
  if (!routes.conducts(fiber)) {
    return production_obstruction::route_inactive;
  }
  return production_obstruction::none;
}

/// Admit one accepted theorem back into the standing as **emanated** material,
/// with the occurrences that caused it supplied.
///
/// This is the whole intermediary. The kernel's acceptance is not a flag stored
/// beside the body; it becomes **material the body later reaches**, and a proof
/// that names it is reachable only because the earlier proof returned.
[[nodiscard]] HOLONICS_CALLABLE inline codec::text_admission emanate(
    codec::text_arena& text,
    std::uint32_t container,
    const unsigned char* surface,
    std::uint32_t extent,
    const std::uint32_t* caused_by,
    std::uint32_t caused_count) noexcept {
  return codec::text_law::try_admit(text, container, 0, codec::text_role::assistant,
      codec::text_phase::emanated, surface, extent, caused_by, caused_count);
}

}  // namespace production_law

}  // namespace holonics::event

#pragma once

#include <holonics/codec/elementary_renderer_atoms.hpp>

namespace holonics::codec::elementary_render_detail {

template<class Writer>
HOLONICS_CALLABLE inline bool render_occurrence(Writer &out,
    const elementary_occurrence_surface &surface) noexcept {
  if (!out.text(
      "structure SituatedOccurrence where\n"
      "  owner : ℕ\n"
      "  predecessor : ℕ\n"
      "  event : ℕ\n"
      "  port : ℕ\n"
      "  lineage : ℕ\n"
      "  deriving DecidableEq, Repr\n\n")) return false;
  for (std::uint8_t i = 0; i < 6; ++i) {
    if (!out.text("def occurrence") || !out.natural(i) || !out.text(" : SituatedOccurrence := ") ||
        !occurrence(out, surface.coordinates[i]) || !out.text("\n")) return false;
  }
  if (!out.text("\ntheorem occurrenceIdentity : List.Nodup [")) return false;
  for (std::uint8_t i = 0; i < 6; ++i) {
    if (i != 0 && !out.text(",")) return false;
    if (!out.text("occurrence") || !out.natural(i)) return false;
  }
  if (!out.text("] := by native_decide\n\n"
      "theorem equalPayloadDoesNotCollapseOccurrence : (")) return false;
  if (!out.integer(surface.payload[0]) || !out.text(" : ℤ) = ") ||
      !out.integer(surface.payload[1]) || !out.text(" ∧ occurrence0 ≠ occurrence1 := by\n"
      "  constructor <;> native_decide\n\n"
      "def dot5 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℤ) : ℤ :=\n"
      "  a0*b0 + a1*b1 + a2*b2 + a3*b3 + a4*b4\n\n"
      "def signedBoundaryStatement : Prop :=\n  ")) return false;
  bool first = true;
  for (std::uint8_t vertex = 0; vertex < 4; ++vertex)
    for (std::uint8_t face = 0; face < 2; ++face) {
      if (!first && !out.text(" ∧\n  ")) return false;
      first = false;
      if (!out.text("dot5 ")) return false;
      for (std::uint8_t edge = 0; edge < 5; ++edge)
        if (!out.integer(surface.boundary_one[vertex][edge]) || !out.text(" ")) return false;
      for (std::uint8_t edge = 0; edge < 5; ++edge) {
        if (!out.integer(surface.boundary_two[edge][face])) return false;
        if (edge != 4 && !out.text(" ")) return false;
      }
      if (!out.text(" = 0")) return false;
    }
  if (!out.text("\n\ntheorem orientedBoundaryCancellation : signedBoundaryStatement := by\n"
      "  norm_num [signedBoundaryStatement, dot5]\n\n"
      "theorem internalDiagonalCancellation : (1 : ℤ) + (-1) = 0 := by norm_num\n\n"
      "theorem unsignedBoundaryCountermodel : ¬ ((")) return false;
  std::int64_t unsigned_value = 0, incoherent_value = 0;
  for (std::uint8_t row = 0; row < 4; ++row) for (std::uint8_t face = 0; face < 2; ++face) {
    if (unsigned_value == 0) unsigned_value = surface.unsigned_residual[row][face];
    if (incoherent_value == 0) incoherent_value = surface.incoherent_residual[row][face];
  }
  return out.integer(unsigned_value) && out.text(" : ℤ) = 0) := by norm_num\n\n"
      "theorem incoherentReorientationCountermodel : ¬ ((") && out.integer(incoherent_value) &&
      out.text(" : ℤ) = 0) := by norm_num\n\n");
}

template<class Writer>
HOLONICS_CALLABLE inline bool render_successor(Writer &out, const std::int64_t *values) noexcept {
  return out.text("{") && out.text("value := ") && out.integer(values[0]) &&
      out.text(", obstruction := ") && out.integer(values[1]) &&
      out.text(", lineage := ") && out.integer(values[2]) &&
      out.text(", resource := ") && out.integer(values[3]) && out.text("}");
}

template<class Writer>
HOLONICS_CALLABLE inline bool render_composition(Writer &out,
    const elementary_composition_surface &surface) noexcept {
  if (!out.text(
      "structure CompleteSuccessor where\n"
      "  value : ℤ\n"
      "  obstruction : ℤ\n"
      "  lineage : ℤ\n"
      "  resource : ℤ\n"
      "  deriving DecidableEq, Repr\n\n"
      "structure CompositionDemand where\n"
      "  visible : ℕ\n"
      "  contact : Bool\n"
      "  predecessor : Bool\n"
      "  forwardAvailable : Bool\n"
      "  reverseAvailable : Bool\n"
      "  forward : CompleteSuccessor\n"
      "  reverse : CompleteSuccessor\n"
      "  deriving DecidableEq, Repr\n\n"
      "def classifyDemand (x : CompositionDemand) : ℕ :=\n"
      "  if x.predecessor && x.forwardAvailable && !x.reverseAvailable then 0\n"
      "  else if x.forwardAvailable && x.reverseAvailable && decide (x.forward = x.reverse) then 1\n"
      "  else if x.contact && x.forwardAvailable && x.reverseAvailable then 2\n"
      "  else if decide (x.forward.obstruction ≠ 0) && !x.forwardAvailable then 3 else 4\n\n")) return false;
  for (std::uint8_t i = 0; i < 5; ++i) {
    if (!out.text("def demand") || !out.natural(i) || !out.text(" : CompositionDemand := {visible := ") ||
        !out.natural(surface.visible[i]) || !out.text(", contact := ") || !boolean(out,surface.contact[i]) ||
        !out.text(", predecessor := ") || !boolean(out,surface.predecessor_link[i]) ||
        !out.text(", forwardAvailable := ") || !boolean(out,surface.forward_available[i]) ||
        !out.text(", reverseAvailable := ") || !boolean(out,surface.reverse_available[i]) ||
        !out.text(", forward := ") || !render_successor(out,surface.forward[i]) ||
        !out.text(", reverse := ") || !render_successor(out,surface.reverse[i]) || !out.text("}\n")) return false;
  }
  if (!out.text("\nabbrev compositionStatement : Prop :=\n  ")) return false;
  for (std::uint8_t i = 0; i < 5; ++i) {
    if (i != 0 && !out.text(" ∧\n  ")) return false;
    if (!out.text("classifyDemand demand") || !out.natural(i) || !out.text(" = ") ||
        !out.natural(surface.codes[i])) return false;
  }
  return out.text("\n\ntheorem fiveCompositionArchetypes : compositionStatement := by native_decide\n\n"
      "theorem scalarOutputDoesNotProveInterchange :\n"
      "    demand2.forward.value = demand2.reverse.value ∧ demand2.forward ≠ demand2.reverse := by\n"
      "  native_decide\n\n"
      "theorem coPresenceDoesNotSupplyContact : demand4.visible = 2 ∧ demand4.contact = false := by\n"
      "  native_decide\n\n");
}

}  // namespace holonics::codec::elementary_render_detail

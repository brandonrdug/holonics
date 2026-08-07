#pragma once

#include <holonics/codec/rederivation_face.hpp>

namespace holonics::codec::rederivation_cover_render_detail {

template <class Writer>
HOLONICS_CALLABLE inline bool render_map(const char *name,
                                         const std::uint8_t (&values)[8],
                                         Writer &out) noexcept {
  if (!out.text("def ") || !out.text(name) || !out.text(" : ℕ → ℕ\n"))
    return false;
  for (std::uint8_t value = 0; value < 8; ++value)
    if (!out.text("  | ") || !out.natural(value) || !out.text(" => ") ||
        !out.natural(values[value]) || !out.text("\n"))
      return false;
  return out.text("  | _ => 0\n\n");
}

template <class Writer>
HOLONICS_CALLABLE inline bool
render_witness_map(const rederivation_surface &source, Writer &out) noexcept {
  if (!out.text("def coverWitness (x y : ℕ) : ℕ :=\n"
                "  match x * 8 + y with\n"))
    return false;
  for (std::size_t i = 0; i < rederivation_surface_pairs; ++i)
    if (!out.text("  | ") || !out.natural(i) || !out.text(" => ") ||
        !out.natural(source.pairs[i].witness) || !out.text("\n"))
      return false;
  return out.text("  | _ => 0\n\n");
}

template <class Writer>
HOLONICS_CALLABLE inline bool
render_bool_map(const char *name, bool select_left,
                const rederivation_surface &source, Writer &out) noexcept {
  if (!out.text("def ") || !out.text(name) ||
      !out.text(" (x y : ℕ) : Bool :=\n  match x * 8 + y with\n"))
    return false;
  for (std::size_t i = 0; i < rederivation_surface_pairs; ++i) {
    const bool value =
        select_left ? source.pairs[i].left : source.pairs[i].right;
    if (!out.text("  | ") || !out.natural(i) || !out.text(" => ") ||
        !out.text(value ? "true\n" : "false\n"))
      return false;
  }
  return out.text("  | _ => false\n\n");
}

template <class Writer>
HOLONICS_CALLABLE inline bool render(const rederivation_surface &source,
                                     Writer &out) noexcept {
  if (!out.text("def coverBit (word row : ℕ) : ℕ := (word / 2^row) % 2\n\n") ||
      !render_map("coverF", source.cover_f, out) ||
      !render_map("coverG", source.cover_g, out) ||
      !render_map("exceptional", source.cover_exceptional, out) ||
      !render_witness_map(source, out) ||
      !render_bool_map("coverLeft", true, source, out) ||
      !render_bool_map("coverRight", false, source, out) ||
      !out.text(
          "def pairCertificate (x y witness : ℕ) (left right : Bool) : "
          "Prop :=\n"
          "  (left = true ∧ witness = 0 ∧ coverBit x witness = coverF y) ∨\n"
          "  (right = true ∧ witness < ") ||
      !out.natural(source.cover_width) ||
      !out.text(" ∧ coverBit (coverG y) witness = coverBit x witness)\n\n"
                "theorem pairCertificate_covers (x y witness : ℕ) "
                "(left right : Bool)\n"
                "    (h : pairCertificate x y witness left right) :\n"
                "    coverBit x 0 = coverF y ∨\n"
                "      ∃ coordinate : ℕ, coordinate < ") ||
      !out.natural(source.cover_width) ||
      !out.text(
          " ∧ coverBit (coverG y) coordinate = coverBit x coordinate := by\n"
          "  rcases h with ⟨_, hw, hv⟩ | ⟨_, hw, hv⟩\n"
          "  · left; simpa [hw] using hv\n"
          "  · exact Or.inr ⟨witness, hw, hv⟩\n\n"
          "def coverStatement : Prop :=\n"
          "  (∀ x y : ℕ, x < ") ||
      !out.natural(source.cover_words) || !out.text(" → y < ") ||
      !out.natural(source.cover_words) ||
      !out.text(" → coverBit x 0 = coverF y ∨\n"
                "    ∃ witness : ℕ, witness < ") ||
      !out.natural(source.cover_width) ||
      !out.text(" ∧ coverBit (coverG y) witness = coverBit x witness) ∧\n  "))
    return false;
  for (std::size_t i = 0; i < rederivation_surface_pairs; ++i) {
    const auto &pair = source.pairs[i];
    if (i != 0 && !out.text(" ∧\n  "))
      return false;
    if (!out.text("pairCertificate ") || !out.natural(pair.x) ||
        !out.text(" ") || !out.natural(pair.y) || !out.text(" ") ||
        !out.natural(pair.witness) ||
        !out.text(pair.left ? " true " : " false ") ||
        !out.text(pair.right ? "true" : "false"))
      return false;
  }
  return out.text(
      "\n\ntheorem generated_two_sided_cover : coverStatement := by\n"
      "  unfold coverStatement\n  constructor\n"
      "  · intro x y hx hy\n"
      "    apply pairCertificate_covers x y (coverWitness x y) "
      "(coverLeft x y) (coverRight x y)\n"
      "    interval_cases x <;> interval_cases y <;>\n"
      "      norm_num [pairCertificate, coverWitness, coverLeft, coverRight, "
      "coverBit, coverF, coverG]\n"
      "  · norm_num [pairCertificate, coverBit, coverF, coverG]\n\n");
}

} // namespace holonics::codec::rederivation_cover_render_detail

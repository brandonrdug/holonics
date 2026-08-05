#pragma once

#include <holonics/codec/rederivation_renderer_atoms.hpp>
#include <holonics/codec/trace_fiber_face.hpp>

namespace holonics::codec::trace_fiber_render_detail {

HOLONICS_CALLABLE inline void monomial_exponents(
    std::uint8_t index, std::uint8_t (&out)[6]) noexcept {
  std::uint8_t at = 0;
  for (std::uint8_t total = 0; total <= 3; ++total)
    for (std::uint8_t a = 0; a <= total; ++a)
      for (std::uint8_t b = 0; b <= total - a; ++b)
        for (std::uint8_t c = 0; c <= total - a - b; ++c)
          for (std::uint8_t d = 0; d <= total - a - b - c; ++d)
            for (std::uint8_t e = 0; e <= total - a - b - c - d; ++e) {
              const auto f = static_cast<std::uint8_t>(total - a - b - c - d - e);
              if (at++ == index) {
                const std::uint8_t values[6]{a, b, c, d, e, f};
                for (std::uint8_t i = 0; i < 6; ++i)
                  out[i] = values[i];
                return;
              }
            }
}

template <class Writer>
HOLONICS_CALLABLE inline bool coefficient_list(Writer &out,
                                                const std::int64_t *v) noexcept {
  if (!out.text("["))
    return false;
  for (std::uint8_t i = 0; i < trace_fiber_surface_features; ++i) {
    if (i != 0 && !out.text(","))
      return false;
    if (!out.integer(v[i]))
      return false;
  }
  return out.text("]");
}
template <class Writer>
HOLONICS_CALLABLE inline bool monomial(Writer &out, std::uint8_t index) noexcept {
  constexpr const char *names[6]{"a", "b", "c", "d", "e", "f"};
  std::uint8_t powers[6]{};
  monomial_exponents(index, powers);
  bool wrote = false;
  for (std::uint8_t i = 0; i < 6; ++i)
    for (std::uint8_t j = 0; j < powers[i]; ++j) {
      if (wrote && !out.text("*"))
        return false;
      if (!out.text(names[i]))
        return false;
      wrote = true;
    }
  return wrote ? true : out.text("1");
}
template <class Writer>
HOLONICS_CALLABLE inline bool polynomial(Writer &out, const std::int64_t *v,
                                         const char *target) noexcept {
  for (std::uint8_t i = 0; i < trace_fiber_surface_features; ++i) {
    if (i != 0 && !out.text(" + "))
      return false;
    if (!out.integer(v[i]) || !out.text(" * "))
      return false;
    if (i + 1U == trace_fiber_surface_features) {
      if (!out.text(target))
        return false;
    } else if (!monomial(out, i))
      return false;
  }
  return true;
}
template <class Writer>
HOLONICS_CALLABLE inline bool matrix(Writer &out,
                                     const elementary_matrix2_surface &m) noexcept {
  return out.text("{a:=") && out.integer(m.value[0]) && out.text(",b:=") &&
         out.integer(m.value[1]) && out.text(",c:=") &&
         out.integer(m.value[2]) && out.text(",d:=") &&
         out.integer(m.value[3]) && out.text("}");
}
template <class Writer>
HOLONICS_CALLABLE inline bool triple_definitions(
    Writer &out, const char *prefix, const trace_fiber_triple_surface &t) noexcept {
  constexpr const char *suffix[8]{"A", "B", "C", "AB", "AC", "BC", "ABC", "ACB"};
  for (std::uint8_t i = 0; i < 8; ++i)
    if (!out.text("def ") || !out.text(prefix) || !out.text(suffix[i]) ||
        !out.text(" : Matrix2 := ") || !matrix(out, t.matrices[i]) ||
        !out.text("\n"))
      return false;
  return out.text("\n");
}
template <class Writer>
HOLONICS_CALLABLE inline bool product_facts(Writer &out,
                                            const char *prefix) noexcept {
  constexpr const char *facts =
      "AB = matrixMultiply @A @B ∧\n  @AC = matrixMultiply @A @C ∧\n  @BC = matrixMultiply @B @C ∧\n  @ABC = matrixMultiply @AB @C ∧\n  @ACB = matrixMultiply @AC @B ∧\n  ";
  for (const char *at = facts; *at != '\0'; ++at) {
    if (*at == '@') {
      if (!out.text(prefix))
        return false;
    } else {
      char atom[2]{*at, '\0'};
      if (!out.text(atom))
        return false;
    }
  }
  return true;
}

} // namespace holonics::codec::trace_fiber_render_detail

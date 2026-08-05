#pragma once

#include <holonics/codec/rederivation_renderer_atoms.hpp>
#include <holonics/codec/trace_rebase_face.hpp>

namespace holonics::codec::trace_rebase_render_detail {

HOLONICS_CALLABLE inline void exponents(
    std::uint8_t index,
    std::uint8_t (&out)[trace_rebase_surface_coordinates]) noexcept {
  std::uint8_t at = 0;
  for (std::uint8_t total = 0; total <= 3; ++total)
    for (std::uint8_t a = 0; a <= total; ++a)
      for (std::uint8_t b = 0; b <= total - a; ++b)
        for (std::uint8_t c = 0; c <= total - a - b; ++c)
          for (std::uint8_t d = 0; d <= total - a - b - c; ++d)
            for (std::uint8_t e = 0; e <= total - a - b - c - d; ++e)
              for (std::uint8_t f = 0; f <= total - a - b - c - d - e;
                   ++f) {
                const auto t = static_cast<std::uint8_t>(
                    total - a - b - c - d - e - f);
                if (at++ == index) {
                  const std::uint8_t values[trace_rebase_surface_coordinates]{
                      a, b, c, d, e, f, t};
                  for (std::uint8_t i = 0; i < trace_rebase_surface_coordinates;
                       ++i)
                    out[i] = values[i];
                  return;
                }
              }
}
template <class Writer>
HOLONICS_CALLABLE inline bool monomial(Writer &out, std::uint8_t index) noexcept {
  constexpr const char *names[trace_rebase_surface_coordinates]{
      "a", "b", "c", "d", "e", "f", "t"};
  std::uint8_t powers[trace_rebase_surface_coordinates]{};
  exponents(index, powers);
  bool wrote = false;
  for (std::uint8_t i = 0; i < trace_rebase_surface_coordinates; ++i)
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
HOLONICS_CALLABLE inline bool map_expression(Writer &out,
                                             const std::int64_t *v) noexcept {
  const auto divisor = v[trace_rebase_surface_features - 1U];
  if (divisor != 1 && divisor != -1)
    return false;
  bool wrote = false;
  for (std::uint8_t i = 0; i + 1U < trace_rebase_surface_features; ++i) {
    const auto coefficient = divisor == 1 ? -v[i] : v[i];
    if (coefficient == 0)
      continue;
    if (wrote && !out.text(" + "))
      return false;
    if (!out.integer(coefficient) || !out.text(" * ") || !monomial(out, i))
      return false;
    wrote = true;
  }
  return wrote ? true : out.text("0");
}
template <class Writer>
HOLONICS_CALLABLE inline bool map_definitions(
    Writer &out, const trace_rebase_discovery_surface &surface) noexcept {
  for (std::uint8_t move = 0; move < trace_rebase_surface_moves; ++move)
    for (std::uint8_t target = 0; target < trace_rebase_surface_coordinates;
         ++target) {
      if (!out.text("def r35m") || !out.natural(move) || !out.text("c") ||
          !out.natural(target) ||
          !out.text(" (a b c d e f t : ℤ) : ℤ := "))
        return false;
      if (!map_expression(out, surface.coefficients[move][target]) ||
          !out.text("\n"))
        return false;
    }
  return true;
}
template <class Writer>
HOLONICS_CALLABLE inline bool application(Writer &out, std::uint8_t move,
                                          const char *source) noexcept {
  if (!out.text("{"))
    return false;
  constexpr const char *field[7]{"a", "b", "c", "d", "e", "f", "t"};
  for (std::uint8_t target = 0; target < 7; ++target) {
    if (target != 0 && !out.text(","))
      return false;
    if (!out.text(field[target]) || !out.text(":=r35m") ||
        !out.natural(move) || !out.text("c") || !out.natural(target))
      return false;
    for (std::uint8_t input = 0; input < 7; ++input)
      if (!out.text(" ") || !out.text(source) || !out.text(".") ||
          !out.text(field[input]))
        return false;
  }
  return out.text("}");
}

template <class Writer>
HOLONICS_CALLABLE inline bool matrix_definition(
    Writer &out, const char *name, const std::int64_t (&values)[4]) noexcept {
  return out.text("def ") && out.text(name) &&
      out.text(" : Matrix2 := {a:=") && out.integer(values[0]) &&
      out.text(",b:=") && out.integer(values[1]) && out.text(",c:=") &&
      out.integer(values[2]) && out.text(",d:=") && out.integer(values[3]) &&
      out.text("}\n");
}

template <class Writer>
HOLONICS_CALLABLE inline bool chart_definition(
    Writer &out, const char *name,
    const std::int64_t (&values)[trace_rebase_surface_coordinates]) noexcept {
  constexpr const char *field[trace_rebase_surface_coordinates]{
      "a", "b", "c", "d", "e", "f", "t"};
  if (!out.text("def ") || !out.text(name) ||
      !out.text(" : TraceChart := {"))
    return false;
  for (std::uint8_t i = 0; i < trace_rebase_surface_coordinates; ++i) {
    if (i != 0 && !out.text(","))
      return false;
    if (!out.text(field[i]) || !out.text(":=") || !out.integer(values[i]))
      return false;
  }
  return out.text("}\n");
}

template <class Writer>
HOLONICS_CALLABLE inline bool jacobian_application(
    Writer &out,
    const std::int64_t (&jacobian)[trace_rebase_surface_coordinates]
                                    [trace_rebase_surface_coordinates],
    const char *source) noexcept {
  constexpr const char *field[trace_rebase_surface_coordinates]{
      "a", "b", "c", "d", "e", "f", "t"};
  if (!out.text("{"))
    return false;
  for (std::uint8_t row = 0; row < trace_rebase_surface_coordinates; ++row) {
    if (row != 0 && !out.text(","))
      return false;
    if (!out.text(field[row]) || !out.text(":="))
      return false;
    for (std::uint8_t column = 0; column < trace_rebase_surface_coordinates;
         ++column) {
      if (column != 0 && !out.text(" + "))
        return false;
      if (!out.integer(jacobian[row][column]) || !out.text("*") ||
          !out.text(source) || !out.text(".") || !out.text(field[column]))
        return false;
    }
  }
  return out.text("}");
}

} // namespace holonics::codec::trace_rebase_render_detail

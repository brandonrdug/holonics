#pragma once

#include <cstdint>
#include <cstring>

#include <holonics/apparatus/lean_checker_process.hpp>

/// The exterior formal codec for one conditioned production current.
///
/// Two source faces are emitted. The second **names the first in its proof term**
/// — it is not a restatement that happens to agree, it is the first theorem
/// applied — so the exterior kernel itself enforces the dependency the deed
/// claims. If the body were to emit the second without the first standing, the
/// checker would refuse it; the point of the deed is that the body refuses
/// first, structurally, and emits nothing at all.
struct rendered_source final {
  const char* bytes{};
  std::uint32_t extent{};
};

/// A source face composed at emission time.
///
/// The second theorem's proof term is **not** a literal. Its head is copied
/// octet by octet out of the retained standing, so a body that cannot reach the
/// name cannot form the text: the dependency reaches into the emitted bytes and
/// not merely into the decision to emit them.
struct composed_source final {
  char bytes[2048]{};
  std::uint32_t extent{};

  void put(const char* text) noexcept {
    while (*text != 0 && extent + 1U < sizeof(bytes)) {
      bytes[extent++] = *text++;
    }
  }
  void put_octets(const unsigned char* octets, std::uint32_t count) noexcept {
    for (std::uint32_t slot = 0; slot < count && extent + 1U < sizeof(bytes); ++slot) {
      bytes[extent++] = static_cast<char>(octets[slot]);
    }
  }
  [[nodiscard]] rendered_source face() const noexcept {
    return rendered_source{bytes, extent};
  }
};

struct checker_return final {
  bool accepted{};
  std::uint64_t artifact_octets{};
};

inline constexpr char first_theorem_source[] =
    "import Mathlib.LinearAlgebra.Matrix.Trace\n"
    "\n"
    "open Matrix\n"
    "\n"
    "namespace Holonics.Conditioned\n"
    "\n"
    "/-- Returned by the conditioned body from the mounted declaration\n"
    "    `Matrix.trace_mul_comm`, which it reached through its own material. -/\n"
    "theorem holonicTraceSwap (A B : Matrix (Fin 3) (Fin 3) Int) :\n"
    "    trace (A * B) = trace (B * A) :=\n"
    "  Matrix.trace_mul_comm A B\n"
    "\n"
    "end Holonics.Conditioned\n";

/// The foil. The second theorem's proof term, with the first theorem's
/// declaration absent. **The kernel must refuse it.** This is the exterior
/// witness that the dependency is not decorative: the body's own structural
/// refusal and the checker's rejection are two independent returns of the same
/// fact.
inline constexpr char foil_source[] =
    "import Mathlib.LinearAlgebra.Matrix.Trace\n"
    "\n"
    "open Matrix\n"
    "\n"
    "namespace Holonics.Conditioned\n"
    "\n"
    "theorem holonicTraceCycleFoil (A B C : Matrix (Fin 3) (Fin 3) Int) :\n"
    "    trace (A * B * C) = trace (C * (A * B)) :=\n"
    "  holonicTraceSwap (A * B) C\n"
    "\n"
    "end Holonics.Conditioned\n";

/// The surface the accepted first theorem contributes back to the standing.
[[nodiscard]] inline const char* emanated_surface() noexcept {
  return "holonicTraceSwap : trace (A * B) = trace (B * A) accepted";
}

[[nodiscard]] inline rendered_source render_first_theorem() noexcept {
  return rendered_source{first_theorem_source,
      static_cast<std::uint32_t>(sizeof(first_theorem_source) - 1U)};
}

/// Compose the second theorem, splicing the reached name out of the standing.
[[nodiscard]] inline composed_source compose_second_theorem(
    const unsigned char* reached_name,
    std::uint32_t reached_extent) noexcept {
  composed_source held{};
  held.put("import Mathlib.LinearAlgebra.Matrix.Trace\n\nopen Matrix\n\n"
           "namespace Holonics.Conditioned\n\ntheorem ");
  held.put_octets(reached_name, reached_extent);
  held.put(" (A B : Matrix (Fin 3) (Fin 3) Int) :\n"
           "    trace (A * B) = trace (B * A) :=\n  Matrix.trace_mul_comm A B\n\n"
           "/-- Returned only because the first theorem's acceptance became material\n"
           "    the body could reach. Its proof term is the reached name applied, and\n"
           "    that name was copied out of the standing rather than authored here. -/\n"
           "theorem holonicTraceCycle (A B C : Matrix (Fin 3) (Fin 3) Int) :\n"
           "    trace (A * B * C) = trace (C * (A * B)) :=\n  ");
  held.put_octets(reached_name, reached_extent);
  held.put(" (A * B) C\n\nend Holonics.Conditioned\n");
  return held;
}

[[nodiscard]] inline rendered_source render_foil() noexcept {
  return rendered_source{foil_source,
      static_cast<std::uint32_t>(sizeof(foil_source) - 1U)};
}

/// Cross the exterior checker with one rendered face and return what it said.
[[nodiscard]] inline checker_return cross_checker(
    const rendered_source& source,
    const char* source_path,
    const char* produced_path,
    const char* out_path,
    const char* error_path,
    const char* working_directory,
    const char* toolchain_path,
    const char* manifest_path,
    const char* source_root) noexcept {
  checker_return returned{};
  holonics::apparatus::lean_source_view view{};
  view.passage = holonics::exact::word{1};
  view.generated_source = holonics::exact::word{1};
  view.bytes = source.bytes;
  view.byte_count = source.extent;
  holonics::event::checker_outbound_occurrence outbound{};
  outbound.occurrence = holonics::exact::word{1};
  outbound.passage = holonics::exact::word{1};
  outbound.source = holonics::exact::word{1};
  holonics::apparatus::lean_process_configuration configuration{};
  configuration.working_directory = working_directory;
  configuration.toolchain_path = toolchain_path;
  configuration.lake_manifest_path = manifest_path;
  configuration.source_root = source_root;
  configuration.source_path = source_path;
  configuration.produced_artifact_path = produced_path;
  configuration.stdout_path = out_path;
  configuration.stderr_path = error_path;
  holonics::event::checker_raw_return raw{};
  const auto receipt =
      holonics::apparatus::run_lean_checker_source(view, outbound, configuration, raw);
  returned.artifact_octets = receipt.produced_artifact_bytes.value();
  returned.accepted = receipt.returned() && returned.artifact_octets != 0;
  return returned;
}

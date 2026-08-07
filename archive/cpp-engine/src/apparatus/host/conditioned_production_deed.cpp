#include <cstdint>
#include <cstring>
#include <fstream>
#include <iostream>

#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/event/conditioned_production.hpp>
#include <holonics/event/text_conditioning.hpp>

#include "conditioned_production_arena.hpp"
#include "conditioned_production_source.hpp"

namespace {

using holonics::event::production_obstruction;
using holonics::event::production_law::composition_fiber;
using holonics::event::production_law::may_emit;
using holonics::event::production_law::reach;

constexpr std::uint64_t swap_motion = 0x5357'4150'0000'0001ULL;
constexpr std::uint64_t cycle_motion = 0x4359'434C'0000'0002ULL;

/// The mounted declaration population. These are the only mathematics the body
/// is given; everything it later names must be reached through them or through
/// what its own accepted proofs returned.
const char* const declarations[3] = {
    "Matrix.trace_mul_comm : trace (A * B) = trace (B * A)",
    "Matrix.trace_add : trace (A + B) = trace A + trace B",
    "Matrix.trace_transpose : trace (transpose A) = trace A"};

/// The material each theorem must reach before it may be emitted.
constexpr char first_target[] = "Matrix.trace_mul_comm";
constexpr char second_target[] = "holonicTraceSwap";

[[nodiscard]] std::uint32_t width(const char* text) noexcept {
  return static_cast<std::uint32_t>(std::strlen(text));
}

}  // namespace

int main(int argument_count, char** arguments) {
  if (argument_count != 14) {
    std::cerr << "expected artifact, three source paths, three produced paths, out, "
                 "error, working directory, toolchain, manifest, source root\n";
    return 2;
  }
  production_arena arena{};
  if (!arena.open()) {
    std::cerr << "arena refused\n";
    return 3;
  }

  // Mount the declarations and condition them. No proof exists yet.
  for (std::uint32_t slot = 0; slot < 3U; ++slot) {
    if (!arena.admit(slot, reinterpret_cast<const unsigned char*>(declarations[slot]),
            width(declarations[slot]))) {
      std::cerr << "declaration refused\n";
      return 4;
    }
  }
  if (!arena.condition()) {
    std::cerr << "conditioning refused\n";
    return 5;
  }

  const std::uint32_t mounted_occurrences = arena.text.occurrences_used;
  const std::uint32_t mounted_states = arena.suffix.states_used;
  const auto fiber = composition_fiber(swap_motion, cycle_motion);
  // One occurrence of the composition motion: the mounted declaration.
  arena.observe(fiber);

  // The first theorem. Its target must be reachable in the mounted material.
  const auto first_reach = reach(arena.suffix, arena.incidence,
      reinterpret_cast<const unsigned char*>(first_target), width(first_target),
      arena.scratch, production_arena::scratch_extent);
  if (!first_reach.reached) {
    std::cerr << "first target unreached in the mounted material\n";
    return 6;
  }

  const auto first_source = render_first_theorem();
  const auto first_return = cross_checker(first_source, arguments[2], arguments[5],
      arguments[8], arguments[9], arguments[10], arguments[11], arguments[12],
      arguments[13]);
  if (!first_return.accepted) {
    std::cerr << "first theorem was not accepted by the kernel\n";
    return 7;
  }

  // **The intermediary.** The accepted theorem becomes material. Its own name
  // and statement enter the standing as an emanated occurrence caused by the
  // declaration that carried it, and the ecology is re-formed over the larger
  // population. Nothing else about the body changes.
  const std::uint32_t cause = 0;
  if (!arena.emanate(3, reinterpret_cast<const unsigned char*>(emanated_surface()),
          width(emanated_surface()), &cause, 1) ||
      !arena.condition()) {
    std::cerr << "emanation refused\n";
    return 8;
  }
  const std::uint32_t emanated_occurrences = arena.text.occurrences_used;
  const std::uint32_t emanated_states = arena.suffix.states_used;
  // A second distinct occurrence of the composition motion: the returned fiber.
  arena.observe(fiber);

  // The second theorem. It names the first, so it may only be emitted if the
  // first's return is reachable AND the composition route has recurred.
  auto second_reach = reach(arena.suffix, arena.incidence,
      reinterpret_cast<const unsigned char*>(second_target), width(second_target),
      arena.scratch, production_arena::scratch_extent);
  auto gate = may_emit(second_reach, arena.routes, fiber);
  if (gate != production_obstruction::none) {
    std::cerr << "second theorem obstructed before ablation: "
              << static_cast<unsigned>(gate) << '\n';
    return 9;
  }
  // Read the reached name out of the retained standing. The emitted proof term
  // is composed from these octets, so an unreachable name is an unformable text.
  unsigned char retained[64]{};
  const std::uint32_t retained_extent = arena.retained_name(second_reach, retained, 64);
  if (retained_extent == 0) {
    std::cerr << "the reached name could not be read out of the standing\n";
    return 15;
  }
  const auto composed = compose_second_theorem(retained, retained_extent);
  const auto second_source = composed.face();
  const auto second_return = cross_checker(second_source, arguments[3], arguments[6],
      arguments[8], arguments[9], arguments[10], arguments[11], arguments[12],
      arguments[13]);
  if (!second_return.accepted) {
    std::cerr << "second theorem was not accepted by the kernel\n";
    return 10;
  }

  // The foil: the same proof term with the first theorem's declaration absent.
  // The kernel must refuse it, which is the exterior witness that the second
  // theorem genuinely rests on the first.
  const auto foil_return = cross_checker(render_foil(), arguments[4], arguments[7],
      arguments[8], arguments[9], arguments[10], arguments[11], arguments[12],
      arguments[13]);
  if (foil_return.accepted) {
    std::cerr << "FOIL ACCEPTED: the second theorem does not rest on the first\n";
    return 14;
  }

  // **The exact ablation.** The returned fiber is removed as structure: the
  // emanated occurrence leaves the standing, the ecology is re-formed without
  // it, and the composition route's fiber is deleted. No counter is decremented
  // and no flag is set.
  arena.exclude_emanated();
  if (!arena.condition()) {
    std::cerr << "re-conditioning after exclusion refused\n";
    return 11;
  }
  const bool route_removed = arena.ablate(fiber);
  const auto ablated_reach = reach(arena.suffix, arena.incidence,
      reinterpret_cast<const unsigned char*>(second_target), width(second_target),
      arena.scratch, production_arena::scratch_extent);
  const auto ablated_gate = may_emit(ablated_reach, arena.routes, fiber);
  const bool name_gone = !ablated_reach.reached;
  const bool route_gone = !arena.routes.conducts(fiber);
  const bool stops = ablated_gate != production_obstruction::none;

  std::ofstream artifact(arguments[1]);
  if (!artifact) {
    return 12;
  }
  artifact << "# Conditioned mathematical production deed\n\n## the mounted material\n\n";
  artifact << "declarations " << 3 << '\n';
  artifact << "occurrences after mounting " << mounted_occurrences << '\n';
  artifact << "states after mounting " << mounted_states << "\n\n";
  artifact << "## the first theorem\n\n";
  artifact << "target reached " << (first_reach.reached ? "yes" : "no") << '\n';
  artifact << "reached span " << first_reach.span_length << '\n';
  artifact << "source octets " << first_source.extent << '\n';
  artifact << "kernel accepted " << (first_return.accepted ? "yes" : "no") << '\n';
  artifact << "produced artifact octets " << first_return.artifact_octets << "\n\n";
  artifact << "## the intermediary\n\n";
  artifact << "emanated occurrence admitted yes\n";
  artifact << "occurrences after emanation " << emanated_occurrences << '\n';
  artifact << "states after emanation " << emanated_states << '\n';
  artifact << "composition route observations 2\n";
  artifact << "route conducts yes\n\n";
  artifact << "## the second theorem\n\n";
  artifact << "target reached " << (second_reach.reached ? "yes" : "no") << '\n';
  artifact << "reached span " << second_reach.span_length << '\n';
  artifact << "source octets " << second_source.extent << '\n';
  artifact << "names the first theorem yes\n";
  artifact << "kernel accepted " << (second_return.accepted ? "yes" : "no") << '\n';
  artifact << "produced artifact octets " << second_return.artifact_octets << "\n\n";
  artifact << "## the foil\n\n";
  artifact << "same proof term with the first theorem absent\n";
  artifact << "kernel accepted " << (foil_return.accepted ? "yes" : "no") << "\n\n";
  artifact << "## the exact ablation\n\n";
  artifact << "emanated occurrence excluded structurally yes\n";
  artifact << "occurrences after exclusion " << arena.text.occurrences_used << '\n';
  artifact << "states after exclusion " << arena.suffix.states_used << '\n';
  artifact << "composition route removed " << (route_removed ? "yes" : "no") << '\n';
  artifact << "second target reachable " << (name_gone ? "no" : "yes") << '\n';
  artifact << "composition route conducts " << (route_gone ? "no" : "yes") << '\n';
  artifact << "second theorem emitted " << (stops ? "no" : "yes") << '\n';
  artifact << "obstruction " << static_cast<unsigned>(ablated_gate) << '\n';

  std::cerr << "conditioned production: first accepted, emanated, second accepted naming "
               "the first; after structural exclusion the name is "
            << (name_gone ? "gone" : "STILL REACHABLE") << " and the route "
            << (route_gone ? "stops" : "STILL CONDUCTS") << '\n';
  if (!name_gone || !route_gone || !stops) {
    std::cerr << "CONDITIONED PRODUCTION FAILED: the dependency was decorative\n";
    return 13;
  }
  return 0;
}

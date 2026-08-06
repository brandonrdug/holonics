#include <cstdint>
#include <fstream>
#include <iostream>
#include <ostream>

#include <holonics/apparatus/resident_ecology_executor.hpp>

#include "ecology_cases.hpp"

namespace {

/// The declared aperture of the phase 7 movement 2 mount. It is chosen to be far past
/// anything a kernel frame could carry: the ecology is tens of megabytes and
/// the default per-thread stack is one kilobyte.
///
/// The germ alphabet is held fixed while the informant-path population doubles,
/// so the second mount is the falsifier of the remaining fan-out term: a cost
/// that grows with the corpus would raise the work per symbol, while a cost set
/// by the declared alphabet does not.
constexpr holonics::apparatus::resident_mount_request declared_mount(
    std::uint32_t sources) noexcept {
  return holonics::apparatus::resident_mount_request{
      sources,  // informant paths
      12,       // germs per path
      128000,   // state capacity
      600000,   // transition capacity
      64000,    // occurrence capacity
      1024};    // device-answered query paths
}

void report(
    std::ostream& out,
    const char* title,
    const holonics::apparatus::resident_mount_request& request,
    const holonics::apparatus::resident_mount_receipt& mount) {
  out << "### " << title << "\n\n";
  out << "informant paths " << request.sources << '\n';
  out << "germs per path " << request.path_length << '\n';
  out << "states " << mount.states << '\n';
  out << "transitions " << mount.transitions << '\n';
  out << "caused occurrences " << mount.occurrences << '\n';
  out << "ordered sources " << mount.ordered << '\n';
  out << "formation steps " << mount.formation_steps << '\n';
  out << "lookup steps " << mount.lookup_steps << '\n';
  out << "resident octets " << mount.resident_octets << '\n';
  out << "frame octets " << mount.frame_octets << '\n';
  out << "device answered queries " << mount.device_queries << '\n';
  out << "parity failures " << mount.parity_failures << '\n';
  out << "host replay work " << mount.host_replay_work << '\n';
  out << "standing unchanged " << (mount.standing_unchanged ? "yes" : "no") << "\n\n";
}

}  // namespace

int main(int argument_count, char** arguments) {
  if (argument_count != 2) {
    std::cerr << "expected one resident mount artifact path\n";
    return 2;
  }
  const auto cost = holonics::tests::suffix_cost_law();
  const auto narrow_request = declared_mount(2000);
  const auto request = declared_mount(4000);
  const auto narrow = holonics::apparatus::mount_resident_ecology(narrow_request);
  const auto mount = holonics::apparatus::mount_resident_ecology(request);
  if (!narrow.returned() || !mount.returned()) {
    std::cerr << "resident mount returned obstruction "
              << static_cast<unsigned>(mount.state) << '\n';
    return 3;
  }
  // The corpus doubles under a fixed germ alphabet. A fan-out cost that grew
  // with the corpus would quadruple the total; one set by the alphabet doubles.
  const bool lookup_corpus_linear = mount.lookup_steps <= 3U * narrow.lookup_steps;
  const bool formation_corpus_linear = mount.formation_steps <= 3U * narrow.formation_steps;

  std::ofstream artifact(arguments[1]);
  if (!artifact) {
    std::cerr << "cannot open resident mount artifact\n";
    return 4;
  }
  artifact << "# Phase 7 resident mount deed\n\n";
  artifact << "## movement 1: the cost law, measured across a quadrupled aperture\n\n";
  artifact << "symbols " << cost.small_symbols << " -> " << cost.large_symbols << '\n';
  artifact << "states " << cost.small_states << " -> " << cost.large_states << '\n';
  artifact << "formation steps " << cost.small_formation << " -> "
           << cost.large_formation << '\n';
  artifact << "lookup steps " << cost.small_lookup << " -> " << cost.large_lookup << '\n';
  artifact << "formation linear " << (cost.formation_linear ? "yes" : "no") << '\n';
  artifact << "lookup linear " << (cost.lookup_linear ? "yes" : "no") << "\n\n";
  artifact << "## movement 2: the arena crossing\n\n";
  report(artifact, "narrow aperture", narrow_request, narrow);
  report(artifact, "declared aperture", request, mount);
  artifact << "### the corpus scaling law\n\n";
  artifact << "the germ alphabet is fixed; the informant-path population doubles\n";
  artifact << "formation corpus-linear " << (formation_corpus_linear ? "yes" : "no")
           << '\n';
  artifact << "lookup corpus-linear " << (lookup_corpus_linear ? "yes" : "no") << '\n';
  artifact << "device capability " << mount.device_major << '.' << mount.device_minor
           << '\n';

  std::cerr << "phase 7 movement 1 cost law: formation " << cost.small_formation << " -> "
            << cost.large_formation << "; lookup " << cost.small_lookup << " -> "
            << cost.large_lookup << '\n';
  std::cerr << "phase 7 movement 2 arena crossing: " << mount.states << " states, "
            << mount.transitions << " transitions, " << mount.occurrences
            << " occurrences; " << mount.resident_octets << " resident octets against "
            << mount.frame_octets << " frame octets; " << mount.device_queries
            << " device queries, " << mount.parity_failures << " parity failures\n";
  std::cerr << "phase 7 movement 2 corpus scaling: doubling the corpus took formation "
            << narrow.formation_steps << " -> " << mount.formation_steps << ", lookup "
            << narrow.lookup_steps << " -> " << mount.lookup_steps << '\n';
  if (!cost.holds) {
    std::cerr << "PHASE 7 MOVEMENT 1 COST LAW FAILED\n";
    return 5;
  }
  if (!mount.holds() || !narrow.holds()) {
    std::cerr << "PHASE 7 MOVEMENT 2 MOUNT FAILED: parity=" << mount.parity_failures
              << " replay=" << mount.host_replay_work
              << " unchanged=" << mount.standing_unchanged << '\n';
    return 6;
  }
  if (!formation_corpus_linear || !lookup_corpus_linear) {
    std::cerr << "PHASE 7 MOVEMENT 2 CORPUS SCALING FAILED: formation="
              << formation_corpus_linear << " lookup=" << lookup_corpus_linear << '\n';
    return 7;
  }
  return 0;
}

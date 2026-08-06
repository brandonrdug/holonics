#include <algorithm>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>

#include <holonics/apparatus/text_material_mount.hpp>

namespace {

constexpr std::uint32_t container_budget = 4096;
constexpr std::uint32_t section_budget = 131072;
constexpr std::uint32_t surface_budget = 12582912;

/// The exterior codec. Containers and their splitting are the apparatus's
/// business entirely: the interior receives octets, a container ordinal, and a
/// section ordinal, and never a path, a name, or a directory.
struct corpus final {
  unsigned char* octets{};
  holonics::apparatus::text_section* sections{};
  std::uint32_t section_count{};
  std::uint32_t container_count{};
  std::uint32_t used{};
};

/// Split one container's octets on blank lines. A section is a maximal run of
/// non-empty material; empty runs are separators, not occurrences.
void split(corpus& held, std::uint32_t container, const std::string& body) {
  std::uint32_t at = 0;
  std::uint32_t section = 0;
  const std::uint32_t extent = static_cast<std::uint32_t>(body.size());
  while (at < extent && held.section_count < section_budget) {
    while (at < extent && (body[at] == '\n' || body[at] == '\r' ||
               body[at] == ' ' || body[at] == '\t')) {
      ++at;
    }
    if (at >= extent) {
      break;
    }
    const std::uint32_t start = at;
    std::uint32_t blank = 0;
    while (at < extent && blank < 2) {
      blank = body[at] == '\n' ? blank + 1U : (body[at] == '\r' || body[at] == ' ' ||
                                                      body[at] == '\t'
                                                  ? blank
                                                  : 0U);
      ++at;
    }
    std::uint32_t stop = at;
    while (stop > start && (body[stop - 1U] == '\n' || body[stop - 1U] == '\r' ||
                               body[stop - 1U] == ' ' || body[stop - 1U] == '\t')) {
      --stop;
    }
    const std::uint32_t width = stop - start;
    if (width == 0 || held.used + width > surface_budget) {
      continue;
    }
    for (std::uint32_t slot = 0; slot < width; ++slot) {
      held.octets[held.used + slot] = static_cast<unsigned char>(body[start + slot]);
    }
    held.sections[held.section_count] = holonics::apparatus::text_section{
        container, section, held.octets + held.used, width};
    held.used = held.used + width;
    held.section_count = held.section_count + 1U;
    section = section + 1U;
  }
}

/// Gather every markdown container under the declared root, in a stable order
/// so that section identities are non-decreasing and remain so across runs.
void gather(corpus& held, const char* root) {
  std::string* names = new std::string[container_budget];
  std::uint32_t found = 0;
  std::error_code failure{};
  for (auto walk = std::filesystem::recursive_directory_iterator(root, failure);
       walk != std::filesystem::recursive_directory_iterator(); walk.increment(failure)) {
    if (failure) {
      break;
    }
    const auto& entry = walk->path();
    const std::string text = entry.string();
    if (text.find("/build") != std::string::npos ||
        text.find("/.git") != std::string::npos) {
      continue;
    }
    if (entry.extension() == ".md" && found < container_budget) {
      names[found] = text;
      ++found;
    }
  }
  std::sort(names, names + found);
  for (std::uint32_t slot = 0; slot < found; ++slot) {
    std::ifstream reader(names[slot], std::ios::binary);
    if (!reader) {
      continue;
    }
    const std::string body((std::istreambuf_iterator<char>(reader)),
        std::istreambuf_iterator<char>());
    split(held, slot, body);
  }
  held.container_count = found;
  delete[] names;
}

/// The declared plurality control.
///
/// The corpus itself carries no repeated section and no revised surface, so
/// without this the duplicate and version laws would be implemented and never
/// exercised. Three sections at one native identity: the same surface twice,
/// then a different one. The first repeat must become multiplicity and the
/// change must found a version fiber with its predecessor still readable.
void control(corpus& held) {
  const char* surfaces[3] = {"holonic control surface", "holonic control surface",
      "holonic control surface revised"};
  for (std::uint32_t slot = 0; slot < 3U; ++slot) {
    const std::uint32_t width = static_cast<std::uint32_t>(std::string(surfaces[slot]).size());
    if (held.used + width > surface_budget || held.section_count >= section_budget) {
      return;
    }
    for (std::uint32_t octet = 0; octet < width; ++octet) {
      held.octets[held.used + octet] = static_cast<unsigned char>(surfaces[slot][octet]);
    }
    held.sections[held.section_count] = holonics::apparatus::text_section{
        held.container_count, 0, held.octets + held.used, width};
    held.used = held.used + width;
    held.section_count = held.section_count + 1U;
  }
}

}  // namespace

int main(int argument_count, char** arguments) {
  if (argument_count != 3) {
    std::cerr << "expected a corpus root and one artifact path\n";
    return 2;
  }
  corpus held{};
  held.octets = new unsigned char[surface_budget];
  held.sections = new holonics::apparatus::text_section[section_budget];
  gather(held, arguments[1]);
  control(held);
  if (held.section_count == 0) {
    std::cerr << "corpus root yielded no sections\n";
    return 3;
  }

  holonics::apparatus::text_mount_request request{};
  request.sections = held.sections;
  request.section_count = held.section_count;
  request.containers = held.container_count;
  request.surface_capacity = held.used + 4096U;
  request.occurrence_capacity = held.section_count + 16U;
  request.caused_capacity = 4096;
  request.state_capacity = 5000000;
  request.transition_capacity = 12000000;
  request.incidence_capacity = 2400000;
  request.octet_aperture = 64;
  request.query_paths = 1024;

  const auto mount = holonics::apparatus::mount_text_material(request);
  if (!mount.returned()) {
    std::cerr << "broad mount returned obstruction "
              << static_cast<unsigned>(mount.state) << '\n';
    return 4;
  }

  std::ofstream artifact(arguments[2]);
  if (!artifact) {
    std::cerr << "cannot open broad mount artifact\n";
    return 5;
  }
  artifact << "# phase 7 movement 3 broad mount deed\n\n## the corpus\n\n";
  artifact << "containers " << mount.containers << '\n';
  artifact << "occurrences " << mount.occurrences << '\n';
  artifact << "surface octets " << mount.surface_octets << '\n';
  artifact << "duplicate witnesses " << mount.duplicate_witnesses
           << " (declared control)\n";
  artifact << "version fibers " << mount.version_fibers << " (declared control)\n";
  artifact << "open causal fibers " << mount.open_causal_fibers << "\n\n";
  artifact << "## the conditioning\n\n";
  artifact << "octet aperture " << request.octet_aperture << '\n';
  artifact << "octets crossed " << mount.octets_crossed << '\n';
  artifact << "states " << mount.states << '\n';
  artifact << "transitions " << mount.transitions << '\n';
  artifact << "caused occurrences admitted " << mount.caused_admitted << '\n';
  artifact << "formation steps " << mount.formation_steps << '\n';
  artifact << "lookup steps " << mount.lookup_steps << '\n';
  artifact << "resident octets " << mount.resident_octets << '\n';
  artifact << "frame octets " << mount.frame_octets << "\n\n";
  artifact << "## the admission gates\n\n";
  artifact << "global pair population " << mount.global_pair_population << '\n';
  artifact << "hot host replay work " << mount.hot_host_replay_work << '\n';
  artifact << "bounded delta equal " << (mount.bounded_delta_equal ? "yes" : "no")
           << "\n\n## rest and remount\n\n";
  artifact << "rest octets " << mount.rest_octets << '\n';
  artifact << "remount octets " << mount.remount_octets << '\n';
  artifact << "founded from octets alone "
           << (mount.remount_founded_from_octets_alone ? "yes" : "no") << '\n';
  artifact << "remount exact " << (mount.remount_exact ? "yes" : "no")
           << "\n\n## ownership\n\n";
  artifact << "mount consumed host " << (mount.mount_consumed_host ? "yes" : "no") << '\n';
  artifact << "consumed host refuses admission "
           << (mount.consumed_host_refuses_admission ? "yes" : "no") << '\n';
  artifact << "refusal returned predecessor "
           << (mount.refusal_returned_predecessor ? "yes" : "no") << "\n\n";
  artifact << "## the resident query\n\n";
  artifact << "device answered queries " << mount.device_queries << '\n';
  artifact << "parity failures " << mount.parity_failures << '\n';
  artifact << "device capability " << mount.device_major << '.' << mount.device_minor
           << '\n';

  std::cerr << "phase 7 movement 3 broad mount: " << mount.containers << " containers, "
            << mount.occurrences << " occurrences, " << mount.surface_octets
            << " surface octets; " << mount.states << " states, " << mount.transitions
            << " transitions from " << mount.octets_crossed << " crossed octets\n";
  std::cerr << "phase 7 movement 3 gates: pair population " << mount.global_pair_population
            << ", replay work " << mount.hot_host_replay_work << ", bounded delta "
            << (mount.bounded_delta_equal ? "equal" : "unequal") << ", remount "
            << (mount.remount_exact ? "exact" : "inexact") << ", parity failures "
            << mount.parity_failures << '\n';
  delete[] held.octets;
  delete[] held.sections;
  if (!mount.holds()) {
    std::cerr << "PHASE 7 MOVEMENT 3 BROAD MOUNT FAILED\n";
    return 6;
  }
  return 0;
}

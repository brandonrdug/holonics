#include <array>
#include <cstddef>
#include <fstream>
#include <iostream>

#include <holonics/apparatus/spine_executor.hpp>

#include "spine_cases.hpp"

namespace {

const char* disposition_name(std::uint8_t value) {
  switch (value) {
    case 0: return "ride";
    case 1: return "found";
    case 2: return "open";
    case 3: return "holonomy";
    default: return "unknown";
  }
}

const char* refusal_name(std::uint8_t value) {
  switch (value) {
    case 0: return "available";
    case 1: return "chart-undeclared";
    case 2: return "not-parallel";
    case 3: return "unadmitted";
    default: return "unknown";
  }
}

}  // namespace

int main(int argument_count, char** arguments) {
  if (argument_count != 2) {
    std::cerr << "expected one spine artifact path\n";
    return 2;
  }
  const auto inputs = holonics::tests::spine_cases();
  const auto names = holonics::tests::spine_case_names();
  std::array<holonics::exact::spine_deed_output, holonics::tests::spine_case_count> device{};
  std::array<holonics::exact::spine_deed_output, holonics::tests::spine_case_count> host{};

  const auto execution = holonics::apparatus::execute_spine_deeds(
      holonics::apparatus::spine_deed_batch{inputs.data(), device.data(), inputs.size()});
  if (!execution.returned()) {
    std::cerr << "device executor returned obstruction "
              << static_cast<unsigned>(execution.state) << '\n';
    return 3;
  }

  std::size_t parity_failures = 0;
  for (std::size_t slot = 0; slot < inputs.size(); ++slot) {
    host[slot] = holonics::body::execute_spine_deed(inputs[slot]);
    if (!holonics::exact::spine_deed_law::equal(device[slot], host[slot])) {
      ++parity_failures;
    }
  }
  const bool swing = holonics::tests::swing_laws_hold(device);
  const bool sharing = holonics::tests::standing_shares_rather_than_copies(device);
  const bool open_law = holonics::tests::open_never_concludes(device);
  const bool carrier = holonics::tests::carrier_laws_hold();
  const bool substrate = holonics::tests::substrate_laws_hold();
  const bool information = holonics::tests::information_laws_hold();

  std::ofstream artifact{arguments[1], std::ios::trunc};
  if (!artifact) {
    std::cerr << "could not open spine artifact\n";
    return 4;
  }
  artifact << "phases=0-5 minimum-carrier-substrate-swing-standing-machine-receipt\n";
  artifact << "grade=established-bounded\n";
  artifact << "evidence=implemented-exact\n";
  artifact << "device_compute=" << execution.device_major << '.' << execution.device_minor << '\n';
  artifact << "bytes_to_device=" << execution.bytes_to_device.value() << '\n';
  artifact << "bytes_from_device=" << execution.bytes_from_device.value() << '\n';
  artifact << "launched_threads=" << execution.launched_threads.value() << '\n';
  artifact << "occurrences=" << inputs.size() << '\n';
  artifact << "device_host_parity_failures=" << parity_failures << '\n';
  artifact << "swing_laws=" << (swing ? 1 : 0) << '\n';
  artifact << "standing_shares=" << (sharing ? 1 : 0) << '\n';
  artifact << "open_never_concludes=" << (open_law ? 1 : 0) << '\n';
  artifact << "carrier_laws=" << (carrier ? 1 : 0) << '\n';
  artifact << "substrate_laws=" << (substrate ? 1 : 0) << '\n';
  artifact << "information_laws=" << (information ? 1 : 0) << '\n';
  for (std::size_t slot = 0; slot < inputs.size(); ++slot) {
    artifact << "case=" << names[slot] << '\n';
    artifact << "  disposition=" << disposition_name(device[slot].disposition)
             << " refusal=" << refusal_name(device[slot].refusal_state)
             << " winding=" << device[slot].winding
             << " groove_rebased=" << (device[slot].groove_rebased ? 1 : 0) << '\n';
    artifact << "  retains_pair=" << (device[slot].retains_pair ? 1 : 0)
             << " may_conclude=" << (device[slot].may_conclude ? 1 : 0)
             << " grade=" << static_cast<unsigned>(device[slot].grade_satisfied) << '\n';
    artifact << "  standing_population=" << device[slot].population_before << "->"
             << device[slot].population_after << " path_copied=" << device[slot].path_copied
             << " nodes=" << device[slot].standing_nodes << '\n';
  }
  artifact.flush();

  if (parity_failures != 0 || !swing || !sharing || !open_law || !carrier || !substrate ||
      !information) {
    std::cerr << "spine deed failed its named laws\n";
    return 5;
  }
  return 0;
}

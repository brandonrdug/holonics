#include <array>
#include <cstddef>
#include <fstream>
#include <iostream>

#include <holonics/apparatus/enclosure_executor.hpp>

#include "enclosure_cases.hpp"

namespace {

using holonics::exact::commitment_ground;
using holonics::exact::enclosure_deed_output;
using holonics::exact::enclosure_state;
using holonics::exact::sign_commitment;

const char* commitment_name(sign_commitment value) {
  switch (value) {
    case sign_commitment::refused: return "refused";
    case sign_commitment::negative: return "negative";
    case sign_commitment::zero: return "zero";
    case sign_commitment::positive: return "positive";
  }
  return "unknown";
}

const char* ground_name(commitment_ground ground) {
  switch (ground) {
    case commitment_ground::strict_endpoint: return "strict-endpoint";
    case commitment_ground::certified_zero: return "certified-zero";
    case commitment_ground::separation_absent: return "separation-absent";
    case commitment_ground::separation_insufficient: return "separation-insufficient";
    case commitment_ground::source_contradiction: return "source-contradiction";
    case commitment_ground::certificate_underived: return "certificate-underived";
    case commitment_ground::enclosure_disordered: return "enclosure-disordered";
  }
  return "unknown";
}

const char* refinement_name(enclosure_state state) {
  switch (state) {
    case enclosure_state::admitted: return "admitted";
    case enclosure_state::aperture_refused: return "aperture-refused";
    case enclosure_state::bracket_absent: return "bracket-absent";
    case enclosure_state::order_refused: return "order-refused";
  }
  return "unknown";
}

void write_return(
    std::ostream& artifact,
    std::string_view name,
    const enclosure_deed_output& output) {
  artifact << "case=" << name << '\n';
  artifact << "  enclosure_lower=" << output.refined.lower.numerator << "/2^"
           << static_cast<unsigned>(output.refined.lower.exponent) << '\n';
  artifact << "  enclosure_upper=" << output.refined.upper.numerator << "/2^"
           << static_cast<unsigned>(output.refined.upper.exponent) << '\n';
  artifact << "  refinement=" << refinement_name(output.refinement_state)
           << " reached_exponent=" << static_cast<unsigned>(output.reached_exponent)
           << " bracketed=" << (output.bracketed ? 1 : 0) << '\n';
  artifact << "  separation=" << output.certificate.numerator << '/'
           << output.certificate.denominator
           << " derived=" << (output.certificate.derived ? 1 : 0)
           << " admits_zero=" << (output.certificate.admits_zero ? 1 : 0)
           << " revalidates=" << (output.certificate_revalidates ? 1 : 0) << '\n';
  artifact << "  commitment=" << commitment_name(output.committed.value)
           << " ground=" << ground_name(output.committed.ground)
           << " certificate_consulted=" << (output.committed.certificate_consulted ? 1 : 0)
           << '\n';
}

}  // namespace

int main(int argument_count, char** arguments) {
  if (argument_count != 2) {
    std::cerr << "expected one certified-enclosure artifact path\n";
    return 2;
  }

  const auto inputs = holonics::tests::enclosure_cases();
  const auto names = holonics::tests::enclosure_case_names();
  std::array<enclosure_deed_output, holonics::tests::enclosure_case_count> device_returns{};
  std::array<enclosure_deed_output, holonics::tests::enclosure_case_count> host_returns{};

  const auto execution = holonics::apparatus::execute_enclosure_deeds(
      holonics::apparatus::enclosure_deed_batch{
          inputs.data(), device_returns.data(), inputs.size()});
  if (!execution.returned()) {
    std::cerr << "device executor returned obstruction "
              << static_cast<unsigned>(execution.state) << '\n';
    return 3;
  }

  std::size_t parity_failures = 0;
  std::size_t oracle_failures = 0;
  for (std::size_t slot = 0; slot < inputs.size(); ++slot) {
    host_returns[slot] = holonics::exact::execute_enclosure_deed(inputs[slot]);
    if (!holonics::exact::enclosure_deed_law::equal(device_returns[slot], host_returns[slot])) {
      ++parity_failures;
    }
    if (!holonics::tests::independent_enclosure_agrees(inputs[slot], device_returns[slot])) {
      ++oracle_failures;
    }
  }

  const bool named = holonics::tests::certified_enclosure_returns(device_returns);
  const bool ablation = holonics::tests::certificate_ablation_holds(device_returns);
  const bool aperture = holonics::tests::aperture_refusal_holds(device_returns);

  std::ofstream artifact{arguments[1], std::ios::trunc};
  if (!artifact) {
    std::cerr << "could not open certified-enclosure artifact\n";
    return 4;
  }
  artifact << "movement=A certified-exact-enclosure-carrier\n";
  artifact << "grade=established-bounded\n";
  artifact << "evidence=implemented-exact\n";
  artifact << "device_compute=" << execution.device_major << '.' << execution.device_minor
           << '\n';
  artifact << "bytes_to_device=" << execution.bytes_to_device.value() << '\n';
  artifact << "bytes_from_device=" << execution.bytes_from_device.value() << '\n';
  artifact << "launched_threads=" << execution.launched_threads.value() << '\n';
  artifact << "occurrences=" << inputs.size() << '\n';
  artifact << "device_host_parity_failures=" << parity_failures << '\n';
  artifact << "independent_oracle_failures=" << oracle_failures << '\n';
  artifact << "named_returns=" << (named ? 1 : 0) << '\n';
  artifact << "certificate_ablation=" << (ablation ? 1 : 0) << '\n';
  artifact << "aperture_refusal=" << (aperture ? 1 : 0) << '\n';
  for (std::size_t slot = 0; slot < inputs.size(); ++slot) {
    write_return(artifact, names[slot], device_returns[slot]);
  }
  artifact.flush();

  if (parity_failures != 0 || oracle_failures != 0 || !named || !ablation || !aperture) {
    std::cerr << "certified-enclosure deed failed its named returns\n";
    return 5;
  }
  return 0;
}

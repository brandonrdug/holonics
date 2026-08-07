#include "r1_artifact.hpp"

#include <cstddef>
#include <cstdint>
#include <iomanip>
#include <ostream>
#include <string_view>

namespace holonics::tests {
namespace {

[[nodiscard]] std::string_view status_name(exact::status state) {
  using exact::status;
  switch (state) {
    case status::exact: return "exact";
    case status::capacity_refused: return "capacity_refused";
    case status::negative_refused: return "negative_refused";
    case status::divide_by_zero: return "divide_by_zero";
    case status::zero_denominator: return "zero_denominator";
    case status::invalid_modulus: return "invalid_modulus";
    case status::noninvertible: return "noninvertible";
    case status::invalid_projective_pair: return "invalid_projective_pair";
    case status::degree_refused: return "degree_refused";
  }
  return "unknown";
}

void write_integer(std::ostream& stream, const exact::encoded_integer& value) {
  stream << "0x";
  if (value.used == 0) {
    stream << '0';
    return;
  }
  for (std::size_t index = value.used; index != 0; --index) {
    stream << std::hex << std::setw(16) << std::setfill('0') << value.limbs[index - 1];
  }
  stream << std::dec;
}

}  // namespace

void write_r1_artifact(
    std::ostream& stream,
    const apparatus::exact_executor_receipt& execution,
    const r1_output_batch& outputs,
    std::size_t parity_failures,
    std::size_t algebraic_failures,
    std::size_t exact_returns) {
  stream << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness\n"
         << "program=r1_exact_deed_kernel.sm_89\n"
         << "case_aperture=" << outputs.size() << '\n'
         << "device_compute_capability=" << execution.device_major << '.'
         << execution.device_minor << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "oracle_parity_failures=" << parity_failures << '\n'
         << "algebraic_identity_failures=" << algebraic_failures << '\n'
         << "exact_returns_observer_count=" << exact_returns << '\n';
  for (const auto& output : outputs) {
    stream << "case=" << output.case_identity
           << " kind=" << static_cast<unsigned>(output.kind)
           << " status=" << status_name(output.state)
           << " admitted=" << output.admitted_limbs
           << " required=" << output.required_limbs
           << " negative=" << output.negative
           << " relation=" << output.relation
           << " primary=";
    write_integer(stream, output.primary);
    stream << " secondary=";
    write_integer(stream, output.secondary);
    stream << " witness=" << output.witness_hash << " auxiliary=";
    for (const std::uint64_t value : output.auxiliary) {
      stream << value << ',';
    }
    stream << '\n';
  }
}

}  // namespace holonics::tests

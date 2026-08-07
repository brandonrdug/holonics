#include <cstddef>
#include <cstdlib>

#include <holonics/apparatus/returned_theorem_checker_process.hpp>

namespace holonics::apparatus {

lean_process_receipt run_returned_theorem_checker_source(
    const lean_source_view& source,
    const event::checker_outbound_occurrence& outbound,
    const lean_process_configuration& configuration,
    event::checker_raw_return& returned) noexcept {
  lean_process_receipt receipt{};
  if (configuration.source_root == nullptr || configuration.source_root[0] == '\0') {
    return receipt;
  }
  constexpr std::size_t prior_capacity = 4096;
  char prior[prior_capacity]{};
  std::size_t prior_bytes = 0;
  const char* inherited = ::getenv("LEAN_PATH");
  if (inherited != nullptr) {
    while (inherited[prior_bytes] != '\0') {
      if (prior_bytes + 1U >= prior_capacity) {
        receipt.state = lean_process_status::environment_refused;
        return receipt;
      }
      prior[prior_bytes] = inherited[prior_bytes];
      ++prior_bytes;
    }
  }
  if (::setenv("LEAN_PATH", configuration.source_root, 1) != 0) {
    receipt.state = lean_process_status::environment_refused;
    return receipt;
  }
  receipt = run_lean_checker_source(source, outbound, configuration, returned);
  const int restored = inherited == nullptr ? ::unsetenv("LEAN_PATH") :
      ::setenv("LEAN_PATH", prior, 1);
  if (restored != 0) { receipt.state = lean_process_status::environment_refused; }
  return receipt;
}

lean_process_receipt run_returned_theorem_checker_process(
    const codec::formal_checker_face& face,
    const event::checker_outbound_occurrence& outbound,
    const lean_process_configuration& configuration,
    event::checker_raw_return& returned) noexcept {
  if (face.byte_count > codec::formal_checker_face_capacity) { return {}; }
  const lean_source_view source{face.passage, face.generated_source, face.bytes, face.byte_count};
  return run_returned_theorem_checker_source(source, outbound, configuration, returned);
}

}  // namespace holonics::apparatus

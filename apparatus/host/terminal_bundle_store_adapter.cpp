#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/terminal_bundle_store_adapter.hpp>

namespace holonics::apparatus {
namespace {

constexpr std::uint64_t fold_offset = 14'695'981'039'346'656'037ULL;
constexpr std::uint64_t fold_prime = 1'099'511'628'211ULL;

struct artifact_read final {
  std::uint64_t fold{fold_offset};
  std::uint32_t bytes{};
};

[[nodiscard]] terminal_store_status read_artifact(const char* path, char* capture,
    std::size_t capacity, artifact_read& result) noexcept {
  if (path == nullptr || path[0] == '\0') { return terminal_store_status::invalid_aperture; }
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) { return terminal_store_status::open_refused; }
  char buffer[4096]{};
  std::size_t captured = 0;
  for (;;) {
    const auto count = ::read(descriptor, buffer, sizeof(buffer));
    if (count < 0 && errno == EINTR) { continue; }
    if (count < 0) {
      static_cast<void>(::close(descriptor));
      return terminal_store_status::read_refused;
    }
    if (count == 0) { break; }
    const auto amount = static_cast<std::size_t>(count);
    if (result.bytes > UINT32_MAX - amount ||
        (capture != nullptr && captured + amount > capacity)) {
      static_cast<void>(::close(descriptor));
      return terminal_store_status::size_refused;
    }
    for (std::size_t slot = 0; slot < amount; ++slot) {
      const auto octet = static_cast<unsigned char>(buffer[slot]);
      result.fold ^= octet;
      result.fold *= fold_prime;
      if (capture != nullptr) { capture[captured++] = buffer[slot]; }
    }
    result.bytes += static_cast<std::uint32_t>(amount);
  }
  if (::close(descriptor) != 0) { return terminal_store_status::read_refused; }
  return result.bytes == 0 ? terminal_store_status::size_refused : terminal_store_status::returned;
}

}  // namespace

dependent_setup_store_receipt read_dependent_theorem_setup(
    const char* path, event::dependent_theorem_setup& setup) noexcept {
  dependent_setup_store_receipt receipt{};
  if (path == nullptr || path[0] == '\0') { return receipt; }
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) { receipt.state = terminal_store_status::open_refused; return receipt; }
  auto* destination = reinterpret_cast<unsigned char*>(&setup);
  std::size_t received = 0;
  while (received < sizeof(setup)) {
    const auto count = ::read(descriptor, destination + received, sizeof(setup) - received);
    if (count < 0 && errno == EINTR) { continue; }
    if (count <= 0) {
      static_cast<void>(::close(descriptor));
      receipt.state = terminal_store_status::read_refused;
      return receipt;
    }
    received += static_cast<std::size_t>(count);
  }
  unsigned char excess = 0;
  const auto trailing = ::read(descriptor, &excess, 1);
  const bool closed = ::close(descriptor) == 0;
  if (!closed || trailing != 0) {
    receipt.state = terminal_store_status::size_refused;
    return receipt;
  }
  receipt.integrity_exact = setup.integrity == event::dependent_setup_integrity(setup);
  if (!receipt.integrity_exact) {
    receipt.state = terminal_store_status::integrity_refused;
    return receipt;
  }
  receipt.state = terminal_store_status::returned;
  receipt.bytes = exact::word{sizeof(setup)};
  receipt.read_calls = exact::word{1};
  return receipt;
}

terminal_store_status collect_first_return_artifacts(
    const char* deed_path, const char* produced_artifact_path,
    first_return_artifact_testimony& testimony) noexcept {
  artifact_read deed{};
  artifact_read produced{};
  const auto deed_state = read_artifact(
      deed_path, testimony.deed, first_return_artifact_capacity, deed);
  if (deed_state != terminal_store_status::returned) { return deed_state; }
  const auto produced_state = read_artifact(produced_artifact_path, nullptr, 0, produced);
  if (produced_state != terminal_store_status::returned) { return produced_state; }
  testimony.deed_fold = deed.fold;
  testimony.produced_artifact_fold = produced.fold;
  testimony.deed_bytes = deed.bytes;
  testimony.produced_artifact_bytes = produced.bytes;
  testimony.observer_artifact_reads = exact::word{2};
  testimony.exact = true;
  return terminal_store_status::returned;
}

}  // namespace holonics::apparatus

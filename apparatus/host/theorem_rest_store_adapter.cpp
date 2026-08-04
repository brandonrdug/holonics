#include <cerrno>
#include <cstddef>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/theorem_rest_store_adapter.hpp>

namespace holonics::apparatus {

theorem_rest_store_receipt read_theorem_production_rest(
    const char* path, event::theorem_production_rest_record& record) noexcept {
  theorem_rest_store_receipt receipt{};
  if (path == nullptr || path[0] == '\0') { return receipt; }
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) { receipt.state = theorem_rest_store_status::open_refused; return receipt; }
  auto* destination = reinterpret_cast<unsigned char*>(&record);
  std::size_t received = 0;
  while (received < sizeof(record)) {
    const auto count = ::read(descriptor, destination + received, sizeof(record) - received);
    if (count < 0 && errno == EINTR) { continue; }
    if (count <= 0) {
      static_cast<void>(::close(descriptor));
      receipt.state = theorem_rest_store_status::read_refused;
      return receipt;
    }
    received += static_cast<std::size_t>(count);
  }
  unsigned char excess = 0;
  const auto trailing = ::read(descriptor, &excess, 1);
  const bool closed = ::close(descriptor) == 0;
  if (!closed || trailing != 0) { receipt.state = theorem_rest_store_status::size_refused; return receipt; }
  receipt.integrity_exact = record.integrity == event::theorem_production_rest_integrity(record);
  if (!receipt.integrity_exact) {
    receipt.state = theorem_rest_store_status::integrity_refused; return receipt;
  }
  receipt.state = theorem_rest_store_status::returned;
  receipt.bytes = exact::word{sizeof(record)};
  receipt.read_calls = exact::word{1};
  return receipt;
}

}  // namespace holonics::apparatus

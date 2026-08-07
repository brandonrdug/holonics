#include <cerrno>
#include <cstddef>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/toric_cycle_store_adapter.hpp>

namespace holonics::apparatus {
namespace {

template<class Record>
[[nodiscard]] toric_store_status read_exact(const char* path, Record& record) noexcept {
  if (path == nullptr || path[0] == '\0') { return toric_store_status::invalid_aperture; }
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) { return toric_store_status::open_refused; }
  auto* destination = reinterpret_cast<unsigned char*>(&record);
  std::size_t received = 0;
  while (received < sizeof(record)) {
    const auto count = ::read(descriptor, destination + received, sizeof(record) - received);
    if (count < 0 && errno == EINTR) { continue; }
    if (count <= 0) { static_cast<void>(::close(descriptor));
      return toric_store_status::transfer_refused; }
    received += static_cast<std::size_t>(count);
  }
  unsigned char excess = 0; const auto trailing = ::read(descriptor, &excess, 1);
  const bool closed = ::close(descriptor) == 0;
  return closed && trailing == 0 ? toric_store_status::returned :
      toric_store_status::size_refused;
}

template<class Record>
[[nodiscard]] toric_store_status write_exact(const char* path,
    const Record& record) noexcept {
  if (path == nullptr || path[0] == '\0') { return toric_store_status::invalid_aperture; }
  const int descriptor = ::open(path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
  if (descriptor < 0) { return toric_store_status::open_refused; }
  const auto* source = reinterpret_cast<const unsigned char*>(&record);
  std::size_t transferred = 0;
  while (transferred < sizeof(record)) {
    const auto count = ::write(descriptor, source + transferred,
        sizeof(record) - transferred);
    if (count < 0 && errno == EINTR) { continue; }
    if (count <= 0) { static_cast<void>(::close(descriptor));
      return toric_store_status::transfer_refused; }
    transferred += static_cast<std::size_t>(count);
  }
  return ::close(descriptor) == 0 ? toric_store_status::returned :
      toric_store_status::transfer_refused;
}

}  // namespace

toric_store_receipt read_cm_incidence_handoff(
    const char* path, event::cm_incidence_rest_record& record) noexcept {
  toric_store_receipt receipt{}; receipt.state = read_exact(path, record);
  if (receipt.state != toric_store_status::returned) { return receipt; }
  receipt.integrity_exact = record.integrity == event::cm_incidence_rest_integrity(record);
  if (!receipt.integrity_exact) { receipt.state = toric_store_status::integrity_refused;
    return receipt; }
  receipt.bytes = exact::word{sizeof(record)}; receipt.transfer_calls = exact::word{1};
  return receipt;
}

toric_store_receipt write_toric_cycle_handoff(
    const char* path, const event::toric_cycle_rest_record& record) noexcept {
  toric_store_receipt receipt{};
  receipt.integrity_exact = record.integrity == event::toric_cycle_rest_integrity(record);
  if (!receipt.integrity_exact) { receipt.state = toric_store_status::integrity_refused;
    return receipt; }
  receipt.state = write_exact(path, record);
  if (receipt.state == toric_store_status::returned) {
    receipt.bytes = exact::word{sizeof(record)}; receipt.transfer_calls = exact::word{1};
  }
  return receipt;
}

}  // namespace holonics::apparatus

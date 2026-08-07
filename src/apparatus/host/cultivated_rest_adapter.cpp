#include <cerrno>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/cultivated_organ_store_adapter.hpp>

namespace holonics::apparatus {
namespace {
template<class Record>
[[nodiscard]] cultivated_store_receipt transfer_record(
    const char *path, Record &record, bool write) noexcept {
  cultivated_store_receipt receipt{};
  const int descriptor = ::open(path, write ? O_WRONLY | O_CREAT | O_TRUNC : O_RDONLY, 0644);
  if (descriptor < 0) { receipt.state = cultivated_store_status::open_refused; return receipt; }
  auto *bytes = reinterpret_cast<unsigned char *>(&record); std::size_t at = 0; std::uint64_t calls = 0;
  while (at < sizeof(record)) {
    const auto moved = write ? ::write(descriptor, bytes + at, sizeof(record) - at) :
                               ::read(descriptor, bytes + at, sizeof(record) - at);
    if (moved < 0 && errno == EINTR) continue;
    if (moved <= 0) { receipt.state = cultivated_store_status::transfer_refused; break; }
    at += static_cast<std::size_t>(moved); ++calls;
  }
  if (!write && at == sizeof(record)) { char excess{}; if (::read(descriptor, &excess, 1) != 0)
    receipt.state = cultivated_store_status::size_refused; }
  const bool closed = ::close(descriptor) == 0;
  if (at == sizeof(record) && closed && receipt.state != cultivated_store_status::size_refused)
    receipt.state = cultivated_store_status::returned;
  receipt.bytes = exact::word{sizeof(record)}; receipt.transfer_calls = exact::word{calls};
  receipt.integrity_exact = receipt.state == cultivated_store_status::returned &&
      record.integrity == event::cultivated_organ_rest_integrity(record);
  if (!receipt.integrity_exact) receipt.state = cultivated_store_status::transfer_refused;
  return receipt;
}
}  // namespace

cultivated_store_receipt read_cultivated_organ_rest(
    const char *path, event::cultivated_organ_rest_record &record) noexcept {
  return transfer_record(path, record, false);
}

cultivated_store_receipt write_cultivated_organ_rest(
    const char *path, const event::cultivated_organ_rest_record &record) noexcept {
  auto mutable_record = record; return transfer_record(path, mutable_record, true);
}

}  // namespace holonics::apparatus

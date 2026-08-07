#include <cerrno>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/trace_rebase_store_adapter.hpp>

namespace holonics::apparatus {
namespace {
[[nodiscard]] cultivated_store_receipt transfer(
    const char *path, event::trace_rebase_rest_record &record,
    bool write) noexcept {
  cultivated_store_receipt out{};
  const int descriptor =
      ::open(path, write ? O_WRONLY | O_CREAT | O_TRUNC : O_RDONLY, 0644);
  if (descriptor < 0) {
    out.state = cultivated_store_status::open_refused;
    return out;
  }
  auto *bytes = reinterpret_cast<unsigned char *>(&record);
  std::size_t at = 0;
  std::uint64_t calls = 0;
  while (at < sizeof(record)) {
    const auto moved = write ? ::write(descriptor, bytes + at, sizeof(record) - at)
                             : ::read(descriptor, bytes + at, sizeof(record) - at);
    if (moved < 0 && errno == EINTR)
      continue;
    if (moved <= 0) {
      out.state = cultivated_store_status::transfer_refused;
      break;
    }
    at += static_cast<std::size_t>(moved);
    ++calls;
  }
  if (!write && at == sizeof(record)) {
    char excess{};
    if (::read(descriptor, &excess, 1) != 0)
      out.state = cultivated_store_status::size_refused;
  }
  const bool closed = ::close(descriptor) == 0;
  if (at == sizeof(record) && closed &&
      out.state != cultivated_store_status::size_refused)
    out.state = cultivated_store_status::returned;
  out.bytes = exact::word{sizeof(record)};
  out.transfer_calls = exact::word{calls};
  out.integrity_exact = out.state == cultivated_store_status::returned &&
                        record.integrity == event::trace_rebase_rest_integrity(record);
  if (!out.integrity_exact)
    out.state = cultivated_store_status::transfer_refused;
  return out;
}
} // namespace
cultivated_store_receipt read_trace_rebase_rest(
    const char *path, event::trace_rebase_rest_record &record) noexcept {
  return transfer(path, record, false);
}
cultivated_store_receipt write_trace_rebase_rest(
    const char *path, const event::trace_rebase_rest_record &record) noexcept {
  auto value = record;
  return transfer(path, value, true);
}

} // namespace holonics::apparatus

#include <cerrno>
#include <cstddef>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/rederivation_store_adapter.hpp>

namespace holonics::apparatus {
namespace {
[[nodiscard]] rederivation_store_status
transfer(int descriptor, unsigned char *bytes, std::size_t count,
         std::uint64_t &calls) noexcept {
  std::size_t at = 0;
  while (at != count) {
    const auto got = ::read(descriptor, bytes + at, count - at);
    if (got < 0 && errno == EINTR)
      continue;
    if (got <= 0)
      return rederivation_store_status::transfer_refused;
    at += static_cast<std::size_t>(got);
    ++calls;
  }
  char excess = 0;
  return ::read(descriptor, &excess, 1) == 0
             ? rederivation_store_status::returned
             : rederivation_store_status::size_refused;
}
[[nodiscard]] rederivation_store_status
transfer(int descriptor, const unsigned char *bytes, std::size_t count,
         std::uint64_t &calls) noexcept {
  std::size_t at = 0;
  while (at != count) {
    const auto got = ::write(descriptor, bytes + at, count - at);
    if (got < 0 && errno == EINTR)
      continue;
    if (got <= 0)
      return rederivation_store_status::transfer_refused;
    at += static_cast<std::size_t>(got);
    ++calls;
  }
  return rederivation_store_status::returned;
}
template <class Record>
rederivation_store_receipt
read_record(const char *path, Record &record,
            std::uint64_t (*integrity)(const Record &) noexcept) noexcept {
  rederivation_store_receipt receipt{};
  if (path == nullptr || path[0] == '\0')
    return receipt;
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) {
    receipt.state = rederivation_store_status::open_refused;
    return receipt;
  }
  std::uint64_t calls = 0;
  receipt.state =
      transfer(descriptor, reinterpret_cast<unsigned char *>(&record),
               sizeof(record), calls);
  if (::close(descriptor) != 0 &&
      receipt.state == rederivation_store_status::returned)
    receipt.state = rederivation_store_status::transfer_refused;
  receipt.bytes = exact::word{sizeof(record)};
  receipt.transfer_calls = exact::word{calls};
  receipt.integrity_exact =
      receipt.state == rederivation_store_status::returned &&
      record.integrity == integrity(record);
  if (!receipt.integrity_exact)
    receipt.state = rederivation_store_status::transfer_refused;
  return receipt;
}
} // namespace
rederivation_store_receipt read_arithmetic_rederivation_handoff(
    const char *path, event::arithmetic_spectral_rest_record &record) noexcept {
  return read_record(path, record, event::arithmetic_spectral_rest_integrity);
}
rederivation_store_receipt
read_rederivation_handoff(const char *path,
                          event::rederivation_rest_record &record) noexcept {
  return read_record(path, record, event::rederivation_rest_integrity);
}
rederivation_store_receipt write_rederivation_handoff(
    const char *path, const event::rederivation_rest_record &record) noexcept {
  rederivation_store_receipt receipt{};
  if (path == nullptr || path[0] == '\0' ||
      record.integrity != event::rederivation_rest_integrity(record))
    return receipt;
  const int descriptor = ::open(path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
  if (descriptor < 0) {
    receipt.state = rederivation_store_status::open_refused;
    return receipt;
  }
  std::uint64_t calls = 0;
  receipt.state =
      transfer(descriptor, reinterpret_cast<const unsigned char *>(&record),
               sizeof(record), calls);
  if (::close(descriptor) != 0 &&
      receipt.state == rederivation_store_status::returned)
    receipt.state = rederivation_store_status::transfer_refused;
  receipt.bytes = exact::word{sizeof(record)};
  receipt.transfer_calls = exact::word{calls};
  receipt.integrity_exact =
      receipt.state == rederivation_store_status::returned;
  return receipt;
}
} // namespace holonics::apparatus

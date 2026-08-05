#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/arithmetic_spectral_store_adapter.hpp>
#include <holonics/event/arithmetic_spectral_rest.hpp>
#include <holonics/event/hodge_realization_rest.hpp>

namespace holonics::apparatus {
namespace {

[[nodiscard]] arithmetic_store_status write_all(int descriptor, const unsigned char* bytes,
    std::size_t count, std::uint64_t& calls) noexcept {
  std::size_t written = 0;
  while (written != count) {
    const auto result = ::write(descriptor, bytes + written, count - written);
    if (result < 0 && errno == EINTR) { continue; }
    if (result <= 0) { return arithmetic_store_status::transfer_refused; }
    written += static_cast<std::size_t>(result); ++calls;
  }
  return arithmetic_store_status::returned;
}

[[nodiscard]] arithmetic_store_status read_all(int descriptor, unsigned char* bytes,
    std::size_t count, std::uint64_t& calls) noexcept {
  std::size_t read_count = 0;
  while (read_count != count) {
    const auto result = ::read(descriptor, bytes + read_count, count - read_count);
    if (result < 0 && errno == EINTR) { continue; }
    if (result <= 0) { return arithmetic_store_status::transfer_refused; }
    read_count += static_cast<std::size_t>(result); ++calls;
  }
  char excess = 0; const auto trailing = ::read(descriptor, &excess, 1);
  return trailing == 0 ? arithmetic_store_status::returned : arithmetic_store_status::size_refused;
}

template<class Record>
[[nodiscard]] arithmetic_store_receipt read_record(const char* path, Record& record,
    std::uint64_t (*integrity)(const Record&) noexcept) noexcept {
  arithmetic_store_receipt receipt{}; if (path == nullptr || path[0] == '\0') { return receipt; }
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) { receipt.state = arithmetic_store_status::open_refused; return receipt; }
  std::uint64_t calls = 0; receipt.state = read_all(descriptor,
      reinterpret_cast<unsigned char*>(&record), sizeof(record), calls);
  if (::close(descriptor) != 0 && receipt.state == arithmetic_store_status::returned) {
    receipt.state = arithmetic_store_status::transfer_refused;
  }
  receipt.bytes = exact::word{sizeof(record)}; receipt.transfer_calls = exact::word{calls};
  receipt.integrity_exact = receipt.state == arithmetic_store_status::returned &&
      record.integrity == integrity(record);
  if (!receipt.integrity_exact) { receipt.state = arithmetic_store_status::transfer_refused; }
  return receipt;
}

}  // namespace

arithmetic_store_receipt read_hodge_spectral_handoff(
    const char* path, event::hodge_realization_rest_record& record) noexcept {
  return read_record(path, record, event::hodge_realization_rest_integrity);
}

arithmetic_store_receipt write_arithmetic_spectral_handoff(
    const char* path, const event::arithmetic_spectral_rest_record& record) noexcept {
  arithmetic_store_receipt receipt{};
  if (path == nullptr || path[0] == '\0' || record.integrity !=
      event::arithmetic_spectral_rest_integrity(record)) { return receipt; }
  const int descriptor = ::open(path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
  if (descriptor < 0) { receipt.state = arithmetic_store_status::open_refused; return receipt; }
  std::uint64_t calls = 0; receipt.state = write_all(descriptor,
      reinterpret_cast<const unsigned char*>(&record), sizeof(record), calls);
  if (::close(descriptor) != 0 && receipt.state == arithmetic_store_status::returned) {
    receipt.state = arithmetic_store_status::transfer_refused;
  }
  receipt.bytes = exact::word{sizeof(record)}; receipt.transfer_calls = exact::word{calls};
  receipt.integrity_exact = receipt.state == arithmetic_store_status::returned; return receipt;
}

arithmetic_store_receipt read_arithmetic_spectral_handoff(
    const char* path, event::arithmetic_spectral_rest_record& record) noexcept {
  return read_record(path, record, event::arithmetic_spectral_rest_integrity);
}

}  // namespace holonics::apparatus

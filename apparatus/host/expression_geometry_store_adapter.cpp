#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/expression_geometry_store_adapter.hpp>
#include <holonics/event/expression_geometry_rest.hpp>
#include <holonics/event/intrinsic_hypergeometry_rest.hpp>

namespace holonics::apparatus {
namespace {

[[nodiscard]] expression_geometry_store_status write_all(
    int descriptor, const unsigned char* bytes, std::size_t count,
    std::uint64_t& calls) noexcept {
  std::size_t written = 0;
  while (written != count) {
    const auto result = ::write(descriptor, bytes + written, count - written);
    if (result < 0 && errno == EINTR) { continue; }
    if (result <= 0) { return expression_geometry_store_status::transfer_refused; }
    written += static_cast<std::size_t>(result); ++calls;
  }
  return expression_geometry_store_status::returned;
}

[[nodiscard]] expression_geometry_store_status read_all(
    int descriptor, unsigned char* bytes, std::size_t count,
    std::uint64_t& calls) noexcept {
  std::size_t read_count = 0;
  while (read_count != count) {
    const auto result = ::read(descriptor, bytes + read_count, count - read_count);
    if (result < 0 && errno == EINTR) { continue; }
    if (result <= 0) { return expression_geometry_store_status::transfer_refused; }
    read_count += static_cast<std::size_t>(result); ++calls;
  }
  char excess = 0; const auto trailing = ::read(descriptor, &excess, 1);
  return trailing == 0 ? expression_geometry_store_status::returned :
      expression_geometry_store_status::size_refused;
}

}  // namespace

expression_geometry_store_receipt read_intrinsic_hypergeometry_handoff(
    const char* path, event::intrinsic_hypergeometry_rest_record& record) noexcept {
  expression_geometry_store_receipt receipt{};
  if (path == nullptr || path[0] == '\0') { return receipt; }
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) {
    receipt.state = expression_geometry_store_status::open_refused; return receipt;
  }
  std::uint64_t calls = 0; receipt.state = read_all(descriptor,
      reinterpret_cast<unsigned char*>(&record), sizeof(record), calls);
  if (::close(descriptor) != 0 && receipt.state == expression_geometry_store_status::returned) {
    receipt.state = expression_geometry_store_status::transfer_refused;
  }
  receipt.bytes = exact::word{sizeof(record)}; receipt.transfer_calls = exact::word{calls};
  receipt.integrity_exact = receipt.state == expression_geometry_store_status::returned &&
      record.integrity == event::intrinsic_hypergeometry_rest_integrity(record);
  if (!receipt.integrity_exact) {
    receipt.state = expression_geometry_store_status::transfer_refused;
  }
  return receipt;
}

expression_geometry_store_receipt write_expression_geometry_handoff(
    const char* path, const event::expression_geometry_rest_record& record) noexcept {
  expression_geometry_store_receipt receipt{};
  if (path == nullptr || path[0] == '\0' || record.integrity !=
      event::expression_geometry_rest_integrity(record)) { return receipt; }
  const int descriptor = ::open(path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
  if (descriptor < 0) { receipt.state = expression_geometry_store_status::open_refused; return receipt; }
  std::uint64_t calls = 0; receipt.state = write_all(descriptor,
      reinterpret_cast<const unsigned char*>(&record), sizeof(record), calls);
  if (::close(descriptor) != 0 && receipt.state == expression_geometry_store_status::returned) {
    receipt.state = expression_geometry_store_status::transfer_refused;
  }
  receipt.bytes = exact::word{sizeof(record)}; receipt.transfer_calls = exact::word{calls};
  receipt.integrity_exact = receipt.state == expression_geometry_store_status::returned;
  return receipt;
}

expression_geometry_store_receipt read_expression_geometry_handoff(
    const char* path, event::expression_geometry_rest_record& record) noexcept {
  expression_geometry_store_receipt receipt{};
  if (path == nullptr || path[0] == '\0') { return receipt; }
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) { receipt.state = expression_geometry_store_status::open_refused; return receipt; }
  std::uint64_t calls = 0; receipt.state = read_all(descriptor,
      reinterpret_cast<unsigned char*>(&record), sizeof(record), calls);
  if (::close(descriptor) != 0 && receipt.state == expression_geometry_store_status::returned) {
    receipt.state = expression_geometry_store_status::transfer_refused;
  }
  receipt.bytes = exact::word{sizeof(record)}; receipt.transfer_calls = exact::word{calls};
  receipt.integrity_exact = receipt.state == expression_geometry_store_status::returned &&
      record.integrity == event::expression_geometry_rest_integrity(record);
  if (!receipt.integrity_exact) { receipt.state = expression_geometry_store_status::transfer_refused; }
  return receipt;
}

}  // namespace holonics::apparatus

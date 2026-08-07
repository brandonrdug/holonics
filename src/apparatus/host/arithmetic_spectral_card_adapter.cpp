#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/arithmetic_spectral_store_adapter.hpp>

namespace holonics::apparatus {
namespace {

constexpr std::uint64_t fold_offset = 14'695'981'039'346'656'037ULL;
constexpr std::uint64_t fold_prime = 1'099'511'628'211ULL;
void fold_octet(std::uint64_t& fold, unsigned char value) noexcept { fold ^= value; fold *= fold_prime; }
[[nodiscard]] std::uint64_t fold_path(const char* path) noexcept {
  std::uint64_t fold = fold_offset;
  for (std::size_t slot = 0; path[slot] != '\0'; ++slot) {
    fold_octet(fold, static_cast<unsigned char>(path[slot]));
  }
  return fold;
}

struct card_bytes final { char values[1024]{}; std::uint32_t count{}; std::uint64_t fold{fold_offset}; };

[[nodiscard]] arithmetic_store_status read_card(const char* path, card_bytes& bytes) noexcept {
  if (path == nullptr || path[0] == '\0') { return arithmetic_store_status::invalid_aperture; }
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) { return arithmetic_store_status::open_refused; }
  for (;;) {
    if (bytes.count == sizeof(bytes.values)) {
      char excess = 0; const auto trailing = ::read(descriptor, &excess, 1);
      static_cast<void>(::close(descriptor));
      return trailing == 0 ? arithmetic_store_status::returned : arithmetic_store_status::size_refused;
    }
    const auto result = ::read(descriptor, bytes.values + bytes.count,
        sizeof(bytes.values) - bytes.count);
    if (result < 0 && errno == EINTR) { continue; }
    if (result < 0) {
      static_cast<void>(::close(descriptor)); return arithmetic_store_status::transfer_refused;
    }
    if (result == 0) { break; }
    const auto count = static_cast<std::size_t>(result);
    for (std::size_t slot = 0; slot < count; ++slot) {
      fold_octet(bytes.fold, static_cast<unsigned char>(bytes.values[bytes.count + slot]));
    }
    bytes.count += static_cast<std::uint32_t>(count);
  }
  return ::close(descriptor) == 0 && bytes.count != 0 ?
      arithmetic_store_status::returned : arithmetic_store_status::transfer_refused;
}

struct token_reader final {
  const card_bytes& source; std::uint32_t position{};
  [[nodiscard]] bool next(std::int64_t& value) noexcept {
    while (position < source.count && (source.values[position] == ' ' ||
        source.values[position] == '\n' || source.values[position] == '\r' ||
        source.values[position] == '\t')) { ++position; }
    if (position == source.count) { return false; }
    bool negative = false; if (source.values[position] == '-') { negative = true; ++position; }
    if (position == source.count || source.values[position] < '0' || source.values[position] > '9') {
      return false;
    }
    std::uint64_t magnitude = 0;
    while (position < source.count && source.values[position] >= '0' && source.values[position] <= '9') {
      magnitude = magnitude * 10U + static_cast<std::uint64_t>(source.values[position] - '0'); ++position;
    }
    if (magnitude > 9'223'372'036'854'775'807ULL) { return false; }
    value = negative ? -static_cast<std::int64_t>(magnitude) : static_cast<std::int64_t>(magnitude);
    return true;
  }
  [[nodiscard]] bool finished() noexcept {
    while (position < source.count && (source.values[position] == ' ' ||
        source.values[position] == '\n' || source.values[position] == '\r' ||
        source.values[position] == '\t')) { ++position; }
    return position == source.count;
  }
};

[[nodiscard]] bool next(token_reader& reader, std::int64_t& value,
    std::int64_t minimum, std::int64_t maximum) noexcept {
  return reader.next(value) && value >= minimum && value <= maximum;
}

}  // namespace

arithmetic_store_receipt read_arithmetic_spectral_card(
    const char* path, organ::arithmetic_spectral_card& card) noexcept {
  card_bytes bytes{}; arithmetic_store_receipt receipt{}; receipt.state = read_card(path, bytes);
  if (receipt.state != arithmetic_store_status::returned) { return receipt; }
  token_reader reader{bytes}; std::int64_t schema = 0; std::int64_t occurrence = 0;
  std::int64_t count = 0;
  if (!next(reader, schema, 290'029, 290'029) || !next(reader, occurrence, 1, 9'999'999) ||
      !next(reader, count, 6, 6)) { receipt.state = arithmetic_store_status::parse_refused; return receipt; }
  for (std::uint8_t slot = 0; slot < organ::arithmetic_baseline_count; ++slot) {
    std::int64_t prime = 0; std::int64_t coefficient = 0;
    const std::int64_t expected_prime = slot < 2 ? 5 : 13;
    if (!next(reader, prime, expected_prime, expected_prime) ||
        !next(reader, coefficient, 1, expected_prime - 1)) {
      receipt.state = arithmetic_store_status::parse_refused; return receipt;
    }
    card.baseline[slot] = {static_cast<std::uint16_t>(prime),
        static_cast<std::uint16_t>(coefficient), exact::word{196'301U + slot}, exact::word{}};
  }
  std::int64_t changed_prime = 0; std::int64_t changed_from = 0; std::int64_t changed_to = 0;
  std::int64_t degree_min = 0; std::int64_t degree_max = 0;
  std::int64_t candidate_min = 0; std::int64_t candidate_max = 0; std::int64_t test_degree = 0;
  std::int64_t test_min = 0; std::int64_t test_max = 0; std::int64_t rechart_left = 0;
  std::int64_t rechart_right = 0;
  if (!next(reader, changed_prime, 13, 13) || !next(reader, changed_from, 1, 12) ||
      !next(reader, changed_to, 1, 12) || !next(reader, degree_min, 1, 1) ||
      !next(reader, degree_max, 4, 4) || !next(reader, candidate_min, -4, -4) ||
      !next(reader, candidate_max, 4, 4) || !next(reader, test_degree, 4, 4) ||
      !next(reader, test_min, -1, -1) || !next(reader, test_max, 1, 1) ||
      !next(reader, rechart_left, 0, 5) || !next(reader, rechart_right, 0, 5) ||
      !reader.finished()) { receipt.state = arithmetic_store_status::parse_refused; return receipt; }
  card.schema = exact::word{static_cast<std::uint64_t>(schema)};
  card.occurrence = exact::word{static_cast<std::uint64_t>(occurrence)};
  card.changed_prime = static_cast<std::uint16_t>(changed_prime);
  card.changed_from = static_cast<std::uint16_t>(changed_from);
  card.changed_to = static_cast<std::uint16_t>(changed_to);
  card.degree_min = static_cast<std::uint8_t>(degree_min);
  card.degree_max = static_cast<std::uint8_t>(degree_max);
  card.candidate_min = static_cast<std::int8_t>(candidate_min);
  card.candidate_max = static_cast<std::int8_t>(candidate_max);
  card.test_degree = static_cast<std::uint8_t>(test_degree);
  card.test_min = static_cast<std::int8_t>(test_min); card.test_max = static_cast<std::int8_t>(test_max);
  card.rechart_left = static_cast<std::uint8_t>(rechart_left);
  card.rechart_right = static_cast<std::uint8_t>(rechart_right);
  card.byte_count = bytes.count; card.byte_fold = bytes.fold; card.path_fold = fold_path(path);
  card.lineage = exact::word{card.occurrence.value() + card.byte_fold + card.path_fold};
  for (std::uint8_t slot = 0; slot < organ::arithmetic_baseline_count; ++slot) {
    card.baseline[slot].lineage = exact::word{card.lineage.value() + slot + 1U};
  }
  card.parsed = true; receipt.bytes = exact::word{bytes.count}; receipt.transfer_calls = exact::word{1};
  receipt.byte_fold = bytes.fold; receipt.path_fold = card.path_fold; receipt.integrity_exact = true;
  return receipt;
}

}  // namespace holonics::apparatus

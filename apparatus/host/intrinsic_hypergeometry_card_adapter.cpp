#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/intrinsic_hypergeometry_store_adapter.hpp>

namespace holonics::apparatus {
namespace {

constexpr std::uint64_t fold_offset = 14'695'981'039'346'656'037ULL;
constexpr std::uint64_t fold_prime = 1'099'511'628'211ULL;
void fold_octet(std::uint64_t& fold, unsigned char value) noexcept {
  fold ^= value; fold *= fold_prime;
}
[[nodiscard]] std::uint64_t fold_path(const char* path) noexcept {
  std::uint64_t fold = fold_offset;
  for (std::size_t slot = 0; path[slot] != '\0'; ++slot) {
    fold_octet(fold, static_cast<unsigned char>(path[slot]));
  }
  return fold;
}

struct card_bytes final {
  char values[512]{}; std::uint32_t count{}; std::uint64_t fold{fold_offset};
};

[[nodiscard]] intrinsic_hypergeometry_store_status read_card(
    const char* path, card_bytes& bytes) noexcept {
  if (path == nullptr || path[0] == '\0') {
    return intrinsic_hypergeometry_store_status::invalid_aperture;
  }
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) { return intrinsic_hypergeometry_store_status::open_refused; }
  for (;;) {
    if (bytes.count == sizeof(bytes.values)) {
      char excess = 0; const auto trailing = ::read(descriptor, &excess, 1);
      static_cast<void>(::close(descriptor));
      return trailing == 0 ? intrinsic_hypergeometry_store_status::returned :
          intrinsic_hypergeometry_store_status::size_refused;
    }
    const auto result = ::read(descriptor, bytes.values + bytes.count,
        sizeof(bytes.values) - bytes.count);
    if (result < 0 && errno == EINTR) { continue; }
    if (result < 0) { static_cast<void>(::close(descriptor));
      return intrinsic_hypergeometry_store_status::transfer_refused; }
    if (result == 0) { break; }
    const auto count = static_cast<std::size_t>(result);
    for (std::size_t slot = 0; slot < count; ++slot) {
      fold_octet(bytes.fold, static_cast<unsigned char>(bytes.values[bytes.count + slot]));
    }
    bytes.count += static_cast<std::uint32_t>(count);
  }
  return ::close(descriptor) == 0 && bytes.count != 0 ?
      intrinsic_hypergeometry_store_status::returned :
      intrinsic_hypergeometry_store_status::transfer_refused;
}

struct token_reader final {
  const card_bytes& source; std::uint32_t position{};
  [[nodiscard]] bool next(std::int64_t& value) noexcept {
    while (position < source.count && (source.values[position] == ' ' ||
        source.values[position] == '\n' || source.values[position] == '\r' ||
        source.values[position] == '\t')) { ++position; }
    if (position == source.count) { return false; }
    bool negative = false;
    if (source.values[position] == '-') { negative = true; ++position; }
    if (position == source.count || source.values[position] < '0' ||
        source.values[position] > '9') { return false; }
    std::uint64_t magnitude = 0;
    while (position < source.count && source.values[position] >= '0' &&
        source.values[position] <= '9') {
      magnitude = magnitude * 10U +
          static_cast<std::uint64_t>(source.values[position] - '0'); ++position;
    }
    if (magnitude > 9'223'372'036'854'775'807ULL) { return false; }
    value = negative ? -static_cast<std::int64_t>(magnitude) :
        static_cast<std::int64_t>(magnitude); return true;
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

intrinsic_hypergeometry_store_receipt read_intrinsic_hypergeometry_card(
    const char* path, organ::intrinsic_hypergeometry_card& card) noexcept {
  card_bytes bytes{}; intrinsic_hypergeometry_store_receipt receipt{};
  receipt.state = read_card(path, bytes);
  if (receipt.state != intrinsic_hypergeometry_store_status::returned) { return receipt; }
  token_reader reader{bytes}; std::int64_t schema = 0; std::int64_t occurrence = 0;
  std::int64_t cases = 0; std::int64_t depth = 0; std::int64_t modulus = 0;
  std::int64_t first_weight = 0; std::int64_t second_weight = 0; std::int64_t denominator = 0;
  if (!next(reader, schema, 260'026, 260'026) ||
      !next(reader, occurrence, 1, 9'999'999) ||
      !next(reader, cases, organ::intrinsic_case_capacity, organ::intrinsic_case_capacity) ||
      !next(reader, depth, 1, organ::intrinsic_series_capacity) ||
      !next(reader, modulus, 65'521, 65'521) || !next(reader, first_weight, 3, 3) ||
      !next(reader, second_weight, 1, 1) || !next(reader, denominator, 3, 3)) {
    receipt.state = intrinsic_hypergeometry_store_status::parse_refused; return receipt;
  }
  for (std::uint8_t slot = 0; slot < organ::intrinsic_case_capacity; ++slot) {
    std::int64_t first = 0; std::int64_t second = 0; std::int64_t rechart = 0;
    if (!next(reader, first, 2, 19) || !next(reader, second, 2, 19) ||
        !next(reader, rechart, 0, 1)) {
      receipt.state = intrinsic_hypergeometry_store_status::parse_refused; return receipt;
    }
    card.cases[slot] = {static_cast<std::uint16_t>(first),
        static_cast<std::uint16_t>(second), static_cast<std::uint8_t>(rechart)};
  }
  if (!reader.finished()) {
    receipt.state = intrinsic_hypergeometry_store_status::parse_refused; return receipt;
  }
  card.schema = exact::word{static_cast<std::uint64_t>(schema)};
  card.occurrence = exact::word{static_cast<std::uint64_t>(occurrence)};
  card.case_count = static_cast<std::uint8_t>(cases);
  card.series_depth = static_cast<std::uint8_t>(depth);
  card.section_modulus = static_cast<std::uint32_t>(modulus);
  card.receiver_first_weight = static_cast<std::uint8_t>(first_weight);
  card.receiver_second_weight = static_cast<std::uint8_t>(second_weight);
  card.receiver_denominator = static_cast<std::uint8_t>(denominator);
  card.byte_count = bytes.count; card.byte_fold = bytes.fold; card.path_fold = fold_path(path);
  card.lineage = exact::word{card.occurrence.value() + card.byte_fold + card.path_fold};
  card.parsed = true; receipt.bytes = exact::word{bytes.count};
  receipt.transfer_calls = exact::word{1}; receipt.byte_fold = bytes.fold;
  receipt.path_fold = card.path_fold; receipt.integrity_exact = true; return receipt;
}

}  // namespace holonics::apparatus

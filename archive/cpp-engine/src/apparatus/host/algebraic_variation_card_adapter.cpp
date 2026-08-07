#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/algebraic_variation_store_adapter.hpp>

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

struct card_bytes final { char values[1'024]{}; std::uint32_t count{};
  std::uint64_t fold{fold_offset}; };

[[nodiscard]] variation_store_status read_card(const char* path, card_bytes& bytes) noexcept {
  if (path == nullptr || path[0] == '\0') { return variation_store_status::invalid_aperture; }
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) { return variation_store_status::open_refused; }
  for (;;) {
    if (bytes.count == sizeof(bytes.values)) {
      char excess = 0; const auto trailing = ::read(descriptor, &excess, 1);
      static_cast<void>(::close(descriptor));
      return trailing == 0 ? variation_store_status::returned :
          variation_store_status::size_refused;
    }
    const auto result = ::read(descriptor, bytes.values + bytes.count,
        sizeof(bytes.values) - bytes.count);
    if (result < 0 && errno == EINTR) { continue; }
    if (result < 0) { static_cast<void>(::close(descriptor));
      return variation_store_status::transfer_refused; }
    if (result == 0) { break; }
    const auto count = static_cast<std::size_t>(result);
    for (std::size_t slot = 0; slot < count; ++slot) {
      fold_octet(bytes.fold, static_cast<unsigned char>(bytes.values[bytes.count + slot]));
    }
    bytes.count += static_cast<std::uint32_t>(count);
  }
  return ::close(descriptor) == 0 && bytes.count != 0 ? variation_store_status::returned :
      variation_store_status::transfer_refused;
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

variation_store_receipt read_algebraic_variation_card(
    const char* path, organ::algebraic_variation_card& card) noexcept {
  card_bytes bytes{}; variation_store_receipt receipt{};
  receipt.state = read_card(path, bytes);
  if (receipt.state != variation_store_status::returned) { return receipt; }
  token_reader reader{bytes}; std::int64_t value = 0;
  std::int64_t schema = 0; std::int64_t occurrence = 0; std::int64_t degree = 0;
  std::int64_t cover = 0; std::int64_t samples = 0; std::int64_t discovery = 0;
  std::int64_t depth = 0; std::int64_t root_min = 0; std::int64_t root_max = 0;
  std::int64_t form_min = 0; std::int64_t form_max = 0;
  if (!next(reader, schema, 240'024, 240'024) || !next(reader, occurrence, 1, 9'999'999) ||
      !next(reader, degree, 3, 3) || !next(reader, cover, 2, 2) ||
      !next(reader, samples, 7, 7) || !next(reader, discovery, 5, 5) ||
      !next(reader, depth, 6, 6) || !next(reader, root_min, -2, -2) ||
      !next(reader, root_max, 2, 2) || !next(reader, form_min, -2, -2) ||
      !next(reader, form_max, 2, 2)) {
    receipt.state = variation_store_status::parse_refused; return receipt;
  }
  card.schema = exact::word{static_cast<std::uint64_t>(schema)};
  card.occurrence = exact::word{static_cast<std::uint64_t>(occurrence)};
  card.degree = static_cast<std::uint8_t>(degree); card.cover_degree = static_cast<std::uint8_t>(cover);
  card.sample_count = static_cast<std::uint8_t>(samples);
  card.discovery_count = static_cast<std::uint8_t>(discovery);
  card.series_depth = static_cast<std::uint8_t>(depth);
  card.root_min = static_cast<std::int8_t>(root_min); card.root_max = static_cast<std::int8_t>(root_max);
  card.form_min = static_cast<std::int8_t>(form_min); card.form_max = static_cast<std::int8_t>(form_max);
  for (std::uint8_t coefficient = 0; coefficient < 4; ++coefficient) {
    if (!next(reader, card.coefficients[coefficient].constant, -8, 8) ||
        !next(reader, card.coefficients[coefficient].parameter, -8, 8)) {
      receipt.state = variation_store_status::parse_refused; return receipt;
    }
  }
  for (std::uint8_t sample = 0; sample < card.sample_count; ++sample) {
    std::int64_t numerator = 0; std::int64_t denominator = 0;
    if (!next(reader, numerator, -16, 16) || !next(reader, denominator, 1, 16)) {
      receipt.state = variation_store_status::parse_refused; return receipt;
    }
    card.samples[sample] = exact::small_rational_law::make(numerator, denominator);
  }
  if (!reader.finished()) { receipt.state = variation_store_status::parse_refused; return receipt; }
  static_cast<void>(value); card.byte_count = bytes.count; card.byte_fold = bytes.fold;
  card.path_fold = fold_path(path);
  card.lineage = exact::word{card.occurrence.value() + card.byte_fold};
  card.parsed = true; receipt.bytes = exact::word{bytes.count};
  receipt.transfer_calls = exact::word{1}; receipt.byte_fold = bytes.fold;
  receipt.path_fold = card.path_fold; receipt.integrity_exact = true; return receipt;
}

}  // namespace holonics::apparatus

#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/expression_geometry_store_adapter.hpp>

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
  char values[1024]{}; std::uint32_t count{}; std::uint64_t fold{fold_offset};
};

[[nodiscard]] expression_geometry_store_status read_card(
    const char* path, card_bytes& bytes) noexcept {
  if (path == nullptr || path[0] == '\0') {
    return expression_geometry_store_status::invalid_aperture;
  }
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) { return expression_geometry_store_status::open_refused; }
  for (;;) {
    if (bytes.count == sizeof(bytes.values)) {
      char excess = 0; const auto trailing = ::read(descriptor, &excess, 1);
      static_cast<void>(::close(descriptor));
      return trailing == 0 ? expression_geometry_store_status::returned :
          expression_geometry_store_status::size_refused;
    }
    const auto result = ::read(descriptor, bytes.values + bytes.count,
        sizeof(bytes.values) - bytes.count);
    if (result < 0 && errno == EINTR) { continue; }
    if (result < 0) { static_cast<void>(::close(descriptor));
      return expression_geometry_store_status::transfer_refused; }
    if (result == 0) { break; }
    const auto count = static_cast<std::size_t>(result);
    for (std::size_t slot = 0; slot < count; ++slot) {
      fold_octet(bytes.fold, static_cast<unsigned char>(bytes.values[bytes.count + slot]));
    }
    bytes.count += static_cast<std::uint32_t>(count);
  }
  return ::close(descriptor) == 0 && bytes.count != 0 ?
      expression_geometry_store_status::returned :
      expression_geometry_store_status::transfer_refused;
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

expression_geometry_store_receipt read_expression_geometry_card(
    const char* path, organ::expression_geometry_card& card) noexcept {
  card_bytes bytes{}; expression_geometry_store_receipt receipt{};
  receipt.state = read_card(path, bytes);
  if (receipt.state != expression_geometry_store_status::returned) { return receipt; }
  token_reader reader{bytes}; std::int64_t schema = 0; std::int64_t occurrence = 0;
  std::int64_t count = 0; std::int64_t depth = 0; std::int64_t discovery_min = 0;
  std::int64_t discovery_max = 0; std::int64_t holdout_first = 0;
  std::int64_t holdout_second = 0; std::int64_t chart_min = 0; std::int64_t chart_max = 0;
  if (!next(reader, schema, 270'027, 270'027) || !next(reader, occurrence, 1, 9'999'999) ||
      !next(reader, count, 3, 3) || !next(reader, depth, 11, 11) ||
      !next(reader, discovery_min, -4, -4) || !next(reader, discovery_max, 4, 4) ||
      !next(reader, holdout_first, 5, 5) || !next(reader, holdout_second, 6, 6) ||
      !next(reader, chart_min, -2, -2) || !next(reader, chart_max, 2, 2)) {
    receipt.state = expression_geometry_store_status::parse_refused; return receipt;
  }
  for (std::uint8_t presentation = 0; presentation < 3; ++presentation) {
    std::int64_t terms = 0;
    if (!next(reader, terms, 1, organ::expression_term_capacity)) {
      receipt.state = expression_geometry_store_status::parse_refused; return receipt;
    }
    auto& expression = card.presentations[presentation];
    expression.identity = exact::word{194'301U + presentation};
    for (std::uint8_t slot = 0; slot < static_cast<std::uint8_t>(terms); ++slot) {
      std::int64_t coefficient = 0; std::int64_t parameter = 0;
      std::int64_t x = 0; std::int64_t y = 0;
      if (!next(reader, coefficient, -10, 10) || !next(reader, parameter, 0, 1) ||
          !next(reader, x, 0, 5) || !next(reader, y, 0, 2)) {
        receipt.state = expression_geometry_store_status::parse_refused; return receipt;
      }
      expression.terms[slot] = {coefficient, static_cast<std::uint8_t>(parameter),
          static_cast<std::uint8_t>(x), static_cast<std::uint8_t>(y)};
    }
    expression.term_count = static_cast<std::uint8_t>(terms); expression.exact = true;
  }
  if (!reader.finished()) {
    receipt.state = expression_geometry_store_status::parse_refused; return receipt;
  }
  card.schema = exact::word{static_cast<std::uint64_t>(schema)};
  card.occurrence = exact::word{static_cast<std::uint64_t>(occurrence)};
  card.presentation_count = static_cast<std::uint8_t>(count);
  card.series_depth = static_cast<std::uint8_t>(depth);
  card.discovery_min = static_cast<std::int8_t>(discovery_min);
  card.discovery_max = static_cast<std::int8_t>(discovery_max);
  card.holdout_first = static_cast<std::int8_t>(holdout_first);
  card.holdout_second = static_cast<std::int8_t>(holdout_second);
  card.chart_min = static_cast<std::int8_t>(chart_min);
  card.chart_max = static_cast<std::int8_t>(chart_max);
  card.byte_count = bytes.count; card.byte_fold = bytes.fold; card.path_fold = fold_path(path);
  card.lineage = exact::word{card.occurrence.value() + card.byte_fold + card.path_fold};
  for (std::uint8_t slot = 0; slot < 3; ++slot) {
    card.presentations[slot].lineage = exact::word{card.lineage.value() + slot + 1U};
  }
  card.parsed = true; receipt.bytes = exact::word{bytes.count};
  receipt.transfer_calls = exact::word{1}; receipt.byte_fold = bytes.fold;
  receipt.path_fold = card.path_fold; receipt.integrity_exact = true; return receipt;
}

}  // namespace holonics::apparatus

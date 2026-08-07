#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/hodge_realization_store_adapter.hpp>

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

[[nodiscard]] hodge_store_status read_card(const char* path, card_bytes& bytes) noexcept {
  if (path == nullptr || path[0] == '\0') { return hodge_store_status::invalid_aperture; }
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) { return hodge_store_status::open_refused; }
  for (;;) {
    if (bytes.count == sizeof(bytes.values)) {
      char excess = 0; const auto trailing = ::read(descriptor, &excess, 1);
      static_cast<void>(::close(descriptor));
      return trailing == 0 ? hodge_store_status::returned : hodge_store_status::size_refused;
    }
    const auto result = ::read(descriptor, bytes.values + bytes.count,
        sizeof(bytes.values) - bytes.count);
    if (result < 0 && errno == EINTR) { continue; }
    if (result < 0) { static_cast<void>(::close(descriptor)); return hodge_store_status::transfer_refused; }
    if (result == 0) { break; }
    const auto count = static_cast<std::size_t>(result);
    for (std::size_t slot = 0; slot < count; ++slot) {
      fold_octet(bytes.fold, static_cast<unsigned char>(bytes.values[bytes.count + slot]));
    }
    bytes.count += static_cast<std::uint32_t>(count);
  }
  return ::close(descriptor) == 0 && bytes.count != 0 ?
      hodge_store_status::returned : hodge_store_status::transfer_refused;
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

hodge_store_receipt read_hodge_realization_card(
    const char* path, organ::hodge_realization_card& card) noexcept {
  card_bytes bytes{}; hodge_store_receipt receipt{}; receipt.state = read_card(path, bytes);
  if (receipt.state != hodge_store_status::returned) { return receipt; }
  token_reader reader{bytes}; std::int64_t header[13]{};
  const std::int64_t minimum[13]{280'028,1,2,6,2,2,3,-1,1,2,0,1,3};
  const std::int64_t maximum[13]{280'028,9'999'999,2,6,2,2,3,-1,1,2,0,1,3};
  for (std::uint8_t slot = 0; slot < 13; ++slot) {
    if (!next(reader, header[slot], minimum[slot], maximum[slot])) {
      receipt.state = hodge_store_status::parse_refused; return receipt;
    }
  }
  for (std::uint8_t factor = 0; factor < organ::hodge_factor_capacity; ++factor) {
    std::int64_t count = 0;
    if (!next(reader, count, 5, 5)) { receipt.state = hodge_store_status::parse_refused; return receipt; }
    auto& target = card.factors[factor]; target.identity = exact::word{195'301U + factor};
    for (std::uint8_t slot = 0; slot < static_cast<std::uint8_t>(count); ++slot) {
      std::int64_t coefficient = 0; std::int64_t parameter = 0; std::int64_t x = 0; std::int64_t y = 0;
      if (!next(reader, coefficient, -4, 4) || !next(reader, parameter, 0, 1) ||
          !next(reader, x, 0, 3) || !next(reader, y, 0, 2)) {
        receipt.state = hodge_store_status::parse_refused; return receipt;
      }
      target.terms[slot] = {coefficient, static_cast<std::uint8_t>(parameter),
          static_cast<std::uint8_t>(x), static_cast<std::uint8_t>(y)};
    }
    target.term_count = static_cast<std::uint8_t>(count); target.exact = true;
  }
  for (std::uint8_t question = 0; question < organ::hodge_target_capacity; ++question) {
    for (std::uint8_t slot = 0; slot < organ::hodge_rank; ++slot) {
      if (!next(reader, card.questions[question].numerator[slot], -4, 4)) {
        receipt.state = hodge_store_status::parse_refused; return receipt;
      }
    }
    std::int64_t denominator = 0;
    if (!next(reader, denominator, 1, 2)) { receipt.state = hodge_store_status::parse_refused; return receipt; }
    card.questions[question].denominator = static_cast<std::uint8_t>(denominator);
  }
  if (!reader.finished()) { receipt.state = hodge_store_status::parse_refused; return receipt; }
  card.schema = exact::word{static_cast<std::uint64_t>(header[0])};
  card.occurrence = exact::word{static_cast<std::uint64_t>(header[1])};
  card.factor_count = static_cast<std::uint8_t>(header[2]); card.rank = static_cast<std::uint8_t>(header[3]);
  card.base_t = static_cast<std::int8_t>(header[4]); card.base_u = static_cast<std::int8_t>(header[5]);
  card.off_diagonal_u = static_cast<std::int8_t>(header[6]);
  card.coefficient_min = static_cast<std::int8_t>(header[7]);
  card.coefficient_max = static_cast<std::int8_t>(header[8]);
  card.denominator_aperture = static_cast<std::uint8_t>(header[9]);
  card.center_selector = static_cast<std::uint8_t>(header[10]);
  card.changed_center_selector = static_cast<std::uint8_t>(header[11]);
  card.question_count = static_cast<std::uint8_t>(header[12]);
  card.byte_count = bytes.count; card.byte_fold = bytes.fold; card.path_fold = fold_path(path);
  card.lineage = exact::word{card.occurrence.value() + card.byte_fold};
  for (std::uint8_t slot = 0; slot < organ::hodge_factor_capacity; ++slot) {
    card.factors[slot].lineage = exact::word{card.lineage.value() + slot + 1U};
  }
  card.parsed = true; receipt.bytes = exact::word{bytes.count}; receipt.transfer_calls = exact::word{1};
  receipt.byte_fold = bytes.fold; receipt.path_fold = card.path_fold; receipt.integrity_exact = true;
  return receipt;
}

}  // namespace holonics::apparatus

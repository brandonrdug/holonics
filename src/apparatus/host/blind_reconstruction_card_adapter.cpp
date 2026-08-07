#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/blind_reconstruction_store_adapter.hpp>
#include <holonics/organ/blind_integer_exact.hpp>

namespace holonics::apparatus {
namespace {

constexpr std::uint64_t fold_offset = 14'695'981'039'346'656'037ULL;
constexpr std::uint64_t fold_prime = 1'099'511'628'211ULL;

void fold_octet(std::uint64_t& fold, unsigned char value) noexcept {
  fold ^= value;
  fold *= fold_prime;
}

[[nodiscard]] std::uint64_t path_fold(const char* path) noexcept {
  std::uint64_t fold = fold_offset;
  for (std::size_t slot = 0; path[slot] != '\0'; ++slot) {
    fold_octet(fold, static_cast<unsigned char>(path[slot]));
  }
  return fold;
}

struct card_bytes final {
  char values[1'024]{};
  std::uint32_t count{};
  std::uint64_t fold{fold_offset};
};

[[nodiscard]] blind_store_status read_card(const char* path, card_bytes& bytes) noexcept {
  if (path == nullptr || path[0] == '\0') { return blind_store_status::invalid_aperture; }
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) { return blind_store_status::open_refused; }
  for (;;) {
    if (bytes.count == sizeof(bytes.values)) {
      char excess = 0;
      const auto trailing = ::read(descriptor, &excess, 1);
      static_cast<void>(::close(descriptor));
      return trailing == 0 ? blind_store_status::returned : blind_store_status::size_refused;
    }
    const auto result = ::read(descriptor, bytes.values + bytes.count,
        sizeof(bytes.values) - bytes.count);
    if (result < 0 && errno == EINTR) { continue; }
    if (result < 0) { static_cast<void>(::close(descriptor));
      return blind_store_status::transfer_refused; }
    if (result == 0) { break; }
    const auto count = static_cast<std::size_t>(result);
    for (std::size_t slot = 0; slot < count; ++slot) {
      fold_octet(bytes.fold,
          static_cast<unsigned char>(bytes.values[bytes.count + slot]));
    }
    bytes.count += static_cast<std::uint32_t>(count);
  }
  return ::close(descriptor) == 0 && bytes.count != 0 ? blind_store_status::returned :
      blind_store_status::transfer_refused;
}

struct token_reader final {
  const card_bytes& source;
  std::uint32_t position{};

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
      const auto digit = static_cast<std::uint64_t>(source.values[position] - '0');
      if (magnitude > 922'337'203'685'477'580ULL) { return false; }
      magnitude = magnitude * 10U + digit;
      ++position;
    }
    if (magnitude > 9'223'372'036'854'775'807ULL) { return false; }
    value = negative ? -static_cast<std::int64_t>(magnitude) :
        static_cast<std::int64_t>(magnitude);
    return true;
  }

  [[nodiscard]] bool finished() noexcept {
    while (position < source.count && (source.values[position] == ' ' ||
        source.values[position] == '\n' || source.values[position] == '\r' ||
        source.values[position] == '\t')) { ++position; }
    return position == source.count;
  }
};

[[nodiscard]] blind_store_receipt base_receipt(
    const char* path, const card_bytes& bytes) noexcept {
  blind_store_receipt receipt{};
  receipt.state = blind_store_status::returned;
  receipt.bytes = exact::word{bytes.count};
  receipt.transfer_calls = exact::word{1};
  receipt.byte_fold = bytes.fold;
  receipt.path_fold = path_fold(path);
  receipt.integrity_exact = true;
  return receipt;
}

}  // namespace

blind_store_receipt read_binary_code_card(
    const char* path, organ::binary_code_problem_card& card) noexcept {
  card_bytes bytes{};
  const auto state = read_card(path, bytes);
  if (state != blind_store_status::returned) { blind_store_receipt out{}; out.state = state; return out; }
  token_reader reader{bytes};
  std::int64_t schema = 0;
  std::int64_t occurrence = 0;
  std::int64_t dimension = 0;
  std::int64_t row_count = 0;
  if (!reader.next(schema) || !reader.next(occurrence) || !reader.next(dimension) ||
      !reader.next(row_count) || schema != 210'021 || occurrence <= 0 ||
      dimension <= 0 || dimension >
          static_cast<std::int64_t>(organ::blind_cube_dimension_capacity) ||
      row_count <= 0 || row_count >
          static_cast<std::int64_t>(organ::blind_parity_row_capacity)) {
    auto out = base_receipt(path, bytes); out.state = blind_store_status::parse_refused; return out;
  }
  card.schema = exact::word{static_cast<std::uint64_t>(schema)};
  card.occurrence = exact::word{static_cast<std::uint64_t>(occurrence)};
  card.dimension = static_cast<std::uint8_t>(dimension);
  card.row_count = static_cast<std::uint8_t>(row_count);
  for (std::uint8_t row = 0; row < card.row_count; ++row) {
    std::int64_t mask = 0;
    if (!reader.next(mask) || mask <= 0 || mask >= (1LL << card.dimension)) {
      auto out = base_receipt(path, bytes); out.state = blind_store_status::parse_refused; return out;
    }
    card.parity_rows[row] = static_cast<std::uint8_t>(mask);
  }
  if (!reader.finished()) {
    auto out = base_receipt(path, bytes); out.state = blind_store_status::parse_refused; return out;
  }
  auto out = base_receipt(path, bytes);
  card.byte_count = bytes.count;
  card.byte_fold = bytes.fold;
  card.path_fold = out.path_fold;
  card.lineage = exact::word{card.occurrence.value() + bytes.fold + out.path_fold};
  card.parsed = true;
  return out;
}

blind_store_receipt read_moment_problem_card(
    const char* path, organ::moment_problem_card& card) noexcept {
  card_bytes bytes{};
  const auto state = read_card(path, bytes);
  if (state != blind_store_status::returned) { blind_store_receipt out{}; out.state = state; return out; }
  token_reader reader{bytes};
  std::int64_t schema = 0;
  std::int64_t case_count = 0;
  if (!reader.next(schema) || !reader.next(case_count) || schema != 210'022 ||
      case_count != organ::blind_moment_case_capacity) {
    auto out = base_receipt(path, bytes); out.state = blind_store_status::parse_refused; return out;
  }
  card.schema = exact::word{static_cast<std::uint64_t>(schema)};
  card.case_count = static_cast<std::uint8_t>(case_count);
  for (std::uint8_t slot = 0; slot < card.case_count; ++slot) {
    std::int64_t identity = 0;
    std::int64_t degree = 0;
    std::int64_t moment_count = 0;
    std::int64_t aperture_min = 0;
    std::int64_t aperture_max = 0;
    if (!reader.next(identity) || !reader.next(degree) || !reader.next(moment_count) ||
        !reader.next(aperture_min) || !reader.next(aperture_max) || identity <= 0 ||
        degree < 2 || degree >
            static_cast<std::int64_t>(organ::blind_moment_degree_capacity) ||
        moment_count < 0 || moment_count >
            static_cast<std::int64_t>(organ::blind_moment_capacity) ||
        aperture_min < -32 || aperture_max > 32 ||
        aperture_min > aperture_max) {
      auto out = base_receipt(path, bytes); out.state = blind_store_status::parse_refused; return out;
    }
    auto& value = card.cases[slot];
    value.occurrence = exact::word{static_cast<std::uint64_t>(identity)};
    value.degree = static_cast<std::uint8_t>(degree);
    value.moment_count = static_cast<std::uint8_t>(moment_count);
    value.aperture_min = static_cast<std::int16_t>(aperture_min);
    value.aperture_max = static_cast<std::int16_t>(aperture_max);
    for (std::uint8_t index = 0; index < value.moment_count; ++index) {
      if (!reader.next(value.moments[index]) ||
          organ::blind_integer_detail::magnitude(value.moments[index]) > 1'000'000U) {
        auto out = base_receipt(path, bytes); out.state = blind_store_status::parse_refused; return out;
      }
    }
  }
  if (!reader.finished()) {
    auto out = base_receipt(path, bytes); out.state = blind_store_status::parse_refused; return out;
  }
  auto out = base_receipt(path, bytes);
  card.byte_count = bytes.count;
  card.byte_fold = bytes.fold;
  card.path_fold = out.path_fold;
  card.lineage = exact::word{bytes.fold + out.path_fold + card.schema.value()};
  card.parsed = true;
  return out;
}

}  // namespace holonics::apparatus

#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/causal_linear_store_adapter.hpp>

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
  char values[256]{}; std::uint32_t count{}; std::uint64_t fold{fold_offset};
};

[[nodiscard]] causal_linear_store_status read_card(
    const char* path, card_bytes& bytes) noexcept {
  if (path == nullptr || path[0] == '\0') {
    return causal_linear_store_status::invalid_aperture;
  }
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) { return causal_linear_store_status::open_refused; }
  for (;;) {
    if (bytes.count == sizeof(bytes.values)) {
      char excess = 0; const auto trailing = ::read(descriptor, &excess, 1);
      static_cast<void>(::close(descriptor));
      return trailing == 0 ? causal_linear_store_status::returned :
          causal_linear_store_status::size_refused;
    }
    const auto result = ::read(descriptor, bytes.values + bytes.count,
        sizeof(bytes.values) - bytes.count);
    if (result < 0 && errno == EINTR) { continue; }
    if (result < 0) { static_cast<void>(::close(descriptor));
      return causal_linear_store_status::transfer_refused; }
    if (result == 0) { break; }
    const auto count = static_cast<std::size_t>(result);
    for (std::size_t slot = 0; slot < count; ++slot) {
      fold_octet(bytes.fold, static_cast<unsigned char>(bytes.values[bytes.count + slot]));
    }
    bytes.count += static_cast<std::uint32_t>(count);
  }
  return ::close(descriptor) == 0 && bytes.count != 0 ?
      causal_linear_store_status::returned : causal_linear_store_status::transfer_refused;
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

causal_linear_store_receipt read_causal_linear_card(
    const char* path, organ::causal_linear_card& card) noexcept {
  card_bytes bytes{}; causal_linear_store_receipt receipt{};
  receipt.state = read_card(path, bytes);
  if (receipt.state != causal_linear_store_status::returned) { return receipt; }
  token_reader reader{bytes}; std::int64_t schema = 0; std::int64_t occurrence = 0;
  std::int64_t first = 0; std::int64_t second = 0;
  std::int64_t eigen_min = 0; std::int64_t eigen_max = 0;
  if (!next(reader, schema, 250'025, 250'025) ||
      !next(reader, occurrence, 1, 9'999'999) || !next(reader, first, 2, 17) ||
      !next(reader, second, 2, 19) || !next(reader, eigen_min, -16, -2) ||
      !next(reader, eigen_max, 2, 16) || !reader.finished()) {
    receipt.state = causal_linear_store_status::parse_refused; return receipt;
  }
  card.schema = exact::word{static_cast<std::uint64_t>(schema)};
  card.occurrence = exact::word{static_cast<std::uint64_t>(occurrence)};
  card.phase_first = static_cast<std::uint8_t>(first);
  card.phase_second = static_cast<std::uint8_t>(second);
  card.eigen_min = static_cast<std::int8_t>(eigen_min);
  card.eigen_max = static_cast<std::int8_t>(eigen_max);
  card.byte_count = bytes.count; card.byte_fold = bytes.fold; card.path_fold = fold_path(path);
  card.lineage = exact::word{card.occurrence.value() + card.byte_fold + card.path_fold};
  card.parsed = true; receipt.bytes = exact::word{bytes.count};
  receipt.transfer_calls = exact::word{1}; receipt.byte_fold = bytes.fold;
  receipt.path_fold = card.path_fold; receipt.integrity_exact = true; return receipt;
}

}  // namespace holonics::apparatus

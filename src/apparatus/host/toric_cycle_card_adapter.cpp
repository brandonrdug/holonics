#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/toric_cycle_store_adapter.hpp>

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
  char values[1'024]{};
  std::uint32_t count{};
  std::uint64_t fold{fold_offset};
};

[[nodiscard]] toric_store_status read_card(const char* path, card_bytes& bytes) noexcept {
  if (path == nullptr || path[0] == '\0') { return toric_store_status::invalid_aperture; }
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) { return toric_store_status::open_refused; }
  for (;;) {
    if (bytes.count == sizeof(bytes.values)) {
      char excess = 0; const auto trailing = ::read(descriptor, &excess, 1);
      static_cast<void>(::close(descriptor));
      return trailing == 0 ? toric_store_status::returned : toric_store_status::size_refused;
    }
    const auto result = ::read(descriptor, bytes.values + bytes.count,
        sizeof(bytes.values) - bytes.count);
    if (result < 0 && errno == EINTR) { continue; }
    if (result < 0) { static_cast<void>(::close(descriptor));
      return toric_store_status::transfer_refused; }
    if (result == 0) { break; }
    const auto count = static_cast<std::size_t>(result);
    for (std::size_t slot = 0; slot < count; ++slot) {
      fold_octet(bytes.fold, static_cast<unsigned char>(bytes.values[bytes.count + slot]));
    }
    bytes.count += static_cast<std::uint32_t>(count);
  }
  return ::close(descriptor) == 0 && bytes.count != 0 ? toric_store_status::returned :
      toric_store_status::transfer_refused;
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
      magnitude = magnitude * 10U +
          static_cast<std::uint64_t>(source.values[position] - '0'); ++position;
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

[[nodiscard]] bool next(token_reader& reader, std::int64_t& value,
    std::int64_t minimum, std::int64_t maximum) noexcept {
  return reader.next(value) && value >= minimum && value <= maximum;
}

}  // namespace

toric_store_receipt read_toric_cycle_card(
    const char* path, organ::toric_cycle_card& card) noexcept {
  card_bytes bytes{}; toric_store_receipt receipt{};
  receipt.state = read_card(path, bytes);
  if (receipt.state != toric_store_status::returned) { return receipt; }
  token_reader reader{bytes};
  std::int64_t schema = 0; std::int64_t occurrence = 0; std::int64_t fan_count = 0;
  std::int64_t selected_fan = 0; std::int64_t selected_cone = 0;
  std::int64_t minimum = 0; std::int64_t maximum = 0;
  if (!next(reader, schema, 230'023, 230'023) ||
      !next(reader, occurrence, 1, 9'999'999) ||
      !next(reader, fan_count, 2, 2) || !next(reader, selected_fan, 0, 1) ||
      !next(reader, selected_cone, 0, 4) || !next(reader, minimum, -4, -4) ||
      !next(reader, maximum, 4, 4)) {
    receipt.state = toric_store_status::parse_refused; return receipt;
  }
  card.schema = exact::word{static_cast<std::uint64_t>(schema)};
  card.occurrence = exact::word{static_cast<std::uint64_t>(occurrence)};
  card.fan_count = static_cast<std::uint8_t>(fan_count);
  card.selected_fan = static_cast<std::uint8_t>(selected_fan);
  card.selected_cone = static_cast<std::uint8_t>(selected_cone);
  card.representative_min = static_cast<std::int16_t>(minimum);
  card.representative_max = static_cast<std::int16_t>(maximum);
  for (std::uint8_t fan = 0; fan < card.fan_count; ++fan) {
    std::int64_t ray_count = 0;
    if (!next(reader, ray_count, 3, static_cast<std::int64_t>(organ::toric_ray_capacity))) {
      receipt.state = toric_store_status::parse_refused; return receipt;
    }
    card.fans[fan].ray_count = static_cast<std::uint8_t>(ray_count);
    for (std::uint8_t ray = 0; ray < card.fans[fan].ray_count; ++ray) {
      if (!next(reader, card.fans[fan].rays[ray].x, -16, 16) ||
          !next(reader, card.fans[fan].rays[ray].y, -16, 16)) {
        receipt.state = toric_store_status::parse_refused; return receipt;
      }
    }
  }
  std::int64_t target_count = 0;
  if (!next(reader, target_count, 3, 3)) {
    receipt.state = toric_store_status::parse_refused; return receipt;
  }
  card.target_count = static_cast<std::uint8_t>(target_count);
  const auto response_count = card.fans[1].ray_count;
  for (std::uint8_t target = 0; target < card.target_count; ++target) {
    for (std::uint8_t ray = 0; ray < response_count; ++ray) {
      if (!next(reader, card.targets[target].response[ray].numerator, -64, 64) ||
          !next(reader, card.targets[target].response[ray].denominator, 1, 64)) {
        receipt.state = toric_store_status::parse_refused; return receipt;
      }
    }
  }
  if (!reader.finished() || card.selected_cone >= card.fans[card.selected_fan].ray_count) {
    receipt.state = toric_store_status::parse_refused; return receipt;
  }
  card.byte_count = bytes.count; card.byte_fold = bytes.fold; card.path_fold = fold_path(path);
  card.lineage = exact::word{card.occurrence.value() + card.byte_fold + card.path_fold};
  card.parsed = true;
  receipt.bytes = exact::word{bytes.count}; receipt.transfer_calls = exact::word{1};
  receipt.byte_fold = bytes.fold; receipt.path_fold = card.path_fold;
  receipt.integrity_exact = true;
  return receipt;
}

}  // namespace holonics::apparatus

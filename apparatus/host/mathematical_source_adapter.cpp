#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>
#include <system_error>

#include <holonics/apparatus/mathematical_source_adapter.hpp>

namespace holonics::apparatus {
namespace {

constexpr std::uint64_t fold_basis = 14'695'981'039'346'656'037ULL;
constexpr std::uint64_t fold_prime = 1'099'511'628'211ULL;

void mix(std::uint64_t& fold, unsigned char value) noexcept {
  fold ^= value;
  fold *= fold_prime;
}

void mix_word(std::uint64_t& fold, std::uint64_t value) noexcept {
  for (std::size_t octet = 0; octet < 8; ++octet) {
    mix(fold, static_cast<unsigned char>(value & 255U));
    value >>= 8U;
  }
}

[[nodiscard]] bool contains(
    const codec::mathematical_source_buffer& source, const char* marker) noexcept {
  std::size_t marker_count = 0;
  while (marker[marker_count] != '\0') { ++marker_count; }
  if (marker_count == 0 || marker_count > source.byte_count) { return false; }
  for (std::size_t begin = 0; begin + marker_count <= source.byte_count; ++begin) {
    bool equal = true;
    for (std::size_t offset = 0; offset < marker_count; ++offset) {
      equal = equal && source.bytes[begin + offset] ==
          static_cast<unsigned char>(marker[offset]);
    }
    if (equal) { return true; }
  }
  return false;
}

[[nodiscard]] bool read_one(const char* path,
    codec::mathematical_source_buffer& source,
    mathematical_source_receipt& receipt) noexcept {
  std::ifstream input{path, std::ios::binary};
  if (!input) { receipt.state = mathematical_source_status::open_refused; return false; }
  source.material_testimony = fold_basis;
  char octet = 0;
  while (input.get(octet)) {
    if (source.byte_count == codec::mathematical_source_byte_capacity) {
      receipt.state = mathematical_source_status::capacity_refused;
      return false;
    }
    const auto value = static_cast<unsigned char>(octet);
    source.bytes[source.byte_count++] = value;
    mix(source.material_testimony, value);
  }
  if (!input.eof() || source.byte_count == 0) {
    receipt.state = mathematical_source_status::read_refused;
    return false;
  }
  for (const char* cursor = path; *cursor != '\0'; ++cursor) {
    mix(receipt.path_testimony, static_cast<unsigned char>(*cursor));
  }
  return true;
}

[[nodiscard]] bool same_buffer(
    const codec::mathematical_source_buffer& left,
    const codec::mathematical_source_buffer& right) noexcept {
  if (left.byte_count != right.byte_count) { return false; }
  for (std::size_t slot = 0; slot < left.byte_count; ++slot) {
    if (left.bytes[slot] != right.bytes[slot]) { return false; }
  }
  return true;
}

}  // namespace

mathematical_source_result mount_mathematical_sources(
    const char* const* paths, std::size_t count, std::uint16_t chunk_aperture) noexcept {
  mathematical_source_result result{};
  result.receipt.path_testimony = fold_basis;
  if (paths == nullptr || count != codec::mathematical_source_capacity ||
      chunk_aperture == 0 || !result.environment.admitted()) {
    return result;
  }
  auto& encoded = result.environment.encoded();
  encoded.source_count = static_cast<std::uint16_t>(count);
  result.receipt.source_count = static_cast<std::uint16_t>(count);
  result.receipt.chunk_aperture = chunk_aperture;
  for (std::size_t slot = 0; slot < count; ++slot) {
    if (!read_one(paths[slot], encoded.sources[slot], result.receipt)) { return result; }
    result.receipt.byte_count += encoded.sources[slot].byte_count;
    result.receipt.chunk_count = static_cast<std::uint16_t>(result.receipt.chunk_count +
        (encoded.sources[slot].byte_count + chunk_aperture - 1U) / chunk_aperture);
  }
  for (std::size_t slot = 0; slot < count; ++slot) {
    const auto& source = encoded.sources[slot];
    result.receipt.recognized_declarations |= contains(source, "theorem map") ? 1U : 0U;
    result.receipt.recognized_declarations |= contains(source, "theorem trans") ? 2U : 0U;
    result.receipt.recognized_declarations |=
        contains(source, "theorem trace_rebase_iff") ? 4U : 0U;
    result.receipt.recognized_declarations |=
        contains(source, "theorem semantics_rebase_iff") ? 8U : 0U;
  }
  if (result.receipt.recognized_declarations != 15U) {
    result.receipt.state = mathematical_source_status::recognition_refused;
    return result;
  }
  std::uint64_t first = encoded.sources[0].material_testimony;
  std::uint64_t second = encoded.sources[1].material_testimony;
  std::uint64_t first_size = encoded.sources[0].byte_count;
  std::uint64_t second_size = encoded.sources[1].byte_count;
  if (second < first || (second == first && second_size < first_size)) {
    const auto saved_fold = first;
    const auto saved_size = first_size;
    first = second; first_size = second_size;
    second = saved_fold; second_size = saved_size;
  }
  result.receipt.material_testimony = fold_basis;
  mix_word(result.receipt.material_testimony, first);
  mix_word(result.receipt.material_testimony, first_size);
  mix_word(result.receipt.material_testimony, second);
  mix_word(result.receipt.material_testimony, second_size);
  result.receipt.state = mathematical_source_status::exact;
  return result;
}

mathematical_source_result mount_relocated_mathematical_sources(
    const char* const* paths, std::size_t count, std::uint16_t chunk_aperture,
    const char* destination) noexcept {
  namespace fs = std::filesystem;
  std::error_code error{};
  fs::create_directories(destination, error);
  mathematical_source_result refused{};
  if (error || count != codec::mathematical_source_capacity) {
    refused.receipt.state = mathematical_source_status::relocation_refused;
    return refused;
  }
  fs::path relocated[codec::mathematical_source_capacity]{};
  const char* relocated_paths[codec::mathematical_source_capacity]{};
  for (std::size_t slot = 0; slot < count; ++slot) {
    const std::size_t source_slot = count - slot - 1U;
    relocated[slot] = fs::path{destination} /
        ("inherited_" + std::to_string(slot) + ".formal");
    fs::copy_file(paths[source_slot], relocated[slot],
        fs::copy_options::overwrite_existing, error);
    if (error) {
      refused.receipt.state = mathematical_source_status::relocation_refused;
      return refused;
    }
    relocated_paths[slot] = relocated[slot].c_str();
  }
  return mount_mathematical_sources(relocated_paths, count, chunk_aperture);
}

bool same_mathematical_material(
    const codec::mathematical_source_environment& left,
    const codec::mathematical_source_environment& right) noexcept {
  if (!left.admitted() || !right.admitted()) { return false; }
  const auto& a = left.encoded();
  const auto& b = right.encoded();
  if (a.source_count != b.source_count) { return false; }
  bool matched[codec::mathematical_source_capacity]{};
  for (std::size_t left_slot = 0; left_slot < a.source_count; ++left_slot) {
    bool found = false;
    for (std::size_t right_slot = 0; right_slot < b.source_count; ++right_slot) {
      if (!matched[right_slot] && same_buffer(a.sources[left_slot], b.sources[right_slot])) {
        matched[right_slot] = true;
        found = true;
        break;
      }
    }
    if (!found) { return false; }
  }
  return true;
}

}  // namespace holonics::apparatus

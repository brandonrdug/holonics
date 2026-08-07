#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>
#include <system_error>

#include <holonics/apparatus/source_store_adapter.hpp>
#include <holonics/structure/identity_mint.hpp>
#include <holonics/structure/occurrence.hpp>

namespace holonics::apparatus {
namespace {

void mix(std::uint64_t& fold, std::uint64_t value) noexcept {
  constexpr std::uint64_t prime = 1'099'511'628'211ULL;
  for (std::size_t octet = 0; octet < 8; ++octet) {
    fold ^= value & 255U;
    fold *= prime;
    value >>= 8U;
  }
}

[[nodiscard]] std::size_t physical_slot(
    std::size_t logical,
    std::size_t count,
    std::size_t order) noexcept {
  if (order == 1) {
    return count - logical - 1;
  }
  if (order == 2) {
    const std::size_t even_count = (count + 1) / 2;
    return (logical & 1U) == 0 ? logical / 2 : even_count + logical / 2;
  }
  if (order == 3) {
    return (logical + 7U) % count;
  }
  return logical;
}

[[nodiscard]] bool found_variants(codec::encoded_source_environment& encoded) noexcept {
  constexpr std::uint16_t apertures[codec::source_variant_capacity]{31U, 64U, 127U, 257U};
  std::size_t encoded_chunk_count = 0;
  for (std::size_t variant_slot = 0; variant_slot < codec::source_variant_capacity; ++variant_slot) {
    codec::encoded_source_chunk canonical[codec::source_chunk_capacity]{};
    std::size_t logical_count = 0;
    structure::identity_mint<structure::lineage_identity_owner> lineage_mint{
        9'000'000U + static_cast<std::uint64_t>(variant_slot) * 100'000U};
    for (std::size_t source_slot = 0; source_slot < encoded.source_count; ++source_slot) {
      const auto source = encoded.sources[source_slot];
      for (std::size_t begin = 0; begin < source.byte_count; begin += apertures[variant_slot]) {
        const std::size_t remaining = static_cast<std::size_t>(source.byte_count) - begin;
        const std::size_t count = remaining < apertures[variant_slot]
            ? remaining : apertures[variant_slot];
        auto& chunk = canonical[logical_count];
        chunk.source_slot = static_cast<std::uint16_t>(source_slot);
        chunk.local_begin = static_cast<std::uint16_t>(begin);
        chunk.byte_count = static_cast<std::uint16_t>(count);
        chunk.logical_slot = static_cast<std::uint16_t>(logical_count);
        chunk.cut_lineage = lineage_mint.mint().serial().value();
        ++logical_count;
      }
    }
    if (encoded_chunk_count + logical_count > codec::source_chunk_capacity || logical_count == 0) {
      return false;
    }
    auto& variant = encoded.variants[variant_slot];
    variant.chunk_begin = static_cast<std::uint16_t>(encoded_chunk_count);
    variant.chunk_count = static_cast<std::uint16_t>(logical_count);
    variant.chunk_aperture = apertures[variant_slot];
    variant.ingestion_order = static_cast<std::uint16_t>(variant_slot);
    variant.owner_seed = 20'000'000U;
    for (std::size_t logical = 0; logical < logical_count; ++logical) {
      const std::size_t physical = physical_slot(logical, logical_count, variant_slot);
      auto chunk = canonical[logical];
      const bool source_continues = chunk.local_begin + chunk.byte_count <
          encoded.sources[chunk.source_slot].byte_count;
      if (source_continues) {
        const std::size_t next = physical_slot(logical + 1, logical_count, variant_slot);
        chunk.next_chunk = static_cast<std::uint16_t>(encoded_chunk_count + next);
      }
      encoded.chunks[encoded_chunk_count + physical] = chunk;
    }
    encoded_chunk_count += logical_count;
  }
  encoded.chunk_count = static_cast<std::uint16_t>(encoded_chunk_count);
  return true;
}

[[nodiscard]] bool read_one(
    const char* path,
    codec::encoded_source_environment& encoded,
    std::size_t source_slot,
    source_store_receipt& receipt) noexcept {
  std::ifstream input{path, std::ios::binary};
  if (!input) {
    receipt.state = source_store_status::open_refused;
    return false;
  }
  const std::size_t begin = encoded.byte_count;
  char octet = 0;
  while (input.get(octet)) {
    if (encoded.byte_count == codec::source_byte_capacity) {
      receipt.state = source_store_status::capacity_refused;
      return false;
    }
    encoded.bytes[encoded.byte_count] = static_cast<unsigned char>(octet);
    mix(receipt.byte_testimony_fold, static_cast<unsigned char>(octet));
    ++encoded.byte_count;
  }
  if (!input.eof()) {
    receipt.state = source_store_status::read_refused;
    return false;
  }
  const std::size_t count = encoded.byte_count - begin;
  if (count == 0) {
    receipt.state = source_store_status::read_refused;
    return false;
  }
  auto& span = encoded.sources[source_slot];
  span.byte_begin = static_cast<std::uint16_t>(begin);
  span.byte_count = static_cast<std::uint16_t>(count);
  span.relation_begin = encoded.relation_count;
  span.cut_begin = static_cast<std::uint16_t>(begin + source_slot);
  encoded.relation_count = static_cast<std::uint16_t>(encoded.relation_count + count - 1);
  for (const char* cursor = path; *cursor != '\0'; ++cursor) {
    mix(receipt.path_testimony_fold, static_cast<unsigned char>(*cursor));
  }
  return true;
}

}  // namespace

source_store_result mount_source_store(const char* const* paths, std::size_t count) noexcept {
  source_store_result result{};
  result.receipt.path_testimony_fold = 14'695'981'039'346'656'037ULL;
  result.receipt.byte_testimony_fold = 14'695'981'039'346'656'037ULL;
  if (paths == nullptr || count == 0 || count > codec::source_span_capacity ||
      !result.environment.admitted()) {
    return result;
  }
  auto& encoded = result.environment.encoded();
  encoded.source_count = static_cast<std::uint16_t>(count);
  encoded.query_face = static_cast<std::uint8_t>('#');
  encoded.query_occurrence = 20'000'000U;
  for (std::size_t slot = 0; slot < count; ++slot) {
    if (!read_one(paths[slot], encoded, slot, result.receipt)) {
      return result;
    }
  }
  if (!found_variants(encoded)) {
    result.receipt.state = source_store_status::capacity_refused;
    return result;
  }
  result.receipt.state = source_store_status::exact;
  result.receipt.source_count = encoded.source_count;
  result.receipt.byte_count = encoded.byte_count;
  return result;
}

source_store_result mount_relocated_source_store(
    const char* const* paths,
    std::size_t count,
    const char* destination) noexcept {
  namespace fs = std::filesystem;
  std::error_code error{};
  fs::create_directories(destination, error);
  source_store_result refused{};
  if (error || count > codec::source_span_capacity) {
    refused.receipt.state = source_store_status::relocation_refused;
    return refused;
  }
  fs::path relocated[codec::source_span_capacity]{};
  const char* relocated_paths[codec::source_span_capacity]{};
  for (std::size_t slot = 0; slot < count; ++slot) {
    relocated[slot] = fs::path{destination} / ("source_" + std::to_string(slot) + ".bin");
    fs::copy_file(paths[slot], relocated[slot], fs::copy_options::overwrite_existing, error);
    if (error) {
      refused.receipt.state = source_store_status::relocation_refused;
      return refused;
    }
    relocated_paths[slot] = relocated[slot].c_str();
  }
  return mount_source_store(relocated_paths, count);
}

bool same_source_material(
    const codec::source_environment& left,
    const codec::source_environment& right) noexcept {
  if (!left.admitted() || !right.admitted()) {
    return false;
  }
  const auto& a = left.encoded();
  const auto& b = right.encoded();
  if (a.byte_count != b.byte_count || a.source_count != b.source_count ||
      a.relation_count != b.relation_count) {
    return false;
  }
  for (std::size_t slot = 0; slot < a.byte_count; ++slot) {
    if (a.bytes[slot] != b.bytes[slot]) {
      return false;
    }
  }
  return true;
}

}  // namespace holonics::apparatus

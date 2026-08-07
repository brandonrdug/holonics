#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/port.hpp>

namespace holonics::codec {

inline constexpr std::size_t source_byte_capacity = 16'384;
inline constexpr std::size_t source_span_capacity = 4;
inline constexpr std::size_t source_variant_capacity = 4;
inline constexpr std::size_t source_chunk_capacity = 2'048;
inline constexpr std::uint16_t no_chunk_slot = 65'535U;

struct encoded_source_span final {
  std::uint16_t byte_begin{};
  std::uint16_t byte_count{};
  std::uint16_t relation_begin{};
  std::uint16_t cut_begin{};
};

struct encoded_source_chunk final {
  std::uint16_t source_slot{};
  std::uint16_t local_begin{};
  std::uint16_t byte_count{};
  std::uint16_t next_chunk{no_chunk_slot};
  std::uint16_t logical_slot{};
  std::uint16_t reserved{};
  std::uint64_t cut_lineage{};
};

struct encoded_mount_variant final {
  std::uint16_t chunk_begin{};
  std::uint16_t chunk_count{};
  std::uint16_t chunk_aperture{};
  std::uint16_t ingestion_order{};
  std::uint64_t owner_seed{};
};

struct encoded_source_environment final {
  unsigned char bytes[source_byte_capacity]{};
  encoded_source_span sources[source_span_capacity]{};
  encoded_source_chunk chunks[source_chunk_capacity]{};
  encoded_mount_variant variants[source_variant_capacity]{};
  std::uint16_t byte_count{};
  std::uint16_t source_count{};
  std::uint16_t relation_count{};
  std::uint16_t chunk_count{};
  std::uint8_t query_face{};
  std::uint8_t obstruction_face{};
  std::uint64_t query_occurrence{};
};

using source_mount_port = structure::port<encoded_source_environment, structure::port_direction::inbound>;

enum class transduction_status : std::uint8_t {
  exact,
  capacity_refused,
  malformed_cut,
  incomplete_cover
};

struct transduction_receipt final {
  transduction_status state{transduction_status::exact};
  std::uint16_t chunks{};
  std::uint16_t local_relations{};
  std::uint16_t cross_cut_relations{};
  std::uint16_t boundary_summaries{};
  std::uint16_t source_bytes_visible{};
  std::uint64_t pair_fold{};
};

}  // namespace holonics::codec

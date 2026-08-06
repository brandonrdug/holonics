#pragma once

#include <cstdint>

#include <holonics/event/text_conditioning.hpp>

#include "text_mount_reserve.cuh"

namespace holonics::apparatus::text_mount {

using codec::text_arena;
using organ::incidence_arena;
using organ::suffix_arena;

struct text_query_return final {
  std::uint32_t state{};
  std::uint32_t matched{};
  std::uint32_t span_length{};
  std::uint32_t reaches_own{};
};

/// The resident query kernel. Every law it calls takes its arena by const
/// reference, so this path cannot found, link, freeze, or admit anything.
__global__ void text_query_kernel(
    const text_arena text,
    const suffix_arena suffix,
    const incidence_arena incidence,
    std::uint32_t query_paths,
    std::uint32_t octet_aperture,
    text_query_return* returns) {
  const std::uint32_t slot = blockIdx.x * blockDim.x + threadIdx.x;
  if (slot >= query_paths) {
    return;
  }
  const codec::text_occurrence& held = text.occurrences.at(slot);
  organ::suffix_symbol path[32]{};
  std::uint32_t held_extent = held.surface_extent < octet_aperture
      ? held.surface_extent
      : octet_aperture;
  held_extent = held_extent < 32U ? held_extent : 32U;
  for (std::uint32_t step = 0; step < held_extent; ++step) {
    path[step] = organ::suffix_symbol{organ::symbol_kind::germ,
        static_cast<std::uint64_t>(codec::text_law::octet(text, held, step))};
  }
  text_query_return answered{};
  answered.state =
      organ::suffix_law::follow_read(suffix, path, held_extent, answered.matched);
  answered.span_length = organ::incidence_law::span(incidence, answered.state).length;
  answered.reaches_own =
      organ::incidence_law::reaches(incidence, answered.state, slot) ? 1U : 0U;
  returns[slot] = answered;
}

[[nodiscard]] text_query_return host_query(
    const text_arena& text,
    const suffix_arena& suffix,
    const incidence_arena& incidence,
    std::uint32_t slot,
    std::uint32_t octet_aperture) noexcept {
  const codec::text_occurrence& held = text.occurrences.at(slot);
  organ::suffix_symbol path[32]{};
  std::uint32_t held_extent = held.surface_extent < octet_aperture
      ? held.surface_extent
      : octet_aperture;
  held_extent = held_extent < 32U ? held_extent : 32U;
  for (std::uint32_t step = 0; step < held_extent; ++step) {
    path[step] = organ::suffix_symbol{organ::symbol_kind::germ,
        static_cast<std::uint64_t>(codec::text_law::octet(text, held, step))};
  }
  text_query_return answered{};
  answered.state =
      organ::suffix_law::follow_read(suffix, path, held_extent, answered.matched);
  answered.span_length = organ::incidence_law::span(incidence, answered.state).length;
  answered.reaches_own =
      organ::incidence_law::reaches(incidence, answered.state, slot) ? 1U : 0U;
  return answered;
}

}  // namespace holonics::apparatus::text_mount

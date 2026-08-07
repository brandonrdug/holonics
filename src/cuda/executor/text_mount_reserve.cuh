#pragma once

#include <cstddef>
#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/text_material_mount.hpp>
#include <holonics/organ/incidence_arena.hpp>

namespace holonics::apparatus::text_mount {

/// The ownership state of one text host.
///
/// **Mounting consumes the host.** A consumed host refuses every later
/// admission, so an exterior caller cannot silently bind a second semantic world
/// to the same resident realization. A *refused* mount consumes nothing: the
/// exact predecessor is returned inside the refusal, because absent hardware or
/// a reservation obstruction must not destroy the only conditioned body merely
/// because success would have consumed it.
enum class host_state : std::uint8_t { standing, consumed, barred };

struct text_host final {
  codec::text_arena text{};
  host_state state{host_state::standing};
};

/// A refused mount, carrying its predecessor back out.
struct mount_refusal final {
  executor_status obstruction{executor_status::allocation_refused};
  bool predecessor_returned{};
};

/// One managed reservation. The apparatus owns every page; the interior only
/// ever receives the span.
template<class Value>
[[nodiscard]] inline bool try_reserve(
    structure::resident_span<Value>& span,
    std::uint32_t extent,
    std::uint64_t& octets) noexcept {
  void* pages = nullptr;
  const std::size_t width = sizeof(Value) * static_cast<std::size_t>(extent);
  if (extent == 0 || cudaMallocManaged(&pages, width) != cudaSuccess ||
      pages == nullptr) {
    return false;
  }
  if (cudaMemset(pages, 0, width) != cudaSuccess) {
    static_cast<void>(cudaFree(pages));
    return false;
  }
  span = structure::resident_span<Value>{static_cast<Value*>(pages), extent};
  octets = octets + static_cast<std::uint64_t>(width);
  return true;
}

inline void release(void* pages) noexcept {
  if (pages != nullptr) {
    static_cast<void>(cudaFree(pages));
  }
}

/// Admit one section through the host. A consumed host refuses.
[[nodiscard]] inline codec::text_admission admit(
    text_host& host,
    const text_section& section) noexcept {
  if (host.state != host_state::standing) {
    return codec::text_admission::capacity_refused;
  }
  return codec::text_law::try_admit(host.text, section.container, section.section,
      codec::text_role::document, codec::text_phase::received, section.octets,
      section.extent, nullptr, 0);
}

/// Attempt the ownership crossing. On success the host is consumed; on refusal
/// the host is untouched and the refusal says so.
[[nodiscard]] inline mount_refusal try_cross(text_host& host, bool reserved) noexcept {
  mount_refusal refusal{};
  if (!reserved) {
    refusal.obstruction = executor_status::allocation_refused;
    refusal.predecessor_returned = host.state == host_state::standing &&
        host.text.occurrences_used != 0;
    return refusal;
  }
  host.state = host_state::consumed;
  refusal.obstruction = executor_status::returned;
  return refusal;
}

/// Are these two text standings the same body, octet for octet and occurrence
/// for occurrence? The remount is graded against this and nothing weaker.
[[nodiscard]] inline bool same_standing(
    const codec::text_arena& left,
    const codec::text_arena& right) noexcept {
  if (left.surface_used != right.surface_used ||
      left.occurrences_used != right.occurrences_used ||
      left.caused_used != right.caused_used ||
      left.duplicate_witnesses != right.duplicate_witnesses ||
      left.version_fibers != right.version_fibers ||
      left.open_causal_fibers != right.open_causal_fibers) {
    return false;
  }
  for (std::uint32_t slot = 0; slot < left.surface_used; ++slot) {
    if (left.surface.at(slot) != right.surface.at(slot)) {
      return false;
    }
  }
  for (std::uint32_t slot = 0; slot < left.occurrences_used; ++slot) {
    const codec::text_occurrence& one = left.occurrences.at(slot);
    const codec::text_occurrence& other = right.occurrences.at(slot);
    if (one.native_identity != other.native_identity || one.version != other.version ||
        one.surface_start != other.surface_start ||
        one.surface_extent != other.surface_extent ||
        one.witness_multiplicity != other.witness_multiplicity ||
        one.container != other.container || one.caused_count != other.caused_count ||
        one.role != other.role || one.phase != other.phase) {
      return false;
    }
  }
  return true;
}

}  // namespace holonics::apparatus::text_mount

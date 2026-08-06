#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/organ/source_incidence.hpp>

namespace holonics::organ {

/// The five surface scales that live **simultaneously** in one conditioned body.
/// No interior surface-owning subsystem exists; a surface is one local face. They
/// are not a pipeline and none is primary: a question opens all of them at once,
/// and a token's transport records which of them actually supported it.
enum class surface_scale : std::uint8_t {
  lexical = 0,
  clause_lexical = 1,
  ordered_region = 2,
  forward_mark = 3,
  reverse_mark = 4
};

inline constexpr std::size_t surface_scale_count = 5;

/// What carried one generated token. **Support is plural**: the same visible
/// continuation may be carried by several scales at different matched lengths,
/// and those are retained as distinct supports rather than collapsed to a count.
struct token_transport final {
  std::uint32_t matched_length[surface_scale_count]{};
  std::uint32_t target_state[surface_scale_count]{};
  std::uint64_t recurrence[surface_scale_count]{};
  std::uint8_t supporting_scales{};
  std::uint64_t germ{};
};

/// How a response ended.
///
/// **Observer aperture exhaustion is explicitly not linguistic rest.** A
/// response that stopped because the observer ran out of aperture has open
/// obligations and must say so; reporting it as closed would be the listener's
/// limit masquerading as the body's completion.
enum class response_rest : std::uint8_t {
  closed,
  obstructed,
  observation_aperture_exhausted
};

struct surface_generation final {
  token_transport tokens[32]{};
  std::uint8_t token_count{};
  std::uint32_t open_obligations{};
  response_rest rest{response_rest::obstructed};
};

/// A census over the conditioned scales. Counts are physical testimony about the
/// conditioned body; none of them is a score and none gates admission.
struct scale_census final {
  std::uint32_t states[surface_scale_count]{};
  std::uint32_t transitions[surface_scale_count]{};
  std::uint32_t occurrences[surface_scale_count]{};
  std::uint32_t sources{};
  std::uint32_t passages{};
};

namespace morphological_law {

/// The **greatest productive matched length** across the open scales. This is
/// the restriction a question's front obeys: the longest scale that actually
/// supports a continuation governs, and shorter scales remain available rather
/// than being discarded.
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t greatest_productive(
    const token_transport& transport) noexcept {
  std::uint32_t longest = 0;
  for (std::size_t scale = 0; scale < surface_scale_count; ++scale) {
    if (transport.recurrence[scale] != 0 && transport.matched_length[scale] > longest) {
      longest = transport.matched_length[scale];
    }
  }
  return longest;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t supporting_count(
    const token_transport& transport) noexcept {
  std::uint8_t count = 0;
  for (std::size_t scale = 0; scale < surface_scale_count; ++scale) {
    count = static_cast<std::uint8_t>(count + (transport.recurrence[scale] != 0 ? 1U : 0U));
  }
  return count;
}

/// A token is admissible only where some scale actually carried it. **Absent
/// morphology emits nothing** — the body does not relabel a missing transport as
/// uncertainty and does not invent a continuation to fill a prompt.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool carried(
    const token_transport& transport) noexcept {
  return supporting_count(transport) != 0;
}

/// Close a generation. A response closes only when every open obligation has
/// returned; otherwise it is obstructed, and if the observer's aperture ran out
/// first that is reported as its own state.
[[nodiscard]] HOLONICS_CALLABLE constexpr response_rest close(
    std::uint32_t open_obligations,
    bool aperture_exhausted) noexcept {
  if (aperture_exhausted) {
    return response_rest::observation_aperture_exhausted;
  }
  return open_obligations == 0 ? response_rest::closed : response_rest::obstructed;
}

/// Admit one carried token into a generation.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_emit(
    surface_generation& generation,
    const token_transport& transport) noexcept {
  if (generation.token_count >= 32 || !carried(transport)) {
    return false;
  }
  generation.tokens[generation.token_count] = transport;
  generation.tokens[generation.token_count].supporting_scales =
      supporting_count(transport);
  generation.token_count = static_cast<std::uint8_t>(generation.token_count + 1U);
  return true;
}

/// Two tokens with the same visible germ but different supporting scales are
/// **different transports**. Collapsing them would erase which part of the body
/// carried the continuation.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_transport(
    const token_transport& left,
    const token_transport& right) noexcept {
  if (left.germ != right.germ) {
    return false;
  }
  for (std::size_t scale = 0; scale < surface_scale_count; ++scale) {
    if (left.matched_length[scale] != right.matched_length[scale] ||
        left.target_state[scale] != right.target_state[scale] ||
        left.recurrence[scale] != right.recurrence[scale]) {
      return false;
    }
  }
  return true;
}

}  // namespace morphological_law
}  // namespace holonics::organ

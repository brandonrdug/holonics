#pragma once

#include <cstdint>

#include <holonics/codec/reflective_runtime.hpp>
#include <holonics/event/relational_surface.hpp>

namespace holonics::event {

/// What may cross the mouth inward.
enum class mouth_occurrence : std::uint8_t {
  question,
  world_return,
  feedback,
  formal_return
};

/// What may cross outward.
enum class mouth_consequence : std::uint8_t {
  deed,
  answer,
  clarification,
  feedback,
  formal_return
};

/// The dialogue turn. A body awaiting a world return may not answer; partial
/// standing cannot close a question.
enum class turn_state : std::uint8_t {
  rest,
  awaiting_world_return,
  awaiting_clarification
};

/// A codec residual. **Input-only and output-only regions stay distinct** even
/// when an outer observer later assigns them one scalar loss. The two are
/// different obligations and merging them is how a correction's direction is
/// lost.
struct codec_residual final {
  std::uint32_t input_only_regions{};
  std::uint32_t output_only_regions{};
};

/// One crossing of the mouth.
///
/// The ports are **borrowed for this passage only and never enter standing or
/// native rest**. A body that retained its ports would be carrying the caller's
/// apparatus as if it were its own organ.
struct mouth_crossing final {
  mouth_occurrence received{mouth_occurrence::question};
  mouth_consequence returned{mouth_consequence::clarification};
  codec_residual residual{};
  std::uint32_t codec{codec::no_codec};
  bool ports_retained{};
  bool closed{};
};

namespace mouth_law {

/// The turn law. A question in rest opens a deed or answers. A world return is
/// admissible only while awaiting one. Feedback may arrive at any time and
/// founds a correction rather than an answer.
[[nodiscard]] HOLONICS_CALLABLE constexpr mouth_consequence respond(
    turn_state state,
    mouth_occurrence received,
    bool world_deed_required) noexcept {
  switch (received) {
    case mouth_occurrence::question:
      if (state != turn_state::rest) {
        return mouth_consequence::clarification;
      }
      return world_deed_required ? mouth_consequence::deed : mouth_consequence::answer;
    case mouth_occurrence::world_return:
      return state == turn_state::awaiting_world_return ? mouth_consequence::answer
                                                        : mouth_consequence::clarification;
    case mouth_occurrence::feedback:
      return mouth_consequence::feedback;
    case mouth_occurrence::formal_return:
      return mouth_consequence::formal_return;
  }
  return mouth_consequence::clarification;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr turn_state advance(
    turn_state state,
    mouth_consequence returned) noexcept {
  switch (returned) {
    case mouth_consequence::deed: return turn_state::awaiting_world_return;
    case mouth_consequence::clarification: return turn_state::awaiting_clarification;
    case mouth_consequence::answer: return turn_state::rest;
    default: return state;
  }
}

/// A crossing is admissible only when its ports departed with the passage.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool admissible(
    const mouth_crossing& crossing) noexcept {
  return !crossing.ports_retained;
}

/// A residual with only one side is still a residual. Reporting the pair as a
/// single magnitude would erase which side the correction came from.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool residual_directed(
    const codec_residual& residual) noexcept {
  return residual.input_only_regions != residual.output_only_regions;
}

}  // namespace mouth_law
}  // namespace holonics::event

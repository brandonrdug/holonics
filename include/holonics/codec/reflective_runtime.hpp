#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/local_population.hpp>

namespace holonics::codec {

inline constexpr std::uint32_t no_codec = 0xFFFF'FFFFU;
inline constexpr std::size_t parent_capacity = 4;

/// A codec version. It retains its **parents**, so a correction founds a child
/// rather than overwriting what it corrected, and both identities stay readable
/// on the successor.
struct codec_version final {
  std::uint32_t identity{no_codec};
  std::uint32_t parents[parent_capacity]{};
  std::uint8_t parent_count{};
  std::uint32_t caused_by{};
  std::uint64_t program{};
};

enum class continuation_state : std::uint8_t { running, reflected, rested, obstructed };
enum class reflection_state : std::uint8_t { open, revised, resumed_unchanged };

/// A continuation under a codec. The environment is **moved in and moved back
/// out on every step, including refusal** — that is what lets the runtime
/// recover without cloning standing.
struct reflective_continuation final {
  std::uint32_t identity{};
  std::uint32_t codec{no_codec};
  std::uint64_t instruction{};
  std::uint64_t environment{};
  continuation_state state{continuation_state::running};
};

struct reflection_frame final {
  std::uint32_t identity{};
  std::uint32_t continuation{};
  std::uint32_t codec{no_codec};
  std::uint64_t receiver{};
  reflection_state state{reflection_state::open};
  std::uint32_t revised_into{no_codec};
};

/// The reflective runtime.
///
/// Faces, parented codec versions, continuations, and reflection frames stay
/// distinct but causally connected. A revision **resumes the same continuation**
/// under a lineaged child codec; it does not restart it and does not discard the
/// parent. Not clonable.
template<std::size_t CodecCapacity, std::size_t ContinuationCapacity>
class reflective_runtime final {
  static_assert(CodecCapacity > 0 && ContinuationCapacity > 0);

 public:
  HOLONICS_CALLABLE constexpr reflective_runtime() noexcept
      : codecs_{}, continuations_{}, frames_{} {}
  reflective_runtime(const reflective_runtime&) = delete;
  reflective_runtime& operator=(const reflective_runtime&) = delete;
  reflective_runtime(reflective_runtime&&) = delete;
  reflective_runtime& operator=(reflective_runtime&&) = delete;

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t codecs() const noexcept {
    return codecs_used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const codec_version* codec(
      std::uint32_t identity) const noexcept {
    return identity < codecs_used_ ? &codecs_[identity] : nullptr;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const reflective_continuation* continuation(
      std::uint32_t identity) const noexcept {
    return identity < continuations_used_ ? &continuations_[identity] : nullptr;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const reflection_frame* frame(
      std::uint32_t identity) const noexcept {
    return identity < frames_used_ ? &frames_[identity] : nullptr;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t mount_codec(
      std::uint64_t program,
      std::uint32_t caused_by) noexcept {
    if (codecs_used_ >= CodecCapacity) {
      return no_codec;
    }
    codecs_[codecs_used_] = codec_version{codecs_used_, {}, 0, caused_by, program};
    const std::uint32_t minted = codecs_used_;
    codecs_used_ = codecs_used_ + 1U;
    return minted;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t open_continuation(
      std::uint32_t codec_identity,
      std::uint64_t environment) noexcept {
    if (continuations_used_ >= ContinuationCapacity || codec_identity >= codecs_used_) {
      return no_codec;
    }
    continuations_[continuations_used_] = reflective_continuation{
        continuations_used_, codec_identity, 0, environment,
        continuation_state::running};
    const std::uint32_t minted = continuations_used_;
    continuations_used_ = continuations_used_ + 1U;
    return minted;
  }

  /// Reflect: the continuation suspends and a frame stands OPEN. The environment
  /// is retained on the continuation, not consumed by the reflection.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t reflect(
      std::uint32_t continuation_identity,
      std::uint64_t receiver) noexcept {
    if (continuation_identity >= continuations_used_ || frames_used_ >= ContinuationCapacity) {
      return no_codec;
    }
    reflective_continuation& carried = continuations_[continuation_identity];
    frames_[frames_used_] = reflection_frame{frames_used_, continuation_identity,
        carried.codec, receiver, reflection_state::open, no_codec};
    carried.state = continuation_state::reflected;
    const std::uint32_t minted = frames_used_;
    frames_used_ = frames_used_ + 1U;
    return minted;
  }

  /// Revise and resume. A **parented child codec** is founded and the SAME
  /// continuation resumes under it, keeping its instruction and environment. The
  /// parent is retained and remains readable.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t revise_and_resume(
      std::uint32_t frame_identity,
      std::uint64_t replacement_program) noexcept {
    if (frame_identity >= frames_used_ || codecs_used_ >= CodecCapacity) {
      return no_codec;
    }
    reflection_frame& reflected = frames_[frame_identity];
    if (reflected.state != reflection_state::open) {
      return no_codec;
    }
    codec_version child{};
    child.identity = codecs_used_;
    child.parents[0] = reflected.codec;
    child.parent_count = 1;
    child.caused_by = frame_identity;
    child.program = replacement_program;
    codecs_[codecs_used_] = child;
    const std::uint32_t minted = codecs_used_;
    codecs_used_ = codecs_used_ + 1U;
    reflective_continuation& carried = continuations_[reflected.continuation];
    carried.codec = minted;
    carried.state = continuation_state::running;
    reflected.state = reflection_state::revised;
    reflected.revised_into = minted;
    return minted;
  }

  /// Resume unchanged. The reflection closes without founding a version; a
  /// correction that changed nothing must not manufacture lineage.
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool resume_unchanged(
      std::uint32_t frame_identity) noexcept {
    if (frame_identity >= frames_used_ ||
        frames_[frame_identity].state != reflection_state::open) {
      return false;
    }
    frames_[frame_identity].state = reflection_state::resumed_unchanged;
    continuations_[frames_[frame_identity].continuation].state =
        continuation_state::running;
    return true;
  }

  /// Does `descendant` carry `ancestor` in its lineage? Bounded by the codec
  /// population, so a malformed chain terminates.
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool descends_from(
      std::uint32_t descendant,
      std::uint32_t ancestor) const noexcept {
    std::uint32_t walk = descendant;
    for (std::uint32_t step = 0; step <= codecs_used_; ++step) {
      if (walk == ancestor) {
        return true;
      }
      if (walk >= codecs_used_ || codecs_[walk].parent_count == 0) {
        return false;
      }
      walk = codecs_[walk].parents[0];
    }
    return false;
  }

 private:
  codec_version codecs_[CodecCapacity]{};
  reflective_continuation continuations_[ContinuationCapacity]{};
  reflection_frame frames_[ContinuationCapacity]{};
  std::uint32_t codecs_used_{};
  std::uint32_t continuations_used_{};
  std::uint32_t frames_used_{};
};

}  // namespace holonics::codec

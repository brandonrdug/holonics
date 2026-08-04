#pragma once

#include <cstddef>
#include <cstdint>
#include <new>

#include <holonics/event/checker_pending_deed.hpp>

namespace holonics::event {
namespace checker_detail {

template<std::size_t Capacity, std::size_t Pattern>
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t count_pattern(
    const char (&bytes)[Capacity], std::uint16_t used, const char (&pattern)[Pattern]) noexcept {
  constexpr std::size_t payload = Pattern - 1U;
  std::uint16_t count = 0;
  if (payload == 0 || used < payload) { return count; }
  for (std::size_t start = 0; start + payload <= used; ++start) {
    bool same = true;
    for (std::size_t slot = 0; slot < payload; ++slot) {
      same = same && bytes[start + slot] == pattern[slot];
    }
    if (same) { ++count; }
  }
  return count;
}

template<std::size_t Capacity, std::size_t Pattern>
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t first_pattern(
    const char (&bytes)[Capacity], std::uint16_t used, const char (&pattern)[Pattern]) noexcept {
  constexpr std::size_t payload = Pattern - 1U;
  if (payload == 0 || used < payload) { return used; }
  for (std::size_t start = 0; start + payload <= used; ++start) {
    bool same = true;
    for (std::size_t slot = 0; slot < payload; ++slot) {
      same = same && bytes[start + slot] == pattern[slot];
    }
    if (same) { return static_cast<std::uint16_t>(start); }
  }
  return used;
}

}  // namespace checker_detail

class resident_checker_current final {
 public:
  resident_checker_current() = delete;
  resident_checker_current(const resident_checker_current&) = delete;
  resident_checker_current& operator=(const resident_checker_current&) = delete;
  resident_checker_current(resident_checker_current&&) = delete;
  resident_checker_current& operator=(resident_checker_current&&) = delete;

  HOLONICS_CALLABLE resident_checker_current(std::uint64_t seed, const body::rest_region* regions,
      std::uint64_t mathematical_morphology, std::uint64_t codec_morphology) noexcept
      : body_(seed, regions), mathematical_morphology_(mathematical_morphology),
        codec_morphology_(codec_morphology) {}

  [[nodiscard]] HOLONICS_CALLABLE checker_stage_status stage(
      const codec::formal_math_face& source, checker_observation& observation) noexcept {
    if (pending_live_) { return checker_stage_status::already_pending; }
    if (!codec::render_formal_checker_face(source, observation.checker_face)) {
      return checker_stage_status::invalid_source;
    }
    if (!body_.can_open()) { return checker_stage_status::continuation_unavailable; }
    checker_outbound_occurrence outbound{body_.head(), exact::word{160'100},
        exact::word{160'101}, exact::word{160'102}, exact::word{160'103},
        exact::word{160'104}, source.passage, source.identity};
    ::new (static_cast<void*>(pending_storage_)) checker_pending_deed{
        body_.take_continuation(), outbound};
    pending_live_ = true;
    observation.outbound = outbound;
    observation.stage = checker_stage_status::exact;
    observation.pending_before_process = true;
    return observation.stage;
  }

  [[nodiscard]] HOLONICS_CALLABLE bool resume(
      const checker_raw_return& raw, checker_observation& observation) noexcept {
    observation.raw = raw;
    auto* pending = live_pending();
    if (pending == nullptr || !pending->resumable()) { return false; }
    const auto expected = pending->outbound();
    auto& typed = observation.typed;
    typed.passage = raw.passage;
    typed.source = raw.source;
    const bool lineage_exact = raw.predecessor == expected.predecessor &&
        raw.event == expected.event && raw.port == expected.expected_return_port &&
        raw.lineage.value() == expected.lineage.value() + 1U &&
        raw.passage == expected.passage && raw.source == expected.source;
    if (!lineage_exact) {
      typed.state = checker_return_status::passage_mismatch;
      return false;
    }
    normalize(raw, observation.checker_face, typed);
    const bool accepted = typed.state == checker_return_status::accepted;
    observation.morphology.mathematical_before = mathematical_morphology_;
    observation.morphology.codec_before = codec_morphology_;
    mathematical_morphology_ += accepted ? 3U : 1U;
    codec_morphology_ += accepted ? 2U : 3U;
    const std::uint64_t delta = accepted ? 5U : 4U;
    observation.morphology.commit = body_.commit(expected.predecessor, 0, delta,
        expected.passage.value(), pending->take_continuation());
    pending_live_ = false;
    observation.morphology.mathematical_after = mathematical_morphology_;
    observation.morphology.codec_after = codec_morphology_;
    observation.morphology.returned_difference_applied =
        observation.morphology.commit.state == body::body_change_status::committed;
    observation.pending_after_return = pending_live_;
    observation.passage_preserved = typed.passage == expected.passage &&
        observation.checker_face.passage == expected.passage;
    return observation.morphology.returned_difference_applied;
  }

 private:
  [[nodiscard]] HOLONICS_CALLABLE checker_pending_deed* live_pending() noexcept {
    return pending_live_ ? reinterpret_cast<checker_pending_deed*>(pending_storage_) : nullptr;
  }

  HOLONICS_CALLABLE static void normalize(const checker_raw_return& raw,
      const codec::formal_checker_face& face, checker_typed_return& typed) noexcept {
    constexpr char declaration[] = "theorem Soma.Holonics.generated_semantics_rebase_reverse";
    constexpr char theorem_source[] = "theorem generated_semantics_rebase_reverse";
    constexpr char unsolved[] = "unsolved goals";
    typed.produced_declarations = checker_detail::count_pattern(
        raw.standard_output, raw.stdout_bytes, declaration);
    typed.remaining_goal_count = checker_detail::count_pattern(
        raw.standard_error, raw.stderr_bytes, unsolved);
    typed.message_bytes = static_cast<std::uint16_t>(raw.stdout_bytes + raw.stderr_bytes);
    typed.source_span_begin = checker_detail::first_pattern(
        face.bytes, face.byte_count, theorem_source);
    typed.source_span_end = typed.source_span_begin == face.byte_count ? face.byte_count :
        static_cast<std::uint16_t>(typed.source_span_begin + sizeof(theorem_source) - 1U);
    typed.elaborator_boundary_crossed = raw.launched && raw.exited;
    typed.kernel_boundary_crossed = raw.exit_status == 0 &&
        typed.remaining_goal_count == 0 && typed.produced_declarations == 1 &&
        raw.produced_artifact_bytes != 0;
    if (!raw.launched || !raw.exited) { typed.state = checker_return_status::process_refused; }
    else if (typed.remaining_goal_count != 0) { typed.state = checker_return_status::remaining_goals; }
    else if (typed.kernel_boundary_crossed) { typed.state = checker_return_status::accepted; }
    else { typed.state = checker_return_status::rejected; }
  }

  body::continuing_body body_;
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(checker_pending_deed)]{};
  std::uint64_t mathematical_morphology_{};
  std::uint64_t codec_morphology_{};
  bool pending_live_{};
};

}  // namespace holonics::event

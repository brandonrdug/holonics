#pragma once

#include <cstddef>
#include <cstdint>
#include <new>

#include <holonics/event/checker_normalization_law.hpp>
#include <holonics/event/checker_pending_deed.hpp>

namespace holonics::event {
class resident_checker_current final {
 public:
  resident_checker_current() = delete;
  resident_checker_current(const resident_checker_current&) = delete;
  resident_checker_current& operator=(const resident_checker_current&) = delete;
  resident_checker_current(resident_checker_current&&) = delete;
  resident_checker_current& operator=(resident_checker_current&&) = delete;

  HOLONICS_CALLABLE resident_checker_current(std::uint64_t seed, const body::rest_region* regions,
      std::uint64_t mathematical_admitted_tally, std::uint64_t codec_admitted_tally) noexcept
      : body_(seed, regions), mathematical_admitted_tally_(mathematical_admitted_tally),
        codec_admitted_tally_(codec_admitted_tally) {}

  [[nodiscard]] HOLONICS_CALLABLE checker_stage_status stage(
      const codec::formal_math_face& source, checker_observation& observation) noexcept {
    if (pending_live_) { return checker_stage_status::already_pending; }
    if (!codec::render_formal_checker_face(source,
        codec::formal_declaration_form::reverse_rebase, observation.checker_face)) {
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
    normalize_checker_return(raw, observation.checker_face, typed);
    const bool accepted = typed.state == checker_return_status::accepted;
    observation.morphology.mathematical_before = mathematical_admitted_tally_;
    observation.morphology.codec_before = codec_admitted_tally_;
    mathematical_admitted_tally_ += accepted ? 3U : 1U;
    codec_admitted_tally_ += accepted ? 2U : 3U;
    const std::uint64_t delta = accepted ? 5U : 4U;
    observation.morphology.commit = body_.commit(expected.predecessor, 0, delta,
        expected.passage.value(), pending->take_continuation());
    pending_live_ = false;
    observation.morphology.mathematical_after = mathematical_admitted_tally_;
    observation.morphology.codec_after = codec_admitted_tally_;
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

  body::continuing_body body_;
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(checker_pending_deed)]{};
  std::uint64_t mathematical_admitted_tally_{};
  std::uint64_t codec_admitted_tally_{};
  bool pending_live_{};
};

}  // namespace holonics::event

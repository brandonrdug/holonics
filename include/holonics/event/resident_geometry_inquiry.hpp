#pragma once

#include <new>
#include <type_traits>

#include <holonics/codec/geometry_theory_renderer.hpp>
#include <holonics/event/checker_pending_deed.hpp>
#include <holonics/event/geometry_checker_normalization_law.hpp>
#include <holonics/event/geometry_inquiry_return.hpp>
#include <holonics/organ/geometry_inquiry_law.hpp>

namespace holonics::event {

class resident_geometry_inquiry final {
 public:
  resident_geometry_inquiry() = delete;
  resident_geometry_inquiry(const resident_geometry_inquiry&) = delete;
  resident_geometry_inquiry& operator=(const resident_geometry_inquiry&) = delete;
  resident_geometry_inquiry(resident_geometry_inquiry&&) = delete;
  resident_geometry_inquiry& operator=(resident_geometry_inquiry&&) = delete;

  HOLONICS_CALLABLE resident_geometry_inquiry(
      const organ::geometry_inquiry_foundation& foundation,
      const terminal_theorem_rest_record& record,
      terminal_theorem_remount_receipt& receipt) noexcept
      : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
        first_(record.first), second_(record.second),
        mathematical_admitted_tally_(record.mathematical_admitted_tally),
        codec_admitted_tally_(record.codec_admitted_tally), source_detached_(true) {
    const bool exact = record.integrity == terminal_theorem_rest_integrity(record);
    receipt.first_fiber = first_.identity;
    receipt.second_fiber = second_.identity;
    receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
    receipt.both_returns_preserved = exact && first_.accepted && second_.accepted;
    receipt.source_replayed = receipt.body.source_replay_count != 0;
    admitted_ = exact && receipt.both_returns_preserved &&
        organ::valid_geometry_inquiry_foundation(foundation_);
  }

  HOLONICS_CALLABLE resident_geometry_inquiry(
      const organ::geometry_inquiry_foundation& foundation,
      const geometry_inquiry_rest_record& record,
      geometry_inquiry_remount_receipt& receipt) noexcept
      : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
        first_(record.first), second_(record.second), geometry_(record.geometry),
        mathematical_admitted_tally_(record.mathematical_admitted_tally),
        codec_admitted_tally_(record.codec_admitted_tally),
        geometry_admitted_tally_(record.geometry_admitted_tally), source_detached_(true) {
    const bool exact = record.integrity == geometry_inquiry_rest_integrity(record);
    receipt.theory = geometry_.identity;
    receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
    receipt.theory_preserved = exact && geometry_.accepted;
    receipt.source_replayed = receipt.body.source_replay_count != 0;
    admitted_ = exact && receipt.theory_preserved &&
        organ::valid_geometry_inquiry_foundation(foundation_);
  }

  [[nodiscard]] HOLONICS_CALLABLE bool admitted() const noexcept { return admitted_; }
  [[nodiscard]] HOLONICS_CALLABLE bool can_continue() const noexcept { return body_.can_open(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word head() const noexcept { return body_.head(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word continuation() const noexcept {
    return body_.continuation_serial();
  }

  [[nodiscard]] HOLONICS_CALLABLE bool form(
      const organ::geometry_inquiry_question& question,
      geometry_inquiry_observation& observation) noexcept {
    if (!admitted_) { return false; }
    organ::close_geometry_inquiry(foundation_, question, observation.inquiry);
    const auto& plan = observation.inquiry.theory;
    const codec::geometry_theory_surface surface{plan.passage, plan.auxiliary_statement,
        plan.affine_statement, plan.fractional_statement, plan.counterexample_statement,
        plan.difference_factor, plan.affine_common_square, plan.fractional_invariance,
        plan.coordinate_counterexample, plan.singular_boundary};
    if (!observation.inquiry.theory_formed ||
        !codec::render_geometry_theory(surface, observation.formal) ||
        !codec::render_geometry_explanation(surface, observation.conversational)) {
      observation.inquiry.obstruction = organ::geometry_inquiry_obstruction::render_refused;
      return false;
    }
    auto continuation = body_.take_continuation();
    observation.theory_commit = body_.commit(body_.head(), 0, 8, plan.passage.value(),
        static_cast<body::linear_continuation&&>(continuation));
    if (observation.theory_commit.state != body::body_change_status::committed) {
      observation.inquiry.obstruction = organ::geometry_inquiry_obstruction::continuation_refused;
      return false;
    }
    checker_outbound_occurrence outbound{body_.head(), exact::word{160'400},
        exact::word{160'401}, exact::word{160'402}, exact::word{160'403},
        exact::word{160'404}, plan.passage, observation.formal.identity};
    ::new (static_cast<void*>(pending_storage_)) checker_pending_deed{
        body_.take_continuation(), outbound};
    pending_live_ = true;
    observation.outbound = outbound;
    observation.checker_stage = checker_stage_status::exact;
    observation.pending_before_process = true;
    return true;
  }

  [[nodiscard]] HOLONICS_CALLABLE bool resume(
      const checker_raw_return& raw, geometry_inquiry_observation& observation) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE geometry_inquiry_rest_receipt rest(
      geometry_inquiry_rest_record& record) noexcept;

 private:
  [[nodiscard]] HOLONICS_CALLABLE checker_pending_deed* live_pending() noexcept {
    return pending_live_ ? reinterpret_cast<checker_pending_deed*>(pending_storage_) : nullptr;
  }

  organ::geometry_inquiry_foundation foundation_{};
  body::continuing_body body_;
  organ::acquired_theorem_fiber first_{};
  organ::acquired_theorem_fiber second_{};
  organ::acquired_geometry_theory geometry_{};
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(checker_pending_deed)]{};
  std::uint64_t mathematical_admitted_tally_{};
  std::uint64_t codec_admitted_tally_{};
  std::uint64_t geometry_admitted_tally_{};
  bool source_detached_{};
  bool pending_live_{};
  bool admitted_{};
};

static_assert(std::is_trivially_destructible_v<resident_geometry_inquiry>);

}  // namespace holonics::event

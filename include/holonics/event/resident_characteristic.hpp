#pragma once

#include <new>
#include <type_traits>

#include <holonics/codec/characteristic_renderer.hpp>
#include <holonics/event/characteristic_checker_normalization_law.hpp>
#include <holonics/event/checker_pending_deed.hpp>
#include <holonics/organ/characteristic_law.hpp>

namespace holonics::event {

class resident_characteristic final {
 public:
  resident_characteristic() = delete;
  resident_characteristic(const resident_characteristic&) = delete;
  resident_characteristic& operator=(const resident_characteristic&) = delete;
  resident_characteristic(resident_characteristic&&) = delete;
  resident_characteristic& operator=(resident_characteristic&&) = delete;

  HOLONICS_CALLABLE resident_characteristic(
      const organ::characteristic_foundation& foundation,
      const phase_crystal_rest_record& record,
      phase_crystal_remount_receipt& receipt) noexcept
      : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
        first_(record.first), second_(record.second), geometry_(record.geometry),
        phase_crystal_(record.phase_crystal),
        mathematical_admitted_tally_(record.mathematical_admitted_tally),
        codec_admitted_tally_(record.codec_admitted_tally),
        geometry_admitted_tally_(record.geometry_admitted_tally),
        phase_admitted_tally_(record.phase_admitted_tally), source_detached_(true) {
    const bool exact = record.integrity == phase_crystal_rest_integrity(record);
    receipt.atlas = phase_crystal_.identity;
    receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
    receipt.atlas_preserved = exact && phase_crystal_.accepted;
    receipt.source_replayed = receipt.body.source_replay_count != 0;
    admitted_ = exact && receipt.atlas_preserved &&
        organ::characteristic_detail::valid_foundation(foundation_);
  }

  HOLONICS_CALLABLE resident_characteristic(
      const organ::characteristic_foundation& foundation,
      const characteristic_rest_record& record,
      characteristic_remount_receipt& receipt) noexcept
      : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
        first_(record.first), second_(record.second), geometry_(record.geometry),
        phase_crystal_(record.phase_crystal), characteristic_(record.characteristic),
        mathematical_admitted_tally_(record.mathematical_admitted_tally),
        codec_admitted_tally_(record.codec_admitted_tally),
        geometry_admitted_tally_(record.geometry_admitted_tally),
        phase_admitted_tally_(record.phase_admitted_tally),
        characteristic_admitted_tally_(record.characteristic_admitted_tally), source_detached_(true) {
    const bool exact = record.integrity == characteristic_rest_integrity(record);
    receipt.theory = characteristic_.identity;
    receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
    receipt.theory_preserved = exact && characteristic_.accepted;
    receipt.source_replayed = receipt.body.source_replay_count != 0;
    admitted_ = exact && receipt.theory_preserved &&
        organ::characteristic_detail::valid_foundation(foundation_);
  }

  [[nodiscard]] HOLONICS_CALLABLE bool admitted() const noexcept { return admitted_; }
  [[nodiscard]] HOLONICS_CALLABLE bool can_continue() const noexcept { return body_.can_open(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word head() const noexcept { return body_.head(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word continuation() const noexcept {
    return body_.continuation_serial();
  }

  [[nodiscard]] HOLONICS_CALLABLE bool form(const organ::characteristic_question& question,
      characteristic_observation& observation) noexcept {
    if (!admitted_) { return false; }
    organ::close_characteristic_inquiry(foundation_, question, observation.inquiry);
    const auto& plan = observation.inquiry.theory;
    const codec::characteristic_surface surface{plan.passage, plan.diagonal_factor,
        plan.weighted_cycle, plan.matrix_controls, plan.discriminants_typed,
        plan.gauss_indicial, plan.lineage_retained};
    if (!observation.inquiry.theory_formed ||
        !codec::render_characteristic_theory(surface, observation.formal) ||
        !codec::render_characteristic_explanation(surface, observation.conversational)) {
      observation.inquiry.obstruction = organ::characteristic_obstruction::render_refused;
      return false;
    }
    auto continuation = body_.take_continuation();
    observation.formation_commit = body_.commit(body_.head(), 0, 13,
        plan.passage.value(), static_cast<body::linear_continuation&&>(continuation));
    if (observation.formation_commit.state != body::body_change_status::committed) {
      observation.inquiry.obstruction = organ::characteristic_obstruction::continuation_refused;
      return false;
    }
    checker_outbound_occurrence outbound{body_.head(), exact::word{160'600},
        exact::word{160'601}, exact::word{160'602}, exact::word{160'603},
        exact::word{160'604}, plan.passage, observation.formal.identity};
    ::new (static_cast<void*>(pending_storage_)) checker_pending_deed{
        body_.take_continuation(), outbound};
    pending_live_ = true;
    observation.outbound = outbound;
    observation.checker_stage = checker_stage_status::exact;
    observation.pending_before_process = true;
    return true;
  }

  [[nodiscard]] HOLONICS_CALLABLE bool resume(
      const checker_raw_return& raw, characteristic_observation& observation) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE characteristic_rest_receipt rest(
      characteristic_rest_record& record) noexcept;

 private:
  [[nodiscard]] HOLONICS_CALLABLE checker_pending_deed* live_pending() noexcept {
    return pending_live_ ? reinterpret_cast<checker_pending_deed*>(pending_storage_) : nullptr;
  }

  organ::characteristic_foundation foundation_{};
  body::continuing_body body_;
  organ::acquired_theorem_fiber first_{};
  organ::acquired_theorem_fiber second_{};
  organ::acquired_geometry_theory geometry_{};
  organ::acquired_phase_crystal phase_crystal_{};
  organ::acquired_characteristic characteristic_{};
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(checker_pending_deed)]{};
  std::uint64_t mathematical_admitted_tally_{};
  std::uint64_t codec_admitted_tally_{};
  std::uint64_t geometry_admitted_tally_{};
  std::uint64_t phase_admitted_tally_{};
  std::uint64_t characteristic_admitted_tally_{};
  bool source_detached_{};
  bool pending_live_{};
  bool admitted_{};
};

static_assert(std::is_trivially_destructible_v<resident_characteristic>);

}  // namespace holonics::event

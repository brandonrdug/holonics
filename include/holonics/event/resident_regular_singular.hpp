#pragma once

#include <new>
#include <type_traits>

#include <holonics/codec/regular_singular_renderer.hpp>
#include <holonics/event/checker_pending_deed.hpp>
#include <holonics/event/regular_singular_checker_normalization_law.hpp>
#include <holonics/organ/regular_singular_law.hpp>

namespace holonics::event {

class resident_regular_singular final {
 public:
  resident_regular_singular() = delete;
  resident_regular_singular(const resident_regular_singular&) = delete;
  resident_regular_singular& operator=(const resident_regular_singular&) = delete;
  resident_regular_singular(resident_regular_singular&&) = delete;
  resident_regular_singular& operator=(resident_regular_singular&&) = delete;

  HOLONICS_CALLABLE resident_regular_singular(
      const organ::regular_singular_foundation& foundation,
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
        organ::regular_singular_detail::valid_foundation(foundation_);
  }

  HOLONICS_CALLABLE resident_regular_singular(
      const organ::regular_singular_foundation& foundation,
      const regular_singular_rest_record& record,
      regular_singular_remount_receipt& receipt) noexcept
      : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
        first_(record.first), second_(record.second), geometry_(record.geometry),
        phase_crystal_(record.phase_crystal), characteristic_(record.characteristic),
        regular_singular_(record.regular_singular),
        mathematical_admitted_tally_(record.mathematical_admitted_tally),
        codec_admitted_tally_(record.codec_admitted_tally),
        geometry_admitted_tally_(record.geometry_admitted_tally),
        phase_admitted_tally_(record.phase_admitted_tally),
        characteristic_admitted_tally_(record.characteristic_admitted_tally),
        regular_singular_admitted_tally_(record.regular_singular_admitted_tally),
        source_detached_(true) {
    const bool exact = record.integrity == regular_singular_rest_integrity(record);
    receipt.theory = regular_singular_.identity;
    receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
    receipt.theory_preserved = exact && regular_singular_.accepted;
    receipt.source_replayed = receipt.body.source_replay_count != 0;
    admitted_ = exact && receipt.theory_preserved &&
        organ::regular_singular_detail::valid_foundation(foundation_);
  }

  [[nodiscard]] HOLONICS_CALLABLE bool admitted() const noexcept { return admitted_; }
  [[nodiscard]] HOLONICS_CALLABLE bool can_continue() const noexcept { return body_.can_open(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word head() const noexcept { return body_.head(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word continuation() const noexcept {
    return body_.continuation_serial();
  }

  [[nodiscard]] HOLONICS_CALLABLE bool form(
      const organ::regular_singular_question& question,
      regular_singular_observation& observation) noexcept {
    if (!admitted_) { return false; }
    organ::close_regular_singular_inquiry(foundation_, question, observation.inquiry);
    const auto& plan = observation.inquiry.theory;
    const codec::regular_singular_surface surface{plan.passage, plan.residue_algebra,
        plan.frobenius_steps, plan.resonance_obstruction, plan.chamber_connection,
        plan.loop_product, plan.lineage_retained};
    if (!observation.inquiry.theory_formed ||
        !codec::render_regular_singular_theory(surface, observation.formal) ||
        !codec::render_regular_singular_explanation(surface, observation.conversational)) {
      observation.inquiry.obstruction = organ::regular_singular_obstruction::render_refused;
      return false;
    }
    auto continuation = body_.take_continuation();
    observation.formation_commit = body_.commit(body_.head(), 0, 14,
        plan.passage.value(), static_cast<body::linear_continuation&&>(continuation));
    if (observation.formation_commit.state != body::body_change_status::committed) {
      observation.inquiry.obstruction =
          organ::regular_singular_obstruction::continuation_refused;
      return false;
    }
    checker_outbound_occurrence outbound{body_.head(), exact::word{160'700},
        exact::word{160'701}, exact::word{160'702}, exact::word{160'703},
        exact::word{160'704}, plan.passage, observation.formal.identity};
    ::new (static_cast<void*>(pending_storage_)) checker_pending_deed{
        body_.take_continuation(), outbound};
    pending_live_ = true;
    observation.outbound = outbound;
    observation.checker_stage = checker_stage_status::exact;
    observation.pending_before_process = true;
    return true;
  }

  [[nodiscard]] HOLONICS_CALLABLE bool resume(
      const checker_raw_return& raw, regular_singular_observation& observation) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE regular_singular_rest_receipt rest(
      regular_singular_rest_record& record) noexcept;

 private:
  [[nodiscard]] HOLONICS_CALLABLE checker_pending_deed* live_pending() noexcept {
    return pending_live_ ? reinterpret_cast<checker_pending_deed*>(pending_storage_) : nullptr;
  }

  organ::regular_singular_foundation foundation_{};
  body::continuing_body body_;
  organ::acquired_theorem_fiber first_{};
  organ::acquired_theorem_fiber second_{};
  organ::acquired_geometry_theory geometry_{};
  organ::acquired_phase_crystal phase_crystal_{};
  organ::acquired_characteristic characteristic_{};
  organ::acquired_regular_singular regular_singular_{};
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(checker_pending_deed)]{};
  std::uint64_t mathematical_admitted_tally_{};
  std::uint64_t codec_admitted_tally_{};
  std::uint64_t geometry_admitted_tally_{};
  std::uint64_t phase_admitted_tally_{};
  std::uint64_t characteristic_admitted_tally_{};
  std::uint64_t regular_singular_admitted_tally_{};
  bool source_detached_{};
  bool pending_live_{};
  bool admitted_{};
};

static_assert(std::is_trivially_destructible_v<resident_regular_singular>);

}  // namespace holonics::event

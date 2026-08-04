#pragma once

#include <new>
#include <type_traits>

#include <holonics/codec/phase_crystal_renderer.hpp>
#include <holonics/event/checker_pending_deed.hpp>
#include <holonics/event/phase_crystal_checker_normalization_law.hpp>
#include <holonics/organ/phase_crystal_law.hpp>

namespace holonics::event {

class resident_phase_crystal final {
 public:
  resident_phase_crystal() = delete;
  resident_phase_crystal(const resident_phase_crystal&) = delete;
  resident_phase_crystal& operator=(const resident_phase_crystal&) = delete;
  resident_phase_crystal(resident_phase_crystal&&) = delete;
  resident_phase_crystal& operator=(resident_phase_crystal&&) = delete;

  HOLONICS_CALLABLE resident_phase_crystal(
      const organ::phase_crystal_foundation& foundation,
      const geometry_inquiry_rest_record& record,
      geometry_inquiry_remount_receipt& receipt) noexcept
      : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
        first_(record.first), second_(record.second), geometry_(record.geometry),
        mathematical_morphology_(record.mathematical_morphology),
        codec_morphology_(record.codec_morphology),
        geometry_morphology_(record.geometry_morphology), source_detached_(true) {
    const bool exact = record.integrity == geometry_inquiry_rest_integrity(record);
    receipt.theory = geometry_.identity;
    receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
    receipt.theory_preserved = exact && geometry_.accepted;
    receipt.source_replayed = receipt.body.source_replay_count != 0;
    admitted_ = exact && receipt.theory_preserved &&
        organ::valid_phase_crystal_foundation(foundation_);
  }

  HOLONICS_CALLABLE resident_phase_crystal(
      const organ::phase_crystal_foundation& foundation,
      const phase_crystal_rest_record& record,
      phase_crystal_remount_receipt& receipt) noexcept
      : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
        first_(record.first), second_(record.second), geometry_(record.geometry),
        phase_crystal_(record.phase_crystal),
        mathematical_morphology_(record.mathematical_morphology),
        codec_morphology_(record.codec_morphology),
        geometry_morphology_(record.geometry_morphology),
        phase_morphology_(record.phase_morphology), source_detached_(true) {
    const bool exact = record.integrity == phase_crystal_rest_integrity(record);
    receipt.atlas = phase_crystal_.identity;
    receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
    receipt.atlas_preserved = exact && phase_crystal_.accepted;
    receipt.source_replayed = receipt.body.source_replay_count != 0;
    admitted_ = exact && receipt.atlas_preserved &&
        organ::valid_phase_crystal_foundation(foundation_);
  }

  [[nodiscard]] HOLONICS_CALLABLE bool admitted() const noexcept { return admitted_; }
  [[nodiscard]] HOLONICS_CALLABLE bool can_continue() const noexcept { return body_.can_open(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word head() const noexcept { return body_.head(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word continuation() const noexcept {
    return body_.continuation_serial();
  }

  [[nodiscard]] HOLONICS_CALLABLE bool form(const organ::phase_crystal_question& question,
      phase_crystal_observation& observation) noexcept {
    if (!admitted_) { return false; }
    organ::close_phase_crystal_inquiry(foundation_, question, observation.inquiry);
    const auto& plan = observation.inquiry.theory;
    const codec::phase_crystal_surface surface{plan.passage, plan.diagonal_statement,
        plan.coprime_statement, plan.population_statement, plan.series_statement,
        plan.diagonal_lcm, plan.coprime_full_tour, plan.cell_population_product,
        plan.seam_cancellation, plan.gauss_transport, plan.projection_distinguished};
    if (!observation.inquiry.theory_formed ||
        !codec::render_phase_crystal_theory(surface, observation.formal) ||
        !codec::render_phase_crystal_explanation(surface, observation.conversational)) {
      observation.inquiry.obstruction = organ::phase_crystal_obstruction::render_refused;
      return false;
    }
    auto continuation = body_.take_continuation();
    observation.formation_commit = body_.commit(body_.head(), 0, 12,
        observation.inquiry.theory.passage.value(),
        static_cast<body::linear_continuation&&>(continuation));
    if (observation.formation_commit.state != body::body_change_status::committed) {
      observation.inquiry.obstruction = organ::phase_crystal_obstruction::continuation_refused;
      return false;
    }
    checker_outbound_occurrence outbound{body_.head(), exact::word{160'500},
        exact::word{160'501}, exact::word{160'502}, exact::word{160'503},
        exact::word{160'504}, observation.inquiry.theory.passage, observation.formal.identity};
    ::new (static_cast<void*>(pending_storage_)) checker_pending_deed{
        body_.take_continuation(), outbound};
    pending_live_ = true;
    observation.outbound = outbound;
    observation.checker_stage = checker_stage_status::exact;
    observation.pending_before_process = true;
    return true;
  }

  [[nodiscard]] HOLONICS_CALLABLE bool resume(
      const checker_raw_return& raw, phase_crystal_observation& observation) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE phase_crystal_rest_receipt rest(
      phase_crystal_rest_record& record) noexcept;

 private:
  [[nodiscard]] HOLONICS_CALLABLE checker_pending_deed* live_pending() noexcept {
    return pending_live_ ? reinterpret_cast<checker_pending_deed*>(pending_storage_) : nullptr;
  }

  organ::phase_crystal_foundation foundation_{};
  body::continuing_body body_;
  organ::acquired_theorem_fiber first_{};
  organ::acquired_theorem_fiber second_{};
  organ::acquired_geometry_theory geometry_{};
  organ::acquired_phase_crystal phase_crystal_{};
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(checker_pending_deed)]{};
  std::uint64_t mathematical_morphology_{};
  std::uint64_t codec_morphology_{};
  std::uint64_t geometry_morphology_{};
  std::uint64_t phase_morphology_{};
  bool source_detached_{};
  bool pending_live_{};
  bool admitted_{};
};

static_assert(std::is_trivially_destructible_v<resident_phase_crystal>);

}  // namespace holonics::event

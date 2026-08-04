#pragma once

#include <new>
#include <type_traits>

#include <holonics/codec/blind_code_renderer.hpp>
#include <holonics/codec/blind_explanation_renderer.hpp>
#include <holonics/codec/blind_moment_renderer.hpp>
#include <holonics/event/blind_checker_normalization_law.hpp>
#include <holonics/event/checker_pending_deed.hpp>
#include <holonics/organ/blind_reconstruction_law.hpp>

namespace holonics::event {

class resident_blind_reconstruction final {
 public:
  resident_blind_reconstruction() = delete;
  resident_blind_reconstruction(const resident_blind_reconstruction&) = delete;
  resident_blind_reconstruction& operator=(const resident_blind_reconstruction&) = delete;
  resident_blind_reconstruction(resident_blind_reconstruction&&) = delete;
  resident_blind_reconstruction& operator=(resident_blind_reconstruction&&) = delete;

  HOLONICS_CALLABLE resident_blind_reconstruction(
      const organ::blind_reconstruction_foundation& foundation,
      const regular_singular_rest_record& record,
      regular_singular_remount_receipt& receipt) noexcept
      : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
        first_(record.first), second_(record.second), geometry_(record.geometry),
        phase_crystal_(record.phase_crystal), characteristic_(record.characteristic),
        regular_singular_(record.regular_singular),
        mathematical_morphology_(record.mathematical_morphology),
        codec_morphology_(record.codec_morphology),
        geometry_morphology_(record.geometry_morphology),
        phase_morphology_(record.phase_morphology),
        characteristic_morphology_(record.characteristic_morphology),
        regular_singular_morphology_(record.regular_singular_morphology), source_detached_(true) {
    const bool exact = record.integrity == regular_singular_rest_integrity(record);
    receipt.theory = regular_singular_.identity;
    receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
    receipt.theory_preserved = exact && regular_singular_.accepted;
    receipt.source_replayed = receipt.body.source_replay_count != 0;
    admitted_ = exact && receipt.theory_preserved &&
        organ::blind_reconstruction_detail::valid_foundation(foundation_);
  }

  HOLONICS_CALLABLE resident_blind_reconstruction(
      const blind_reconstruction_rest_record& record,
      blind_reconstruction_remount_receipt& receipt) noexcept
      : body_(body::continuing_body::remount(record.body, receipt.body)), first_(record.first),
        second_(record.second), geometry_(record.geometry), phase_crystal_(record.phase_crystal),
        characteristic_(record.characteristic), regular_singular_(record.regular_singular),
        code_reconstruction_(record.code_reconstruction),
        moment_reconstruction_(record.moment_reconstruction),
        mathematical_morphology_(record.mathematical_morphology),
        codec_morphology_(record.codec_morphology),
        geometry_morphology_(record.geometry_morphology),
        phase_morphology_(record.phase_morphology),
        characteristic_morphology_(record.characteristic_morphology),
        regular_singular_morphology_(record.regular_singular_morphology),
        blind_reconstruction_morphology_(record.blind_reconstruction_morphology),
        source_detached_(true) {
    const bool exact = record.integrity == blind_reconstruction_rest_integrity(record);
    receipt.code_theory = code_reconstruction_.identity;
    receipt.moment_theory = moment_reconstruction_.identity;
    receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
    receipt.theories_preserved = exact && code_reconstruction_.accepted &&
        moment_reconstruction_.accepted;
    receipt.source_replayed = receipt.body.source_replay_count != 0;
    admitted_ = exact && receipt.theories_preserved;
    stage_ = passage_stage::moment_returned;
  }

  [[nodiscard]] HOLONICS_CALLABLE bool admitted() const noexcept { return admitted_; }
  [[nodiscard]] HOLONICS_CALLABLE bool can_continue() const noexcept { return body_.can_open(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word head() const noexcept { return body_.head(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word continuation() const noexcept {
    return body_.continuation_serial();
  }

  [[nodiscard]] HOLONICS_CALLABLE bool form_code(
      const organ::blind_reconstruction_question& question,
      blind_reconstruction_observation& observation) noexcept {
    if (!admitted_ || pending_live_ || stage_ != passage_stage::none) { return false; }
    organ::blind_reconstruction_detail::close_blind_reconstruction(
        foundation_, question, observation.inquiry);
    const auto& plan = observation.inquiry.theory;
    const codec::blind_reconstruction_surface explanation_surface{plan.code_passage,
        foundation_.code.lineage, plan.code_incidence, plan.jacobi_transport,
        false, plan.alternatives_retained, plan.source_separated};
    codec::blind_code_surface surface{};
    surface.passage = plan.code_passage;
    surface.cell_count = observation.inquiry.pairs[0].cell_count;
    surface.eigenvalue = observation.inquiry.pairs[0].witness_eigenvalue;
    surface.incidence = plan.code_incidence;
    surface.characteristic = plan.jacobi_transport;
    surface.alternatives = plan.alternatives_retained;
    surface.source_separated = plan.source_separated;
    for (std::size_t row = 0; row < codec::blind_code_cell_capacity; ++row) {
      surface.mass[row] = observation.inquiry.pairs[0].population[row];
      surface.witness[row] = observation.inquiry.pairs[0].witness_vector[row];
      for (std::size_t column = 0; column < codec::blind_code_cell_capacity; ++column) {
        surface.quotient[row][column] = observation.inquiry.pairs[0].quotient[row][column];
      }
    }
    for (std::size_t row = 0; row < codec::blind_code_degree_capacity; ++row) {
      surface.weight[row] = observation.inquiry.code.distance_distribution[row];
      surface.dual[row] = observation.inquiry.code.dual_distribution[row];
      surface.multiplicity[row] =
          observation.inquiry.pairs[0].characteristic_multiplicity[row];
      for (std::size_t column = 0; column < codec::blind_code_degree_capacity; ++column) {
        surface.krawtchouk[row][column] = observation.inquiry.code.krawtchouk[row][column];
      }
    }
    if (!observation.inquiry.theory_formed ||
        !codec::render_blind_code(surface, observation.code.formal) ||
        !codec::render_blind_code_explanation(
            explanation_surface, observation.code.conversational)) {
      observation.inquiry.obstruction = organ::blind_obstruction::render_refused; return false;
    }
    auto continuation = body_.take_continuation();
    observation.code.formation_commit = body_.commit(body_.head(), 0, 13,
        plan.code_passage.value(), static_cast<body::linear_continuation&&>(continuation));
    if (observation.code.formation_commit.state != body::body_change_status::committed) {
      observation.inquiry.obstruction = organ::blind_obstruction::continuation_refused; return false;
    }
    const checker_outbound_occurrence outbound{body_.head(), exact::word{160'800},
        exact::word{160'801}, exact::word{160'802}, exact::word{160'803},
        exact::word{160'804}, plan.code_passage, observation.code.formal.identity};
    ::new (static_cast<void*>(pending_storage_)) checker_pending_deed{
        body_.take_continuation(), outbound};
    pending_live_ = true;
    pending_kind_ = passage_kind::code;
    observation.code.outbound = outbound;
    observation.code.checker_stage = checker_stage_status::exact;
    observation.code.pending_before_process = true;
    return true;
  }

  [[nodiscard]] HOLONICS_CALLABLE bool resume_code(
      const checker_raw_return& raw, blind_reconstruction_observation& observation) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool form_moment(
      blind_reconstruction_observation& observation) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool resume_moment(
      const checker_raw_return& raw, blind_reconstruction_observation& observation) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE blind_reconstruction_rest_receipt rest(
      blind_reconstruction_rest_record& record) noexcept;

 private:
  enum class passage_kind : std::uint8_t { none, code, moment };
  enum class passage_stage : std::uint8_t { none, code_returned, moment_returned };

  [[nodiscard]] HOLONICS_CALLABLE checker_pending_deed* live_pending() noexcept {
    return pending_live_ ? reinterpret_cast<checker_pending_deed*>(pending_storage_) : nullptr;
  }

  organ::blind_reconstruction_foundation foundation_{};
  body::continuing_body body_;
  organ::acquired_theorem_fiber first_{};
  organ::acquired_theorem_fiber second_{};
  organ::acquired_geometry_theory geometry_{};
  organ::acquired_phase_crystal phase_crystal_{};
  organ::acquired_characteristic characteristic_{};
  organ::acquired_regular_singular regular_singular_{};
  organ::acquired_blind_reconstruction code_reconstruction_{};
  organ::acquired_blind_reconstruction moment_reconstruction_{};
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(checker_pending_deed)]{};
  std::uint64_t mathematical_morphology_{};
  std::uint64_t codec_morphology_{};
  std::uint64_t geometry_morphology_{};
  std::uint64_t phase_morphology_{};
  std::uint64_t characteristic_morphology_{};
  std::uint64_t regular_singular_morphology_{};
  std::uint64_t blind_reconstruction_morphology_{};
  passage_kind pending_kind_{passage_kind::none};
  passage_stage stage_{passage_stage::none};
  bool source_detached_{};
  bool pending_live_{};
  bool admitted_{};
};

static_assert(std::is_trivially_destructible_v<resident_blind_reconstruction>);

}  // namespace holonics::event

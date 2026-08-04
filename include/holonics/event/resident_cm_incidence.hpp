#pragma once

#include <new>
#include <type_traits>

#include <holonics/codec/cm_explanation_renderer.hpp>
#include <holonics/codec/cm_incidence_renderer.hpp>
#include <holonics/event/checker_pending_deed.hpp>
#include <holonics/event/cm_checker_normalization_law.hpp>
#include <holonics/organ/cm_theory_law.hpp>

namespace holonics::event {

class resident_cm_incidence final {
 public:
  resident_cm_incidence() = delete;
  resident_cm_incidence(const resident_cm_incidence&) = delete;
  resident_cm_incidence& operator=(const resident_cm_incidence&) = delete;
  resident_cm_incidence(resident_cm_incidence&&) = delete;
  resident_cm_incidence& operator=(resident_cm_incidence&&) = delete;

  HOLONICS_CALLABLE resident_cm_incidence(const organ::cm_incidence_foundation& foundation,
      const blind_reconstruction_rest_record& record,
      blind_reconstruction_remount_receipt& receipt) noexcept
      : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
        first_(record.first), second_(record.second), geometry_(record.geometry),
        phase_crystal_(record.phase_crystal), characteristic_(record.characteristic),
        regular_singular_(record.regular_singular),
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
    admitted_ = exact && receipt.theories_preserved &&
        organ::cm_incidence_detail::valid_foundation(foundation_);
  }

  HOLONICS_CALLABLE resident_cm_incidence(const cm_incidence_rest_record& record,
      cm_incidence_remount_receipt& receipt) noexcept
      : body_(body::continuing_body::remount(record.body, receipt.body)), first_(record.first),
        second_(record.second), geometry_(record.geometry), phase_crystal_(record.phase_crystal),
        characteristic_(record.characteristic), regular_singular_(record.regular_singular),
        code_reconstruction_(record.code_reconstruction),
        moment_reconstruction_(record.moment_reconstruction), cm_incidence_(record.cm_incidence),
        mathematical_morphology_(record.mathematical_morphology),
        codec_morphology_(record.codec_morphology),
        geometry_morphology_(record.geometry_morphology),
        phase_morphology_(record.phase_morphology),
        characteristic_morphology_(record.characteristic_morphology),
        regular_singular_morphology_(record.regular_singular_morphology),
        blind_reconstruction_morphology_(record.blind_reconstruction_morphology),
        cm_incidence_morphology_(record.cm_incidence_morphology), source_detached_(true) {
    const bool exact = record.integrity == cm_incidence_rest_integrity(record);
    receipt.theory = cm_incidence_.identity;
    receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
    receipt.theory_preserved = exact && cm_incidence_.accepted;
    receipt.source_replayed = receipt.body.source_replay_count != 0;
    admitted_ = exact && receipt.theory_preserved;
    stage_ = passage_stage::returned;
  }

  [[nodiscard]] HOLONICS_CALLABLE bool admitted() const noexcept { return admitted_; }
  [[nodiscard]] HOLONICS_CALLABLE bool can_continue() const noexcept { return body_.can_open(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word head() const noexcept { return body_.head(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word continuation() const noexcept {
    return body_.continuation_serial();
  }

  [[nodiscard]] HOLONICS_CALLABLE bool form(const organ::cm_incidence_question& question,
      cm_incidence_observation& observation) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool resume(
      const checker_raw_return& raw, cm_incidence_observation& observation) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE cm_incidence_rest_receipt rest(
      cm_incidence_rest_record& record) noexcept;

 private:
  enum class passage_stage : std::uint8_t { none, returned };

  [[nodiscard]] HOLONICS_CALLABLE checker_pending_deed* live_pending() noexcept {
    return pending_live_ ? reinterpret_cast<checker_pending_deed*>(pending_storage_) : nullptr;
  }

  organ::cm_incidence_foundation foundation_{};
  body::continuing_body body_;
  organ::acquired_theorem_fiber first_{};
  organ::acquired_theorem_fiber second_{};
  organ::acquired_geometry_theory geometry_{};
  organ::acquired_phase_crystal phase_crystal_{};
  organ::acquired_characteristic characteristic_{};
  organ::acquired_regular_singular regular_singular_{};
  organ::acquired_blind_reconstruction code_reconstruction_{};
  organ::acquired_blind_reconstruction moment_reconstruction_{};
  organ::acquired_cm_incidence cm_incidence_{};
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(checker_pending_deed)]{};
  std::uint64_t mathematical_morphology_{};
  std::uint64_t codec_morphology_{};
  std::uint64_t geometry_morphology_{};
  std::uint64_t phase_morphology_{};
  std::uint64_t characteristic_morphology_{};
  std::uint64_t regular_singular_morphology_{};
  std::uint64_t blind_reconstruction_morphology_{};
  std::uint64_t cm_incidence_morphology_{};
  passage_stage stage_{passage_stage::none};
  bool source_detached_{};
  bool pending_live_{};
  bool admitted_{};
};

static_assert(std::is_trivially_destructible_v<resident_cm_incidence>);

}  // namespace holonics::event

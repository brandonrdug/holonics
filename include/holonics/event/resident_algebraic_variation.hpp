#pragma once

#include <new>
#include <type_traits>

#include <holonics/codec/algebraic_variation_explanation_renderer.hpp>
#include <holonics/codec/algebraic_variation_renderer.hpp>
#include <holonics/event/algebraic_variation_return.hpp>
#include <holonics/event/algebraic_variation_surface_law.hpp>
#include <holonics/event/checker_pending_deed.hpp>
#include <holonics/event/cm_checker_normalization_law.hpp>
#include <holonics/organ/algebraic_variation_law.hpp>

namespace holonics::event {

class resident_algebraic_variation final {
 public:
  resident_algebraic_variation() = delete;
  resident_algebraic_variation(const resident_algebraic_variation&) = delete;
  resident_algebraic_variation& operator=(const resident_algebraic_variation&) = delete;
  resident_algebraic_variation(resident_algebraic_variation&&) = delete;
  resident_algebraic_variation& operator=(resident_algebraic_variation&&) = delete;

  HOLONICS_CALLABLE resident_algebraic_variation(
      const organ::algebraic_variation_foundation& foundation,
      const toric_cycle_rest_record& record, toric_cycle_remount_receipt& receipt) noexcept;
  HOLONICS_CALLABLE resident_algebraic_variation(
      const algebraic_variation_rest_record& record,
      algebraic_variation_remount_receipt& receipt) noexcept;

  [[nodiscard]] HOLONICS_CALLABLE bool admitted() const noexcept { return admitted_; }
  [[nodiscard]] HOLONICS_CALLABLE bool can_continue() const noexcept { return body_.can_open(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word head() const noexcept { return body_.head(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word continuation() const noexcept {
    return body_.continuation_serial();
  }
  [[nodiscard]] HOLONICS_CALLABLE bool form(const organ::algebraic_variation_question& question,
      algebraic_variation_observation& observation) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool resume(const checker_raw_return& raw,
      algebraic_variation_observation& observation) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE algebraic_variation_rest_receipt rest(
      algebraic_variation_rest_record& record) noexcept;

 private:
  enum class passage_stage : std::uint8_t { none, returned };
  [[nodiscard]] HOLONICS_CALLABLE checker_pending_deed* live_pending() noexcept {
    return pending_live_ ? reinterpret_cast<checker_pending_deed*>(pending_storage_) : nullptr;
  }

  organ::algebraic_variation_foundation foundation_{};
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
  organ::acquired_toric_cycle toric_cycle_{};
  organ::acquired_algebraic_variation algebraic_variation_{};
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(checker_pending_deed)]{};
  std::uint64_t mathematical_admitted_tally_{};
  std::uint64_t codec_admitted_tally_{};
  std::uint64_t geometry_admitted_tally_{};
  std::uint64_t phase_admitted_tally_{};
  std::uint64_t characteristic_admitted_tally_{};
  std::uint64_t regular_singular_admitted_tally_{};
  std::uint64_t blind_reconstruction_admitted_tally_{};
  std::uint64_t cm_incidence_admitted_tally_{};
  std::uint64_t toric_cycle_admitted_tally_{};
  std::uint64_t algebraic_variation_admitted_tally_{};
  passage_stage stage_{passage_stage::none};
  bool source_detached_{};
  bool pending_live_{};
  bool admitted_{};
};

static_assert(std::is_trivially_destructible_v<resident_algebraic_variation>);

}  // namespace holonics::event

#pragma once

#include <new>
#include <type_traits>

#include <holonics/codec/expression_geometry_explanation_renderer.hpp>
#include <holonics/codec/expression_geometry_renderer.hpp>
#include <holonics/event/checker_pending_deed.hpp>
#include <holonics/event/cm_checker_normalization_law.hpp>
#include <holonics/event/expression_geometry_return.hpp>
#include <holonics/event/expression_geometry_surface_law.hpp>
#include <holonics/organ/expression_geometry_law.hpp>

namespace holonics::event {

class resident_expression_geometry final {
 public:
  resident_expression_geometry() = delete;
  resident_expression_geometry(const resident_expression_geometry&) = delete;
  resident_expression_geometry& operator=(const resident_expression_geometry&) = delete;
  resident_expression_geometry(resident_expression_geometry&&) = delete;
  resident_expression_geometry& operator=(resident_expression_geometry&&) = delete;
  HOLONICS_CALLABLE resident_expression_geometry(
      const organ::expression_geometry_foundation& foundation,
      const intrinsic_hypergeometry_rest_record& record,
      intrinsic_hypergeometry_remount_receipt& receipt) noexcept;
  HOLONICS_CALLABLE resident_expression_geometry(
      const expression_geometry_rest_record& record,
      expression_geometry_remount_receipt& receipt) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool admitted() const noexcept { return admitted_; }
  [[nodiscard]] HOLONICS_CALLABLE bool can_continue() const noexcept { return body_.can_open(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word head() const noexcept { return body_.head(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word continuation() const noexcept {
    return body_.continuation_serial();
  }
  [[nodiscard]] HOLONICS_CALLABLE bool form(expression_geometry_observation& out) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool resume(const checker_raw_return& raw,
      expression_geometry_observation& out) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE expression_geometry_rest_receipt rest(
      expression_geometry_rest_record& record) noexcept;

 private:
  enum class passage_stage : std::uint8_t { none, returned };
  [[nodiscard]] HOLONICS_CALLABLE checker_pending_deed* live_pending() noexcept {
    return pending_live_ ? reinterpret_cast<checker_pending_deed*>(pending_storage_) : nullptr;
  }
  organ::expression_geometry_foundation foundation_{}; body::continuing_body body_;
  organ::acquired_theorem_fiber first_{}; organ::acquired_theorem_fiber second_{};
  organ::acquired_geometry_theory geometry_{}; organ::acquired_phase_crystal phase_crystal_{};
  organ::acquired_characteristic characteristic_{};
  organ::acquired_regular_singular regular_singular_{};
  organ::acquired_blind_reconstruction code_reconstruction_{};
  organ::acquired_blind_reconstruction moment_reconstruction_{};
  organ::acquired_cm_incidence cm_incidence_{}; organ::acquired_toric_cycle toric_cycle_{};
  organ::acquired_algebraic_variation algebraic_variation_{};
  organ::acquired_causal_linear causal_linear_{};
  organ::acquired_intrinsic_hypergeometry intrinsic_hypergeometry_{};
  organ::acquired_expression_geometry expression_geometry_{};
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(checker_pending_deed)]{};
  std::uint64_t mathematical_morphology_{}; std::uint64_t codec_morphology_{};
  std::uint64_t geometry_morphology_{}; std::uint64_t phase_morphology_{};
  std::uint64_t characteristic_morphology_{}; std::uint64_t regular_singular_morphology_{};
  std::uint64_t blind_reconstruction_morphology_{}; std::uint64_t cm_incidence_morphology_{};
  std::uint64_t toric_cycle_morphology_{}; std::uint64_t algebraic_variation_morphology_{};
  std::uint64_t causal_linear_morphology_{}; std::uint64_t intrinsic_hypergeometry_morphology_{};
  std::uint64_t expression_geometry_morphology_{};
  passage_stage stage_{passage_stage::none}; bool source_detached_{};
  bool pending_live_{}; bool admitted_{};
};

static_assert(std::is_trivially_destructible_v<resident_expression_geometry>);

}  // namespace holonics::event

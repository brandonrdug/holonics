#pragma once

#include <new>
#include <type_traits>

#include <holonics/codec/elementary_calculus_renderer.hpp>
#include <holonics/codec/heldout_holonomy_renderer.hpp>
#include <holonics/event/checker_pending_deed.hpp>
#include <holonics/event/cm_checker_normalization_law.hpp>
#include <holonics/event/elementary_calculus_return.hpp>
#include <holonics/event/elementary_calculus_surface_law.hpp>

namespace holonics::event {

class resident_elementary_calculus final {
 public:
  resident_elementary_calculus() = delete;
  resident_elementary_calculus(const resident_elementary_calculus &) = delete;
  resident_elementary_calculus &operator=(const resident_elementary_calculus &) = delete;
  resident_elementary_calculus(resident_elementary_calculus &&) = delete;
  resident_elementary_calculus &operator=(resident_elementary_calculus &&) = delete;
  HOLONICS_CALLABLE resident_elementary_calculus(
      const organ::elementary_development_bundle &, const cultivated_organ_rest_record &,
      cultivated_organ_remount_receipt &) noexcept;
  HOLONICS_CALLABLE resident_elementary_calculus(
      const elementary_calculus_rest_record &, elementary_calculus_remount_receipt &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool admitted() const noexcept { return admitted_; }
  [[nodiscard]] HOLONICS_CALLABLE bool can_continue() const noexcept { return body_.can_open(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word head() const noexcept { return body_.head(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word continuation() const noexcept {
    return body_.continuation_serial();
  }
  [[nodiscard]] HOLONICS_CALLABLE bool form_calculus(elementary_calculus_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool resume_calculus(
      const checker_raw_return &, elementary_calculus_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool form_heldout(heldout_holonomy_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool resume_heldout(
      const checker_raw_return &, heldout_holonomy_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE elementary_calculus_rest_receipt rest(
      elementary_calculus_rest_record &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE const organ::cultivated_shift_organ &self_organ() const noexcept {
    return laws_.self_organ;
  }
  [[nodiscard]] HOLONICS_CALLABLE const elementary_law_bundle &laws() const noexcept { return laws_; }

 private:
  enum class stage : std::uint8_t { developmental, derived, applied };
  [[nodiscard]] HOLONICS_CALLABLE checker_pending_deed *pending() noexcept {
    return pending_live_ ? reinterpret_cast<checker_pending_deed *>(pending_storage_) : nullptr;
  }
  cultivated_organ_rest_record standing_{};
  organ::elementary_development_bundle cards_{};
  body::continuing_body body_;
  elementary_law_bundle laws_{};
  elementary_application_fiber application_{};
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(checker_pending_deed)]{};
  std::uint64_t calculus_morphology_{};
  std::uint64_t self_organ_morphology_{};
  std::uint64_t derivation_morphology_{};
  stage stage_{stage::developmental};
  bool pending_live_{};
  bool admitted_{};
};

static_assert(std::is_trivially_destructible_v<resident_elementary_calculus>);

}  // namespace holonics::event

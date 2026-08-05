#pragma once

#include <new>
#include <type_traits>

#include <holonics/codec/cultivated_application_renderer.hpp>
#include <holonics/codec/cultivation_renderer.hpp>
#include <holonics/event/checker_pending_deed.hpp>
#include <holonics/event/cm_checker_normalization_law.hpp>
#include <holonics/event/cultivated_organ_surface_law.hpp>
#include <holonics/event/cultivated_organ_return.hpp>

namespace holonics::event {

class resident_cultivated_organs final {
 public:
  resident_cultivated_organs() = delete;
  resident_cultivated_organs(const resident_cultivated_organs &) = delete;
  resident_cultivated_organs &operator=(const resident_cultivated_organs &) = delete;
  resident_cultivated_organs(resident_cultivated_organs &&) = delete;
  resident_cultivated_organs &operator=(resident_cultivated_organs &&) = delete;
  HOLONICS_CALLABLE resident_cultivated_organs(
      const organ::developmental_stream_card (&cards)[organ::cultivation_family_count],
      const rederivation_rest_record &record, rederivation_remount_receipt &receipt) noexcept;
  HOLONICS_CALLABLE resident_cultivated_organs(
      const cultivated_organ_rest_record &record,
      cultivated_organ_remount_receipt &receipt) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool admitted() const noexcept { return admitted_; }
  [[nodiscard]] HOLONICS_CALLABLE bool can_continue() const noexcept { return body_.can_open(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word head() const noexcept { return body_.head(); }
  [[nodiscard]] HOLONICS_CALLABLE exact::word continuation() const noexcept {
    return body_.continuation_serial();
  }
  [[nodiscard]] HOLONICS_CALLABLE bool form_cultivation(cultivation_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool resume_cultivation(
      const checker_raw_return &, cultivation_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool form_application(
      cultivated_application_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool resume_application(
      const checker_raw_return &, cultivated_application_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE cultivated_organ_rest_receipt rest(
      cultivated_organ_rest_record &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE const organ::cultivated_shift_organ &organ(
      std::uint8_t index) const noexcept { return organs_[index]; }

 private:
  enum class stage : std::uint8_t { developmental, cultivated, applied };
  [[nodiscard]] HOLONICS_CALLABLE checker_pending_deed *pending() noexcept {
    return pending_live_ ? reinterpret_cast<checker_pending_deed *>(pending_storage_) : nullptr;
  }
  rederivation_rest_record standing_{};
  organ::developmental_stream_card cards_[organ::cultivation_family_count]{};
  body::continuing_body body_;
  organ::cultivated_shift_organ organs_[organ::cultivation_family_count]{};
  organ::acquired_organ_application application_{};
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(checker_pending_deed)]{};
  std::uint64_t cultivation_morphology_{};
  std::uint64_t organ_morphology_{};
  std::uint64_t application_morphology_{};
  stage stage_{stage::developmental};
  bool pending_live_{};
  bool admitted_{};
};

static_assert(std::is_trivially_destructible_v<resident_cultivated_organs>);

}  // namespace holonics::event

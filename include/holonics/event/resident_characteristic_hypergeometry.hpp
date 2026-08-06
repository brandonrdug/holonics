#pragma once

#include <new>
#include <type_traits>

#include <holonics/codec/characteristic_dossier_renderer.hpp>
#include <holonics/codec/characteristic_hypergeometry_renderer.hpp>
#include <holonics/codec/heldout_characteristic_renderer.hpp>
#include <holonics/event/characteristic_hypergeometry_return.hpp>
#include <holonics/event/characteristic_hypergeometry_surface_law.hpp>
#include <holonics/event/checker_pending_deed.hpp>
#include <holonics/event/cm_checker_normalization_law.hpp>

namespace holonics::event {

class resident_characteristic_hypergeometry final {
public:
  resident_characteristic_hypergeometry() = delete;
  resident_characteristic_hypergeometry(
      const resident_characteristic_hypergeometry &) = delete;
  resident_characteristic_hypergeometry &
  operator=(const resident_characteristic_hypergeometry &) = delete;
  resident_characteristic_hypergeometry(
      resident_characteristic_hypergeometry &&) = delete;
  resident_characteristic_hypergeometry &
  operator=(resident_characteristic_hypergeometry &&) = delete;
  HOLONICS_CALLABLE resident_characteristic_hypergeometry(
      const organ::characteristic_development_bundle &,
      const elementary_calculus_rest_record &,
      elementary_calculus_remount_receipt &) noexcept;
  HOLONICS_CALLABLE resident_characteristic_hypergeometry(
      const characteristic_hypergeometry_rest_record &,
      hypergeometry_remount_receipt &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool admitted() const noexcept {
    return admitted_;
  }
  [[nodiscard]] HOLONICS_CALLABLE bool can_continue() const noexcept {
    return body_.can_open();
  }
  [[nodiscard]] HOLONICS_CALLABLE exact::word head() const noexcept {
    return body_.head();
  }
  [[nodiscard]] HOLONICS_CALLABLE exact::word continuation() const noexcept {
    return body_.continuation_serial();
  }
  [[nodiscard]] HOLONICS_CALLABLE bool
  form_discovery(characteristic_discovery_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool
  resume_discovery(const checker_raw_return &,
                   characteristic_discovery_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool
  form_heldout(heldout_characteristic_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool
  resume_heldout(const checker_raw_return &,
                 heldout_characteristic_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE hypergeometry_rest_receipt
  rest(characteristic_hypergeometry_rest_record &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE const organ::trace_law_organ &
  organ() const noexcept {
    return law_.organ;
  }
  [[nodiscard]] HOLONICS_CALLABLE const characteristic_law_bundle &
  law() const noexcept {
    return law_;
  }

private:
  enum class stage : std::uint8_t { developmental, derived, applied };
  [[nodiscard]] HOLONICS_CALLABLE checker_pending_deed *pending() noexcept {
    return pending_live_
               ? reinterpret_cast<checker_pending_deed *>(pending_storage_)
               : nullptr;
  }
  elementary_calculus_rest_record standing_{};
  organ::characteristic_development_bundle cards_{};
  body::continuing_body body_;
  characteristic_law_bundle law_{};
  characteristic_application_fiber application_{};
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(
      checker_pending_deed)]{};
  std::uint64_t characteristic_admitted_tally_{};
  std::uint64_t trace_organ_admitted_tally_{};
  std::uint64_t transport_admitted_tally_{};
  stage stage_{stage::developmental};
  bool pending_live_{};
  bool admitted_{};
};
static_assert(
    std::is_trivially_destructible_v<resident_characteristic_hypergeometry>);

} // namespace holonics::event

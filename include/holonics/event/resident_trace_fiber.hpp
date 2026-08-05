#pragma once

#include <new>
#include <type_traits>

#include <holonics/codec/heldout_trace_fiber_renderer.hpp>
#include <holonics/codec/trace_fiber_dossier_renderer.hpp>
#include <holonics/codec/trace_fiber_renderer.hpp>
#include <holonics/event/checker_pending_deed.hpp>
#include <holonics/event/cm_checker_normalization_law.hpp>
#include <holonics/event/trace_fiber_return.hpp>

namespace holonics::event {

class resident_trace_fiber final {
public:
  resident_trace_fiber() = delete;
  resident_trace_fiber(const resident_trace_fiber &) = delete;
  resident_trace_fiber &operator=(const resident_trace_fiber &) = delete;
  resident_trace_fiber(resident_trace_fiber &&) = delete;
  resident_trace_fiber &operator=(resident_trace_fiber &&) = delete;
  HOLONICS_CALLABLE resident_trace_fiber(
      const organ::three_face_development_bundle &,
      const characteristic_hypergeometry_rest_record &,
      hypergeometry_remount_receipt &) noexcept;
  HOLONICS_CALLABLE resident_trace_fiber(const trace_fiber_rest_record &,
                                         trace_fiber_remount_receipt &) noexcept;
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
  form_discovery(trace_fiber_discovery_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool
  resume_discovery(const checker_raw_return &,
                   trace_fiber_discovery_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool
  form_heldout(heldout_trace_fiber_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool
  resume_heldout(const checker_raw_return &,
                 heldout_trace_fiber_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE trace_fiber_rest_receipt
  rest(trace_fiber_rest_record &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE const organ::trace_fiber_organ &
  organ(std::uint8_t target) const noexcept {
    return law_.organs[target];
  }
  [[nodiscard]] HOLONICS_CALLABLE const trace_fiber_law_bundle &law() const noexcept {
    return law_;
  }

private:
  enum class stage : std::uint8_t { developmental, derived, applied };
  [[nodiscard]] HOLONICS_CALLABLE checker_pending_deed *pending() noexcept {
    return pending_live_
               ? reinterpret_cast<checker_pending_deed *>(pending_storage_)
               : nullptr;
  }
  characteristic_hypergeometry_rest_record standing_{};
  organ::three_face_development_bundle cards_{};
  body::continuing_body body_;
  trace_fiber_law_bundle law_{};
  trace_fiber_application application_{};
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(
      checker_pending_deed)]{};
  std::uint64_t trace_fiber_morphology_{};
  std::uint64_t lift_organ_morphology_{};
  std::uint64_t triple_transport_morphology_{};
  stage stage_{stage::developmental};
  bool pending_live_{};
  bool admitted_{};
};
static_assert(std::is_trivially_destructible_v<resident_trace_fiber>);

} // namespace holonics::event

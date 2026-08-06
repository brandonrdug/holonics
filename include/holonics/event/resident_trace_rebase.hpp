#pragma once

#include <new>
#include <type_traits>

#include <holonics/codec/heldout_trace_rebase_renderer.hpp>
#include <holonics/codec/trace_rebase_dossier_renderer.hpp>
#include <holonics/codec/trace_rebase_renderer.hpp>
#include <holonics/event/checker_pending_deed.hpp>
#include <holonics/event/cm_checker_normalization_law.hpp>
#include <holonics/event/trace_rebase_return.hpp>

namespace holonics::event {

class resident_trace_rebase final {
public:
  resident_trace_rebase() = delete;
  resident_trace_rebase(const resident_trace_rebase &) = delete;
  resident_trace_rebase &operator=(const resident_trace_rebase &) = delete;
  resident_trace_rebase(resident_trace_rebase &&) = delete;
  resident_trace_rebase &operator=(resident_trace_rebase &&) = delete;
  HOLONICS_CALLABLE resident_trace_rebase(
      const organ::trace_rebase_development_bundle &,
      const trace_fiber_rest_record &, trace_fiber_remount_receipt &) noexcept;
  HOLONICS_CALLABLE resident_trace_rebase(
      const trace_rebase_rest_record &, trace_rebase_remount_receipt &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool admitted() const noexcept { return admitted_; }
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
  form_discovery_surface(trace_rebase_discovery_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool
  form_discovery(trace_rebase_discovery_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool
  resume_discovery(const checker_raw_return &,
                   trace_rebase_discovery_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool
  form_heldout(heldout_trace_rebase_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE bool
  resume_heldout(const checker_raw_return &,
                 heldout_trace_rebase_observation &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE trace_rebase_rest_receipt
  rest(trace_rebase_rest_record &) noexcept;
  [[nodiscard]] HOLONICS_CALLABLE const trace_rebase_law_bundle &law() const noexcept {
    return law_;
  }
  [[nodiscard]] HOLONICS_CALLABLE const trace_fiber_law_bundle &fiber() const noexcept {
    return standing_.law;
  }

private:
  enum class stage : std::uint8_t { developmental, derived, applied };
  [[nodiscard]] HOLONICS_CALLABLE checker_pending_deed *pending() noexcept {
    return pending_live_
               ? reinterpret_cast<checker_pending_deed *>(pending_storage_)
               : nullptr;
  }
  trace_fiber_rest_record standing_{};
  organ::trace_rebase_development_bundle cards_{};
  body::continuing_body body_;
  trace_rebase_law_bundle law_{};
  trace_rebase_application application_{};
  alignas(checker_pending_deed) unsigned char pending_storage_[sizeof(
      checker_pending_deed)]{};
  std::uint64_t rebase_admitted_tally_{};
  std::uint64_t differential_admitted_tally_{};
  std::uint64_t deck_admitted_tally_{};
  std::uint64_t path_admitted_tally_{};
  stage stage_{stage::developmental};
  bool pending_live_{};
  bool admitted_{};
};
static_assert(std::is_trivially_destructible_v<resident_trace_rebase>);

} // namespace holonics::event

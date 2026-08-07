#pragma once

#include <cuda_runtime_api.h>

#include <holonics/event/resident_trace_rebase_mount.hpp>
#include <holonics/event/resident_trace_rebase_rest.hpp>
#include <holonics/event/resident_trace_rebase_return.hpp>
#include <holonics/organ/heldout_trace_rebase_law.hpp>

namespace holonics::apparatus {

struct trace_rebase_discovery_mount final {
  organ::trace_rebase_development_bundle cards{};
  event::trace_fiber_rest_record inherited{};
};
struct trace_rebase_application_mount final {
  organ::heldout_trace_rebase_card heldout{};
  event::trace_rebase_rest_record inherited{};
};
using trace_rebase_source_secret = organ::heldout_trace_rebase_source;

[[nodiscard]] cudaError_t launch_trace_rebase_mount(
    const trace_rebase_discovery_mount *, unsigned char *,
    event::trace_rebase_discovery_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_rebase_states(
    const trace_rebase_discovery_mount *,
    event::trace_rebase_discovery_observation *, std::uint8_t,
    cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_trace_rebase_edges(
    event::trace_rebase_discovery_observation *, std::uint8_t,
    cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_trace_rebase_close(
    event::resident_trace_rebase *, event::trace_rebase_discovery_observation *,
    organ::trace_rebase_workspace *) noexcept;
[[nodiscard]] cudaError_t launch_trace_rebase_form_surface(
    event::resident_trace_rebase *,
    event::trace_rebase_discovery_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_rebase_form(
    event::resident_trace_rebase *,
    event::trace_rebase_discovery_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_rebase_resume(
    const event::checker_raw_return *, event::resident_trace_rebase *,
    event::trace_rebase_discovery_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_rebase_rest(
    event::resident_trace_rebase *, event::trace_rebase_rest_record *,
    event::trace_rebase_rest_record *,
    event::trace_rebase_discovery_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_rebase_observe(
    const event::trace_rebase_discovery_observation *,
    event::trace_rebase_discovery_observation *) noexcept;

[[nodiscard]] cudaError_t launch_trace_rebase_heldout_mount(
    const trace_rebase_application_mount *, unsigned char *,
    event::heldout_trace_rebase_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_rebase_heldout_source(
    const trace_rebase_application_mount *, trace_rebase_source_secret *,
    cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_trace_rebase_heldout_expose(
    const trace_rebase_source_secret *,
    event::heldout_trace_rebase_observation *, cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_trace_rebase_heldout_predict(
    event::resident_trace_rebase *, const trace_rebase_application_mount *,
    event::heldout_trace_rebase_observation *, cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_trace_rebase_heldout_compare(
    event::resident_trace_rebase *, const trace_rebase_source_secret *,
    event::heldout_trace_rebase_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_rebase_heldout_form(
    event::resident_trace_rebase *,
    event::heldout_trace_rebase_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_rebase_heldout_resume(
    const event::checker_raw_return *, event::resident_trace_rebase *,
    event::heldout_trace_rebase_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_rebase_heldout_rest(
    event::resident_trace_rebase *, event::trace_rebase_rest_record *,
    event::trace_rebase_rest_record *,
    event::heldout_trace_rebase_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_rebase_heldout_observe(
    const event::heldout_trace_rebase_observation *,
    event::heldout_trace_rebase_observation *) noexcept;

} // namespace holonics::apparatus

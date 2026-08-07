#pragma once

#include <cuda_runtime_api.h>

#include <holonics/codec/trace_fiber_dossier_renderer.hpp>
#include <holonics/event/resident_trace_fiber_mount.hpp>
#include <holonics/event/resident_trace_fiber_rest.hpp>
#include <holonics/event/resident_trace_fiber_return.hpp>
#include <holonics/organ/trace_fiber_close_law.hpp>

namespace holonics::apparatus {

struct trace_fiber_discovery_mount final {
  organ::three_face_development_bundle cards{};
  event::characteristic_hypergeometry_rest_record inherited{};
};
struct trace_fiber_application_mount final {
  organ::heldout_oriented_system_card heldout{};
  event::trace_fiber_rest_record inherited{};
};
using trace_source_secret = organ::trace_fiber_matrix_detail::heldout_trace_source_secret;

[[nodiscard]] cudaError_t launch_trace_fiber_mount(
    const trace_fiber_discovery_mount *, unsigned char *,
    event::trace_fiber_discovery_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_fiber_words(
    const trace_fiber_discovery_mount *, event::trace_fiber_discovery_observation *,
    std::uint8_t, cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_trace_fiber_triples(
    event::trace_fiber_discovery_observation *, std::uint8_t,
    cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_trace_fiber_close(
    const trace_fiber_discovery_mount *, event::trace_fiber_discovery_observation *,
    organ::trace_fiber_workspace *) noexcept;
[[nodiscard]] cudaError_t launch_trace_fiber_form(
    event::resident_trace_fiber *, event::trace_fiber_discovery_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_fiber_resume(
    const event::checker_raw_return *, event::resident_trace_fiber *,
    event::trace_fiber_discovery_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_fiber_rest(
    event::resident_trace_fiber *, event::trace_fiber_rest_record *,
    event::trace_fiber_rest_record *, event::trace_fiber_discovery_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_fiber_observe(
    const event::trace_fiber_discovery_observation *,
    event::trace_fiber_discovery_observation *) noexcept;

[[nodiscard]] cudaError_t launch_trace_fiber_heldout_mount(
    const trace_fiber_application_mount *, unsigned char *,
    event::heldout_trace_fiber_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_fiber_heldout_source(
    const trace_fiber_application_mount *, trace_source_secret *,
    cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_trace_fiber_heldout_expose(
    const trace_source_secret *, event::heldout_trace_fiber_observation *,
    cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_trace_fiber_heldout_predict(
    event::resident_trace_fiber *, event::heldout_trace_fiber_observation *,
    cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_trace_fiber_heldout_compare(
    event::resident_trace_fiber *, const trace_fiber_application_mount *,
    const trace_source_secret *, event::heldout_trace_fiber_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_fiber_heldout_form(
    event::resident_trace_fiber *, event::heldout_trace_fiber_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_fiber_heldout_resume(
    const event::checker_raw_return *, event::resident_trace_fiber *,
    event::heldout_trace_fiber_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_fiber_heldout_rest(
    event::resident_trace_fiber *, event::trace_fiber_rest_record *,
    event::trace_fiber_rest_record *, event::heldout_trace_fiber_observation *) noexcept;
[[nodiscard]] cudaError_t launch_trace_fiber_heldout_observe(
    const event::heldout_trace_fiber_observation *,
    event::heldout_trace_fiber_observation *) noexcept;

} // namespace holonics::apparatus

#pragma once

#include <cuda_runtime_api.h>

#include <holonics/codec/elementary_dossier_renderer.hpp>
#include <holonics/event/resident_elementary_calculus_mount.hpp>
#include <holonics/event/resident_elementary_calculus_rest.hpp>
#include <holonics/event/resident_elementary_calculus_return.hpp>
#include <holonics/organ/chart_conduct_law.hpp>
#include <holonics/organ/composition_receiver_law.hpp>
#include <holonics/organ/occurrence_incidence_law.hpp>
#include <holonics/organ/self_holonomy_organ_law.hpp>

namespace holonics::apparatus {

struct elementary_discovery_mount final {
  organ::elementary_development_bundle cards{};
  event::cultivated_organ_rest_record inherited{};
};
struct elementary_application_mount final {
  organ::heldout_triangle_card heldout{};
  event::elementary_calculus_rest_record inherited{};
};

[[nodiscard]] cudaError_t launch_elementary_mount(const elementary_discovery_mount *,
    unsigned char *, event::elementary_calculus_observation *) noexcept;
[[nodiscard]] cudaError_t launch_elementary_source(const elementary_discovery_mount *,
    event::elementary_calculus_observation *, std::uint8_t, cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_elementary_close(const elementary_discovery_mount *,
    event::elementary_calculus_observation *, organ::elementary_workspace *) noexcept;
[[nodiscard]] cudaError_t launch_elementary_form(event::resident_elementary_calculus *,
    event::elementary_calculus_observation *) noexcept;
[[nodiscard]] cudaError_t launch_elementary_resume(const event::checker_raw_return *,
    event::resident_elementary_calculus *, event::elementary_calculus_observation *) noexcept;
[[nodiscard]] cudaError_t launch_elementary_rest(event::resident_elementary_calculus *,
    event::elementary_calculus_rest_record *, event::elementary_calculus_rest_record *,
    event::elementary_calculus_observation *) noexcept;
[[nodiscard]] cudaError_t launch_elementary_observe(const event::elementary_calculus_observation *,
    event::elementary_calculus_observation *) noexcept;

[[nodiscard]] cudaError_t launch_heldout_mount(const elementary_application_mount *,
    unsigned char *, event::heldout_holonomy_observation *) noexcept;
[[nodiscard]] cudaError_t launch_heldout_source(const elementary_application_mount *,
    organ::heldout_workspace *, event::heldout_holonomy_observation *, cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_heldout_predict(event::resident_elementary_calculus *,
    event::heldout_holonomy_observation *, cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_heldout_compare(event::resident_elementary_calculus *,
    const organ::heldout_workspace *, event::heldout_holonomy_observation *) noexcept;
[[nodiscard]] cudaError_t launch_heldout_form(event::resident_elementary_calculus *,
    event::heldout_holonomy_observation *) noexcept;
[[nodiscard]] cudaError_t launch_heldout_resume(const event::checker_raw_return *,
    event::resident_elementary_calculus *, event::heldout_holonomy_observation *) noexcept;
[[nodiscard]] cudaError_t launch_heldout_rest(event::resident_elementary_calculus *,
    event::elementary_calculus_rest_record *, event::elementary_calculus_rest_record *,
    event::heldout_holonomy_observation *) noexcept;
[[nodiscard]] cudaError_t launch_heldout_observe(const event::heldout_holonomy_observation *,
    event::heldout_holonomy_observation *) noexcept;

}  // namespace holonics::apparatus

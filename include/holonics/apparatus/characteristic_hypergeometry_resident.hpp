#pragma once

#include <cuda_runtime_api.h>

#include <holonics/codec/characteristic_dossier_renderer.hpp>
#include <holonics/event/resident_characteristic_hypergeometry_mount.hpp>
#include <holonics/event/resident_characteristic_hypergeometry_rest.hpp>
#include <holonics/event/resident_characteristic_hypergeometry_return.hpp>
#include <holonics/organ/characteristic_census_law.hpp>
#include <holonics/organ/heldout_characteristic_law.hpp>

namespace holonics::apparatus {

struct characteristic_discovery_mount final {
  organ::characteristic_development_bundle cards{};
  event::elementary_calculus_rest_record inherited{};
};
struct characteristic_application_mount final {
  organ::heldout_local_system_card heldout{};
  event::characteristic_hypergeometry_rest_record inherited{};
};

[[nodiscard]] cudaError_t launch_characteristic_mount(
    const characteristic_discovery_mount *, unsigned char *,
    event::characteristic_discovery_observation *) noexcept;
[[nodiscard]] cudaError_t
launch_characteristic_words(const characteristic_discovery_mount *,
                            event::characteristic_discovery_observation *,
                            std::uint8_t, cudaStream_t) noexcept;
[[nodiscard]] cudaError_t
launch_characteristic_pairs(event::characteristic_discovery_observation *,
                            std::uint8_t, cudaStream_t) noexcept;
[[nodiscard]] cudaError_t
launch_characteristic_close(const characteristic_discovery_mount *,
                            event::characteristic_discovery_observation *,
                            organ::characteristic_workspace *) noexcept;
[[nodiscard]] cudaError_t launch_characteristic_form(
    event::resident_characteristic_hypergeometry *,
    event::characteristic_discovery_observation *) noexcept;
[[nodiscard]] cudaError_t launch_characteristic_resume(
    const event::checker_raw_return *,
    event::resident_characteristic_hypergeometry *,
    event::characteristic_discovery_observation *) noexcept;
[[nodiscard]] cudaError_t launch_characteristic_rest(
    event::resident_characteristic_hypergeometry *,
    event::characteristic_hypergeometry_rest_record *,
    event::characteristic_hypergeometry_rest_record *,
    event::characteristic_discovery_observation *) noexcept;
[[nodiscard]] cudaError_t launch_characteristic_observe(
    const event::characteristic_discovery_observation *,
    event::characteristic_discovery_observation *) noexcept;

[[nodiscard]] cudaError_t launch_characteristic_heldout_mount(
    const characteristic_application_mount *, unsigned char *,
    event::heldout_characteristic_observation *) noexcept;
[[nodiscard]] cudaError_t launch_characteristic_heldout_source(
    const characteristic_application_mount *,
    event::heldout_characteristic_observation *, cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_characteristic_heldout_predict(
    event::resident_characteristic_hypergeometry *,
    event::heldout_characteristic_observation *, cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_characteristic_heldout_compare(
    event::resident_characteristic_hypergeometry *,
    const characteristic_application_mount *,
    event::heldout_characteristic_observation *) noexcept;
[[nodiscard]] cudaError_t launch_characteristic_heldout_form(
    event::resident_characteristic_hypergeometry *,
    event::heldout_characteristic_observation *) noexcept;
[[nodiscard]] cudaError_t launch_characteristic_heldout_resume(
    const event::checker_raw_return *,
    event::resident_characteristic_hypergeometry *,
    event::heldout_characteristic_observation *) noexcept;
[[nodiscard]] cudaError_t launch_characteristic_heldout_rest(
    event::resident_characteristic_hypergeometry *,
    event::characteristic_hypergeometry_rest_record *,
    event::characteristic_hypergeometry_rest_record *,
    event::heldout_characteristic_observation *) noexcept;
[[nodiscard]] cudaError_t launch_characteristic_heldout_observe(
    const event::heldout_characteristic_observation *,
    event::heldout_characteristic_observation *) noexcept;

} // namespace holonics::apparatus

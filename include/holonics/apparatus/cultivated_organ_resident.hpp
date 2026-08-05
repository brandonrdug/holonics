#pragma once

#include <cuda_runtime_api.h>

#include <holonics/event/resident_cultivated_application_return.hpp>
#include <holonics/event/resident_cultivated_organs_mount.hpp>
#include <holonics/event/resident_cultivated_organs_rest.hpp>
#include <holonics/event/resident_cultivated_organs_return.hpp>
#include <holonics/organ/cultivated_organ_application_law.hpp>
#include <holonics/organ/cultivation_realization_law.hpp>

namespace holonics::apparatus {

struct cultivation_mount final {
  organ::developmental_stream_card cards[organ::cultivation_family_count]{};
  event::rederivation_rest_record inherited{};
};
struct cultivated_application_mount final {
  organ::heldout_structure_bundle structures{};
  event::cultivated_organ_rest_record inherited{};
};

[[nodiscard]] cudaError_t launch_cultivation_mount(const cultivation_mount *,
    unsigned char *, event::cultivation_observation *) noexcept;
[[nodiscard]] cudaError_t launch_cultivation_family(const cultivation_mount *,
    event::cultivation_observation *, organ::cultivation_workspace *,
    std::uint8_t, cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_cultivation_close(event::cultivation_observation *,
    organ::cultivation_workspace *) noexcept;
[[nodiscard]] cudaError_t launch_cultivation_form(event::resident_cultivated_organs *,
    event::cultivation_observation *) noexcept;
[[nodiscard]] cudaError_t launch_cultivation_resume(const event::checker_raw_return *,
    event::resident_cultivated_organs *, event::cultivation_observation *) noexcept;
[[nodiscard]] cudaError_t launch_cultivation_rest(event::resident_cultivated_organs *,
    event::cultivated_organ_rest_record *, event::cultivated_organ_rest_record *,
    event::cultivation_observation *) noexcept;
[[nodiscard]] cudaError_t launch_cultivation_observe(const event::cultivation_observation *,
    event::cultivation_observation *) noexcept;

[[nodiscard]] cudaError_t launch_application_mount(const cultivated_application_mount *,
    unsigned char *, event::cultivated_application_observation *) noexcept;
[[nodiscard]] cudaError_t launch_application_source(const cultivated_application_mount *,
    event::resident_cultivated_organs *, event::cultivated_application_observation *,
    std::uint8_t, cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_application_close(const cultivated_application_mount *,
    event::cultivated_application_observation *) noexcept;
[[nodiscard]] cudaError_t launch_application_form(event::resident_cultivated_organs *,
    event::cultivated_application_observation *) noexcept;
[[nodiscard]] cudaError_t launch_application_resume(const event::checker_raw_return *,
    event::resident_cultivated_organs *, event::cultivated_application_observation *) noexcept;
[[nodiscard]] cudaError_t launch_application_rest(event::resident_cultivated_organs *,
    event::cultivated_organ_rest_record *, event::cultivated_organ_rest_record *,
    event::cultivated_application_observation *) noexcept;
[[nodiscard]] cudaError_t launch_application_observe(
    const event::cultivated_application_observation *,
    event::cultivated_application_observation *) noexcept;

}  // namespace holonics::apparatus

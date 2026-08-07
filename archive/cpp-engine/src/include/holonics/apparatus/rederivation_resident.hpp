#pragma once

#include <cuda_runtime_api.h>

#include <holonics/event/resident_rederivation_mount.hpp>
#include <holonics/event/resident_rederivation_rest.hpp>
#include <holonics/event/resident_rederivation_return.hpp>
#include <holonics/organ/rederivation_cover_law.hpp>
#include <holonics/organ/rederivation_geometry_law.hpp>
#include <holonics/organ/rederivation_matching_law.hpp>
#include <holonics/organ/rederivation_potential_law.hpp>

namespace holonics::apparatus {

struct rederivation_mount final {
  organ::rederivation_foundation foundation{};
  organ::rederivation_question question{};
  event::arithmetic_spectral_rest_record inherited{};
};

[[nodiscard]] cudaError_t
launch_rederivation_mount(const rederivation_mount *, unsigned char *,
                          event::rederivation_observation *) noexcept;
[[nodiscard]] cudaError_t launch_rederivation_matching(
    event::resident_rederivation *, event::rederivation_observation *,
    organ::rederivation_workspace *, cudaStream_t) noexcept;
[[nodiscard]] cudaError_t
launch_rederivation_matching_close(event::resident_rederivation *,
                                   event::rederivation_observation *,
                                   organ::rederivation_workspace *) noexcept;
[[nodiscard]] cudaError_t launch_rederivation_geometry(
    event::resident_rederivation *, event::rederivation_observation *,
    organ::rederivation_workspace *, cudaStream_t) noexcept;
[[nodiscard]] cudaError_t launch_rederivation_cover(
    event::resident_rederivation *, event::rederivation_observation *,
    organ::rederivation_workspace *, cudaStream_t) noexcept;
[[nodiscard]] cudaError_t
launch_rederivation_compose(event::resident_rederivation *,
                            event::rederivation_observation *,
                            organ::rederivation_workspace *) noexcept;
[[nodiscard]] cudaError_t
launch_rederivation_form_foil(event::resident_rederivation *,
                              event::rederivation_observation *) noexcept;
[[nodiscard]] cudaError_t
launch_rederivation_resume_foil(const event::checker_raw_return *,
                                event::resident_rederivation *,
                                event::rederivation_observation *) noexcept;
[[nodiscard]] cudaError_t
launch_rederivation_form_valid(event::resident_rederivation *,
                               event::rederivation_observation *,
                               const organ::rederivation_workspace *) noexcept;
[[nodiscard]] cudaError_t
launch_rederivation_resume_valid(const event::checker_raw_return *,
                                 event::resident_rederivation *,
                                 event::rederivation_observation *) noexcept;
[[nodiscard]] cudaError_t
launch_rederivation_rest(event::resident_rederivation *,
                         event::rederivation_rest_record *,
                         event::rederivation_rest_record *,
                         event::rederivation_observation *) noexcept;
[[nodiscard]] cudaError_t
launch_rederivation_observe(const event::rederivation_observation *,
                            event::rederivation_observation *) noexcept;

} // namespace holonics::apparatus

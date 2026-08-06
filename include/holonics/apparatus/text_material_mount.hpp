#pragma once

#include <cstdint>

#include <holonics/apparatus/exact_executor.hpp>
#include <holonics/codec/text_rest.hpp>

namespace holonics::apparatus {

/// One section handed to the mount by the exterior codec. The apparatus owns
/// the containers and the splitting; the interior receives octets and ordinals.
struct text_section final {
  std::uint32_t container{};
  std::uint32_t section{};
  const unsigned char* octets{};
  std::uint32_t extent{};
};

struct text_mount_request final {
  const text_section* sections{};
  std::uint32_t section_count{};
  std::uint32_t containers{};
  std::uint32_t surface_capacity{};
  std::uint32_t occurrence_capacity{};
  std::uint32_t caused_capacity{};
  std::uint32_t state_capacity{};
  std::uint32_t transition_capacity{};
  std::uint32_t incidence_capacity{};
  std::uint32_t octet_aperture{};
  std::uint32_t query_paths{};
};

/// What one broad mount returned.
///
/// The three admission gates are literal and are named as the source owner names
/// them: `global_pair_population` must be zero, `hot_host_replay_work` must be
/// zero, and `bounded_delta_equal` must hold.
struct text_mount_receipt final {
  executor_status state{executor_status::invalid_aperture};

  std::uint32_t containers{};
  std::uint32_t occurrences{};
  std::uint32_t surface_octets{};
  std::uint64_t duplicate_witnesses{};
  std::uint64_t version_fibers{};
  std::uint64_t open_causal_fibers{};

  std::uint32_t states{};
  std::uint32_t transitions{};
  std::uint32_t caused_admitted{};
  std::uint64_t octets_crossed{};
  std::uint64_t formation_steps{};
  std::uint64_t lookup_steps{};
  std::uint64_t resident_octets{};
  std::uint64_t frame_octets{};

  std::uint64_t global_pair_population{};
  std::uint64_t hot_host_replay_work{};
  bool bounded_delta_equal{};

  std::uint32_t rest_octets{};
  std::uint32_t remount_octets{};
  bool remount_exact{};
  bool remount_founded_from_octets_alone{};

  bool mount_consumed_host{};
  bool consumed_host_refuses_admission{};
  bool refusal_returned_predecessor{};

  std::uint32_t device_queries{};
  std::uint32_t parity_failures{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == executor_status::returned;
  }
  /// The broad mount holds when every literal gate returns, the rest founds the
  /// same body from its octets alone, and ownership behaves as the source owner
  /// declares — consumption bars the predecessor, refusal returns it.
  ///
  /// The plurality laws must be **exercised**, not merely present: a corpus
  /// carrying no repeat and no revision would leave both at zero and prove
  /// nothing about them, so the declared control must return both.
  [[nodiscard]] constexpr bool holds() const noexcept {
    return returned() && global_pair_population == 0 && hot_host_replay_work == 0 &&
        bounded_delta_equal && remount_exact && remount_founded_from_octets_alone &&
        mount_consumed_host && consumed_host_refuses_admission &&
        refusal_returned_predecessor && parity_failures == 0 && device_queries != 0 &&
        occurrences != 0 && states != 0 && duplicate_witnesses != 0 &&
        version_fibers != 0;
  }
};

/// Mount one broad text standing: condition it, carry it to the resident card,
/// rest it to native octets, and found a fresh host from those octets alone.
[[nodiscard]] text_mount_receipt mount_text_material(
    text_mount_request request) noexcept;

}  // namespace holonics::apparatus

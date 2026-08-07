#pragma once

#include <cstdint>

#include <holonics/codec/reflection_receipt.hpp>
#include <holonics/event/reflective_codec_rest.hpp>

namespace holonics::apparatus {

struct reflective_codec_deed final {
  codec::codec_revision_request revision{};
  codec::surface_packet probe{};
  exact::word render_core{};
  exact::word reflection_occurrence{};
  exact::word reflection_lineage{};
};

struct reflective_codec_mount final {
  codec::codec_environment environment{};
  body::rest_region regions[body::live_region_capacity]{};
  reflective_codec_deed deed{};
  exact::word original_material{};
  exact::word relocated_material{};
  exact::word original_path{};
  exact::word relocated_path{};
  std::uint64_t body_seed{};
  bool source_detached{};
};

struct reflective_codec_observation final {
  codec::codec_obstruction obstruction{codec::codec_obstruction::none};
  codec::codec_behavior before{};
  codec::codec_reflection reflection{};
  codec::codec_revision_return revision{};
  event::reflective_codec_rest_receipt rest{};
  event::reflective_codec_remount_receipt remount{};
  codec::codec_behavior after{};
  exact::word final_head{};
  body::rest_region final_region{};
  bool storage_semantics_invariant{};
  bool source_detached{};
  bool reflection_exact{};
  bool revision_changed_conduct{};
  bool same_body_remounted{};
  bool syntax_not_core_identity{};
  bool local_law_without_registry{};
};

}  // namespace holonics::apparatus

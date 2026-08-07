#pragma once

#include <holonics/codec/reflection_schema.hpp>

namespace holonics::codec {

struct codec_crossing final {
  crossing_kind kind{crossing_kind::parse};
  codec_obstruction obstruction{codec_obstruction::none};
  exact::word occurrence{};
  exact::word lineage{};
  exact::word predecessor{};
  exact::word program{};
  exact::word version{};
  exact::word source_face{};
  exact::word target_face{};
  surface_packet input{};
  surface_packet output{};
  exact::word core_occurrence{};
  exact::word core_value{};
};

struct codec_behavior final {
  codec_crossing parsed{};
  codec_crossing rendered{};
  codec_crossing transduced{};
  codec_crossing unrelated_parsed{};
};

struct codec_reflection final {
  codec_obstruction obstruction{codec_obstruction::none};
  exact::word occurrence{};
  exact::word lineage{};
  codec_program operative{};
  exact::word environment{};
  exact::word inherited_provenance{};
  codec_continuation continuation{};
  bool environment_cloned{};
  bool continuation_cloned{};
};

struct codec_revision_return final {
  codec_obstruction obstruction{codec_obstruction::none};
  exact::word occurrence{};
  exact::word return_port{};
  exact::word lineage{};
  exact::word predecessor{};
  exact::word reflected_program{};
  exact::word old_version{};
  exact::word new_version{};
  exact::word old_bias{};
  exact::word new_bias{};
  codec_continuation reflected_continuation{};
  exact::word successor{};
  bool same_continuation{};
  bool law_changed{};
  bool committed{};
};

}  // namespace holonics::codec

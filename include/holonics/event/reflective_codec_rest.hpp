#pragma once

#include <holonics/body/rest_record.hpp>
#include <holonics/codec/reflection_receipt.hpp>

namespace holonics::event {

struct reflective_codec_rest_record final {
  body::rest_record body{};
  codec::codec_environment environment{};
};

struct reflective_codec_rest_receipt final {
  codec::codec_obstruction obstruction{codec::codec_obstruction::none};
  body::rest_receipt body{};
  exact::word environment{};
  exact::word program{};
  exact::word version{};
  bool source_detached{};
};

struct reflective_codec_remount_receipt final {
  codec::codec_obstruction obstruction{codec::codec_obstruction::none};
  body::rest_receipt body{};
  exact::word environment{};
  exact::word program{};
  exact::word version{};
  bool same_body{};
  bool source_replayed{};
};

}  // namespace holonics::event

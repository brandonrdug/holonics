#pragma once

#include <cstdint>
#include <type_traits>

#include <holonics/exact/word.hpp>
#include <holonics/structure/port.hpp>

namespace holonics::codec {

enum class codec_form : std::uint8_t { additive_symbol = 1, split_pulse = 2 };
enum class crossing_kind : std::uint8_t { parse, render, transduce };

enum class codec_obstruction : std::uint8_t {
  none,
  invalid_environment,
  invalid_program,
  invalid_surface,
  arithmetic_refused,
  stale_reflection,
  foreign_revision,
  continuation_refused,
  rest_refused
};

struct surface_packet final {
  exact::word first{};
  exact::word second{};
};

struct codec_face final {
  exact::word identity{};
  codec_form form{codec_form::additive_symbol};
  exact::word exterior_port{};
  exact::word body_port{};
};

struct codec_program final {
  exact::word identity{};
  exact::word version{};
  codec_face face{};
  exact::word scale{};
  exact::word bias{};
  exact::word inherited_lineage{};
};

struct codec_environment final {
  exact::word identity{};
  exact::word inherited_provenance{};
  exact::word core_occurrence{};
  codec_program operative{};
  codec_program unrelated{};
  exact::word source_material_testimony{};
  exact::word storage_lineage{};
};

struct codec_continuation final {
  exact::word body_head{};
  exact::word pending_serial{};
  bool pending{};
  bool reified_view_only{};
};

struct codec_revision_request final {
  exact::word occurrence{};
  exact::word return_port{};
  exact::word lineage{};
  exact::word next_version{};
  exact::word next_bias{};
};

using surface_input_port =
    structure::port<surface_packet, structure::port_direction::inbound>;
using surface_output_port =
    structure::port<surface_packet, structure::port_direction::outbound>;
using revision_return_port =
    structure::port<codec_revision_request, structure::port_direction::inbound>;

static_assert(!std::is_same_v<codec_face, codec_program>);
static_assert(!std::is_same_v<codec_program, codec_environment>);
static_assert(!std::is_same_v<codec_environment, codec_continuation>);

}  // namespace holonics::codec

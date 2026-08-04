#pragma once

#include <holonics/body/continuing_body.hpp>
#include <holonics/codec/conversational_math_renderer.hpp>
#include <holonics/codec/formal_math_renderer.hpp>
#include <holonics/organ/generative_math_receipt.hpp>

namespace holonics::event {

struct generative_math_return final {
  organ::generative_math_receipt generation{};
  codec::formal_math_face formal{};
  codec::conversational_math_face conversational{};
  exact::word final_head{};
  body::rest_region final_region{};
  bool source_detached{};
  bool same_closed_passage{};
  bool continuation_valid{};
};

}  // namespace holonics::event

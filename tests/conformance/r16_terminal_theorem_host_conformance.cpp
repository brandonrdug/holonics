#include <holonics/codec/theorem_production_renderer.hpp>
#include <holonics/event/dependent_theorem_production_law.hpp>
#include <holonics/event/returned_fiber_exclusion_law.hpp>

#include "r16_cases.hpp"

int main() {
  const auto rest = holonics::tests::r16_host_rest();
  const auto setup = holonics::tests::r16_host_setup();
  const auto mount = holonics::tests::r16_case(rest, setup);
  holonics::event::dependent_theorem_generation_receipt production{};
  std::size_t failures = !holonics::event::form_dependent_theorem(
      mount.foundation, rest.acquired, setup, production);
  failures += production.selected.identity != holonics::exact::word{182'200} ||
      production.passage.selected_rule != holonics::exact::word{181'200} ||
      !production.dependency_exact;
  holonics::codec::theorem_production_surface surface{production.passage.identity,
      production.passage.statement, production.passage.proof,
      holonics::codec::theorem_surface_form::returned_fiber_extension, true, true};
  holonics::codec::formal_math_face formal{};
  holonics::codec::conversational_math_face conversation{};
  failures += !holonics::codec::render_returned_fiber_theorem(surface, formal) ||
      !holonics::codec::render_returned_fiber_explanation(surface, conversation) ||
      formal.byte_count == 0 || conversation.byte_count == 0;
  holonics::event::theorem_production_rest_record projected{};
  const auto exclusion = holonics::event::exclude_returned_theorem_fiber(rest, projected);
  holonics::event::dependent_theorem_generation_receipt ablated{};
  failures += !exclusion.exact || holonics::event::form_dependent_theorem(
      mount.foundation, projected.acquired, setup, ablated) ||
      ablated.obstruction !=
          holonics::organ::theorem_production_obstruction::returned_fiber_absent;
  holonics::event::terminal_theorem_rest_record terminal{};
  terminal.body = rest.body;
  terminal.first = rest.acquired;
  terminal.second = {holonics::exact::word{182'200}, holonics::exact::word{172'200},
      holonics::exact::word{152'200}, holonics::exact::word{162'200},
      holonics::exact::word{160'300}, holonics::exact::word{181'200},
      holonics::exact::word{5}, 2, true};
  terminal.mathematical_morphology = 49;
  terminal.codec_morphology = 36;
  terminal.integrity = holonics::event::terminal_theorem_rest_integrity(terminal);
  failures += terminal.integrity != holonics::event::terminal_theorem_rest_integrity(terminal);
  return failures == 0 ? 0 : 1;
}

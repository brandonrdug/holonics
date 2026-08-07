#include "r28_cases.hpp"

namespace {

[[nodiscard]] std::int64_t pairing(const std::int64_t (&q)[6][6],
    const std::int64_t (&left)[6], const std::int64_t (&right)[6]) noexcept {
  std::int64_t value = 0;
  for (std::uint8_t row = 0; row < 6; ++row) {
    for (std::uint8_t column = 0; column < 6; ++column) {
      value += left[row] * q[row][column] * right[column];
    }
  }
  return value;
}

}  // namespace

int main() {
  using namespace holonics; const auto mount = tests::r28_case({}, tests::r28_host_card());
  organ::hodge_realization_receipt inquiry{}; inquiry.mounted = mount.foundation.card;
  inquiry.question = mount.question;
  for (std::uint8_t slot = 0; slot < 2; ++slot) {
    organ::hodge_factor_detail::derive(mount.foundation, slot, inquiry.factors[slot]);
  }
  organ::hodge_product_detail::derive(inquiry.factors, mount.foundation.card, inquiry.product);
  for (std::uint8_t slot = 0; slot < 4; ++slot) {
    organ::hodge_correspondence_detail::derive_translation(inquiry.factors[0], slot,
        inquiry.cycles.translations[slot]);
  }
  organ::hodge_cycle_detail::close(mount.foundation.card, inquiry.product, inquiry.cycles);
  organ::hodge_blowup_receipt changed{};
  organ::hodge_blowup_detail::derive(inquiry.product, inquiry.cycles,
      mount.foundation.card.center_selector, mount.foundation.card.lineage.value(), inquiry.blowup);
  organ::hodge_blowup_detail::derive(inquiry.product, inquiry.cycles,
      mount.foundation.card.changed_center_selector, mount.foundation.card.lineage.value(), changed);
  organ::hodge_realization_detail::close(inquiry, changed);
  const auto surface = event::hodge_realization_surface(inquiry, changed, true);
  codec::hodge_formal_face formal{}; codec::hodge_explanation explanation{};
  int failures = !inquiry.all_exact || !inquiry.theory_formed || !inquiry.no_expected_invariants ||
      !inquiry.alternatives_retained || !codec::render_hodge_realization(surface, formal) ||
      !codec::render_hodge_realization_explanation(surface, explanation);
  const std::int64_t expected_q[6][6]{{0,1,0,0,0,0},{1,0,0,0,0,0},
      {0,0,0,0,0,-1},{0,0,0,0,1,0},{0,0,0,1,0,0},{0,0,-1,0,0,0}};
  const std::int64_t graph[6]{1,1,0,1,-1,0};
  const std::int64_t negation[6]{1,1,0,-1,1,0};
  for (std::uint8_t row = 0; row < 6; ++row) {
    failures += inquiry.cycles.locus.graph_class[row] != graph[row] ||
        inquiry.cycles.locus.negation_class[row] != negation[row];
    for (std::uint8_t column = 0; column < 6; ++column) {
      failures += inquiry.product.cup[row][column] != expected_q[row][column];
    }
  }
  failures += pairing(expected_q, graph, graph) != 0 || pairing(expected_q, graph, negation) != 4 ||
      inquiry.product.rational_rank != 6 || inquiry.product.f2_rank != 1 ||
      inquiry.product.f1_rank != 5 || inquiry.product.h20 != 1 || inquiry.product.h11 != 4 ||
      inquiry.product.h02 != 1 || inquiry.cycles.locus.quotient_obstruction[0] != -1 ||
      inquiry.cycles.locus.quotient_obstruction[1] != 1 ||
      inquiry.cycles.fibers[0].enumerated != 2187 || inquiry.cycles.fibers[0].realizer_count != 16 ||
      inquiry.cycles.fibers[1].realizer_count != 16 || inquiry.cycles.fibers[0].effective_count != 4 ||
      inquiry.cycles.fibers[1].integral_member || !inquiry.cycles.fibers[2].outside_image ||
      inquiry.blowup.pairing[6][6] != -1 || inquiry.blowup.self_intersections[0] != -1 ||
      changed.self_intersections[1] != -1 || changed.self_intersections[0] != 0;
  return failures == 0 ? 0 : 1;
}

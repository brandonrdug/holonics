#include "r22_cases.hpp"
#include "r23_cases.hpp"
#include "r24_cases.hpp"
#include "r25_cases.hpp"

int main() {
  using namespace holonics;
  const auto mount = tests::r25_case({}, tests::r25_host_card(), tests::r22_host_card(),
      tests::r23_host_card(), tests::r24_host_card());
  const auto receipt = organ::causal_linear_detail::derive(
      mount.foundation, mount.question);
  const auto surface = event::causal_linear_surface(receipt);
  codec::causal_linear_formal_face formal{};
  codec::causal_linear_explanation explanation{};
  int failures = !receipt.all_exact || !receipt.theory_formed ||
      receipt.source_mask != 15 || receipt.phase.vertices != 6 ||
      receipt.phase.boundary_one_analysis.rank != 5 || receipt.phase.betti[1] != 2 ||
      receipt.cm.incidence_analysis.rank != 15 || receipt.cm.homology_one != 25 ||
      receipt.toric.source[0].free_cokernel_rank != 1 ||
      receipt.toric.blowup.free_cokernel_rank != 2 ||
      receipt.variation.determinant[1] != 1 || receipt.variation.determinant[2] != -1 ||
      !receipt.controls.equal_characteristic_unequal_fixed ||
      !receipt.controls.unequal_kernel_placement ||
      receipt.controls.rational_discriminant != -4 ||
      !receipt.controls.rational_eigenvalue_absent ||
      !receipt.controls.gaussian_eigenpair_exact ||
      !codec::render_causal_linear(surface, formal) ||
      !codec::render_causal_linear_explanation(surface, explanation);
  auto changed = mount.foundation; changed.card.phase_second = 4;
  const auto probe = organ::causal_linear_detail::derive(changed,
      {exact::word{192'320}, exact::word{192'321}, exact::word{192'322}});
  failures += !probe.all_exact || probe.phase.vertices != 8 ||
      probe.phase.boundary_one_analysis.rank != 7 || probe.phase.tours != 2 ||
      probe.phase.tour_length != 4 || !probe.cm.exact || !probe.toric.exact ||
      !probe.variation.exact;
  organ::causal_integer_matrix smith_source{};
  organ::causal_linear_detail::set_matrix(smith_source, 2, 2, 192'900, 192'901);
  smith_source.values[0][0] = 2; smith_source.values[1][1] = 4;
  organ::causal_matrix_analysis smith_analysis{};
  organ::causal_linear_detail::analyze(smith_source, smith_analysis, 192'902);
  std::int64_t smith[2]{};
  failures += !organ::causal_linear_detail::smith_rank_two(
      smith_source, smith_analysis, smith) || smith[0] != 2 || smith[1] != 4;
  organ::causal_integer_matrix overflow_source{};
  organ::causal_linear_detail::set_matrix(overflow_source, 2, 2, 192'903, 192'904);
  overflow_source.values[0][0] = organ::blind_integer_detail::exact_limit;
  overflow_source.values[0][1] = 1; overflow_source.values[1][0] = 1;
  overflow_source.values[1][1] = organ::blind_integer_detail::exact_limit;
  organ::causal_matrix_analysis overflow_analysis{};
  organ::causal_linear_detail::analyze(overflow_source, overflow_analysis, 192'905);
  failures += overflow_analysis.exact;
  return failures == 0 ? 0 : 1;
}

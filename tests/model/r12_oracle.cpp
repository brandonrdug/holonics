#include "r12_oracle.hpp"

namespace holonics::tests {
r12_expected r12_oracle() noexcept {
  return {130'100, 140'100, 150'100, 12'001'000, 12'001'001, 13'001'000, 5, 123,
      150'100,
      "import ElementaryHolonics.Algorithm.Rebase\n\n"
      "namespace Soma.Holonics\n\nopen SituatedAlgorithm\n\n"
      "theorem generated_semantics_rebase_reverse {Theta I S O S2 : Type*}\n"
      "    (A : SituatedAlgorithm Theta I S O) (e : S ≃ S2)\n"
      "    (theta : Theta) (input : I) (output : O) :\n"
      "    A.Semantics theta input output ↔\n"
      "      (A.rebase e).Semantics theta input output := by\n"
      "  exact (semantics_rebase_iff A e theta input output).symm\n\n"
      "end Soma.Holonics\n",
      "Generated statement: semantic behavior is invariant in the reverse direction under an "
      "invertible state rebase. The proof takes exact symmetry of the inherited "
      "semantics_rebase_iff passage. The theorem statement and proof object are new; "
      "no mounted theorem source was quoted as the answer.\n"};
}
}  // namespace holonics::tests

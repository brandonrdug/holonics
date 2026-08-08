import KernelWitness
namespace Soma
abbrev ExactRelay (Q : Prop) : Prop := exactCarrier Q
theorem carrier_transport_relayed (P : Prop) (h : P) : exactCarrier P := by
  rw [formal_carry]
  have generated := exact_chart_carry
  assumption
end Soma

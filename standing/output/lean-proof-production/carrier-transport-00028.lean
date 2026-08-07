import KernelWitness
namespace Soma
theorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by
  rw [formal_carry]
  have generated := exact_chart_carry P
  assumption
end Soma

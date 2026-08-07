import KernelWitness
namespace Soma
theorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by
  rw [exact_chart_carry]
  ring
end Soma

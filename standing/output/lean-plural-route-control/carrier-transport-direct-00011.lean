import KernelWitness
namespace Soma
theorem carrier_transport_direct (P : Prop) (h : P) : exactCarrier P := by
  apply exact_chart_carry
  apply exact_chart_carry
  assumption
end Soma

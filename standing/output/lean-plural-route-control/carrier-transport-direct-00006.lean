import KernelWitness
namespace Soma
theorem carrier_transport_direct (P : Prop) (h : P) : exactCarrier P := by
  have generated := exact_chart_carry P
  assumption
end Soma

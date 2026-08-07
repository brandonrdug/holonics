import KernelWitness
namespace Soma
theorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by
  have generated := exact_chart_carry P
  nlinarith
end Soma

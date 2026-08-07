import KernelWitness
namespace Soma
theorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by
  simpa using exact_chart_carry P
end Soma

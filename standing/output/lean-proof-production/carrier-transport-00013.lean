import KernelWitness
namespace Soma
theorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by
  contrapose! h
  exact exact_chart_carry P
end Soma

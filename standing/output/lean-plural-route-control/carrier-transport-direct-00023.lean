import KernelWitness
namespace Soma
theorem carrier_transport_direct (P : Prop) (h : P) : exactCarrier P := by
  contrapose! h
  exact exact_chart_carry P
end Soma

import KernelWitness
namespace Soma
theorem carrier_transport_direct (P : Prop) (h : P) : exactCarrier P := by
  contrapose! h
  exact formal_carry h
end Soma

import KernelWitness
namespace Soma
theorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by
  contrapose! h
  exact formal_carry h
end Soma

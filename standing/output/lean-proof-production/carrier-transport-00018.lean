import KernelWitness
namespace Soma
theorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by
  have generated := formal_carry h
  nlinarith
end Soma

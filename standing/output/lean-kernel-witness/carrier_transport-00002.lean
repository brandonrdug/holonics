namespace Soma
def exactCarrier (P : Prop) : Prop := P
variable (P : Prop)
theorem carrier_transport (h : P) : exactCarrier P := fun x => x
end Soma

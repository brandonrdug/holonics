namespace Soma
def exactCarrier (P : Prop) : Prop := P
variable (P : Prop)
theorem carrier_transport (h : P) : exactCarrier P := Nat.zero
end Soma

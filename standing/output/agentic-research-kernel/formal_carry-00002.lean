namespace Soma
def exactCarrier (P : Prop) : Prop := P
variable (P : Prop)
theorem formal_carry (h : P) : exactCarrier P := by
  simpa using exact_chart_carry P
end Soma

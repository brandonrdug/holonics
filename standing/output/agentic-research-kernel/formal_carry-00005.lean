namespace Soma
def exactCarrier (P : Prop) : Prop := P
variable (P : Prop)
theorem formal_carry (h : P) : exactCarrier P := by
  apply exact_chart_carry
  apply exact_chart_carry
  assumption
end Soma

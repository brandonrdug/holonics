namespace Soma
def exactCarrier (P : Prop) : Prop := P
variable (P : Prop)
theorem formal_carry (h : P) : exactCarrier P := by
  have generated := exact_chart_carry P
  assumption
end Soma

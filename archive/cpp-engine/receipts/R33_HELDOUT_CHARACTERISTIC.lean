import R33_CHARACTERISTIC_HYPERGEOMETRY

namespace Soma.Holonics.R33

def heldoutVisible : ℤ × ℤ × ℤ := (3,2,4)
def heldoutPredictedTrace : ℤ := 3
def heldoutSourceTrace : ℤ := 3
def heldoutCharacteristic : List ℤ := [1,(-3),1]

theorem heldoutCharacteristicTransport :
  tracePolynomial 3 2 4 heldoutPredictedTrace = 0 ∧ heldoutPredictedTrace = heldoutSourceTrace ∧
  heldoutCharacteristic = [1,-heldoutPredictedTrace,1] := by
  have returned := discoveredCharacteristicTransport 2 1 1 1 2 1 (-1) 0 (by norm_num) (by norm_num)
  norm_num [heldoutPredictedTrace, heldoutSourceTrace, heldoutCharacteristic, tracePolynomial] at returned ⊢

theorem generated_heldout_characteristic_transport :
  tracePolynomial 3 2 4 heldoutPredictedTrace = 0 := by exact heldoutCharacteristicTransport.1

end Soma.Holonics.R33

#check Soma.Holonics.R33.generated_heldout_characteristic_transport

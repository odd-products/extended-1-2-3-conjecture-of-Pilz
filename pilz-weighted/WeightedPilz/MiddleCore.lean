import WeightedPilz.CoreBudgets
import WeightedPilz.Initial

/-! The middle-interval core endpoint and square bounds discharge their
smaller-interval hypotheses using the checked initial range through eight. -/

namespace WeightedPilz
variable {K : Type*} [Field K]

theorem middle_core_endpoint_distance (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66) :
    Arithmetic.endpoint n ≤ distance (intervalCore n c) := by
  apply intervalCore_endpoint_distance n c hc (by omega)
  intro j hj w hw
  apply intervalBound_le_eight j _ w hw
  have hroot : Nat.sqrt n < 9 := Nat.sqrt_lt.mpr (by omega)
  omega

theorem middle_core_mul_endpoint (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (D : Poly K) (hD : D ≠ 0) :
    Arithmetic.endpoint n ≤ weight (intervalCore n c * D) :=
  (middle_core_endpoint_distance n c hc hn hn').trans
    (distance_le_weight_mul _ D hD)

theorem middle_core_square_weight (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66) (h2 : (2 : K) ≠ 0) :
    Arithmetic.endpoint n + Arithmetic.linearCoreCount n + 1 ≤
      weight (intervalCore n c ^ 2) := by
  apply intervalCore_square_weight n c hc (by omega) h2
  intro j hj w hw
  apply intervalBound_le_eight j _ w hw
  have hroot : Nat.sqrt n < 9 := Nat.sqrt_lt.mpr (by omega)
  omega

end WeightedPilz

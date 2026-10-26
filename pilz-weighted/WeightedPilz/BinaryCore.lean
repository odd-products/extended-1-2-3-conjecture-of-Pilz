import WeightedPilz.CoreDistanceTransfer
import WeightedPilz.BinarySmoothCore
import WeightedPilz.Initial
import WeightedPilz.Arithmetic.ParityBudgets

/-! The characteristic-two core bound κ in the finite middle interval. -/

namespace WeightedPilz
variable {K : Type*} [Field K] [CharP K 2]

theorem middle_binary_core_distance (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66) :
    Arithmetic.binaryKappa n ≤ distance (intervalCore n c) := by
  apply intervalCore_distance_of_smooth_distance n c hc (by omega)
  · intro j hj w hw
    apply intervalBound_le_eight j _ w hw
    have hroot : Nat.sqrt n < 9 := Nat.sqrt_lt.mpr (by omega)
    omega
  · exact middle_binary_smooth_distance n c hc hn hn'

theorem middle_binary_core_mul_lower (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (D : Poly K) (hD : D ≠ 0) :
    Arithmetic.binaryKappa n ≤ weight (intervalCore n c * D) :=
  (middle_binary_core_distance n c hc hn hn').trans
    (distance_le_weight_mul _ D hD)

/-- The numerical width constraints now use the proved weighted core bound. -/
theorem middle_binary_core_counterexample_width (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (D : Poly K) (hD : D ≠ 0)
    (hshort : weight (intervalCore n c * D) + Arithmetic.freshCount n * weight D < n) :
    weight D ≤ 5 ∧ (weight D ≤ 4 ∨ n = 58) := by
  have hcore := middle_binary_core_mul_lower n c hc hn hn' D hD
  have hbudget := Arithmetic.binary_width_budgets hn hn'
  have hr : 0 < Arithmetic.freshCount n := by
    by_contra h
    have hz : Arithmetic.freshCount n = 0 := by omega
    rw [hz, zero_mul] at hbudget
    omega
  have hquot : weight D ≤ (n - 1 - Arithmetic.binaryKappa n) / Arithmetic.freshCount n :=
    (Nat.le_div_iff_mul_le hr).mpr (by
      have hprod : Arithmetic.freshCount n * weight D ≤
          n - 1 - Arithmetic.binaryKappa n := by omega
      simpa only [Nat.mul_comm] using hprod)
  exact ⟨hquot.trans hbudget.2.2, hbudget.2.1.imp (hquot.trans) id⟩

end WeightedPilz

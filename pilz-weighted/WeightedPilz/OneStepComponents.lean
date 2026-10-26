import WeightedPilz.ComponentBounds
import Pilz.SieveEstimates

/-! The generic weighted component estimate for an arbitrary one-step sieve. -/
noncomputable section
namespace WeightedPilz
variable {K : Type*} [Field K]

/-- Equation `arith:eq:one-step-component-bound`. No positivity of the sieve
density, its resulting main coefficient, or its error constant is assumed. -/
theorem component_budget_one_step (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hq : 5 ≤ q) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D q) (hu : 4 ≤ weight D)
    (T U : Finset ℕ) (hT : ∀p ∈ T, Nat.Prime p) (hU : ∀p ∈ U, Nat.Prime p)
    (hdis : Disjoint T U) (hcover : T ∪ U = Pilz.primesUpTo q)
    (ρ δ : ℝ) (herr : Pilz.RoughDiscrepancy T ρ δ) :
    ((weight D : ℝ) + 4) / 2 * (ρ * (1 - ∑ p ∈ U, 1 / (p : ℝ))) * n -
      2 * ((weight D : ℝ) - 2) * ((1 + (U.card : ℝ)) * δ) ≤
        (weight (interval n c * D) : ℝ) := by
  have hbudget : 4 * (Pilz.roughCount (Pilz.primesUpTo q) n : ℝ) +
      ((weight D - 4 : ℕ) : ℝ) * Pilz.roughIntervalCount (Pilz.primesUpTo q) n ≤
        (weight (interval n c * D) : ℝ) := by
    exact_mod_cast component_budget_four_paper q n c D hc hq hD hnorm hlargest hu
  have hcast : ((weight D - 4 : ℕ) : ℝ) = (weight D : ℝ) - 4 := by
    rw [Nat.cast_sub hu]
    norm_num
  rw [hcast] at hbudget
  have hcount := Pilz.roughRealCount_one_step T U ρ δ (n : ℝ) hT hU hdis herr
    (Nat.cast_nonneg n)
  have hhalf := Pilz.roughRealIntervalCount_one_step T U ρ δ (n : ℝ) hT hU hdis herr
    (Nat.cast_nonneg n)
  rw [hcover, Pilz.roughRealCount_natCast] at hcount
  rw [hcover, Pilz.roughRealIntervalCount_natCast] at hhalf
  have huR : (4 : ℝ) ≤ weight D := by exact_mod_cast hu
  have hprod := mul_le_mul_of_nonneg_left hhalf (sub_nonneg.mpr huR)
  nlinarith

end WeightedPilz

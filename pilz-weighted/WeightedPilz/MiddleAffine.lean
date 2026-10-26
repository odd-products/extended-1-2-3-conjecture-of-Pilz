import WeightedPilz.AffineBudget
import WeightedPilz.UniqueProductCoefficients
import WeightedPilz.Arithmetic.MiddleUniqueBudgets
import WeightedPilz.MiddleCore

/-! The one-term square-cofactor branch of the middle-interval affine
argument, using actual unique integer products and the checked block budgets. -/

noncomputable section
namespace WeightedPilz

open MvPolynomial
variable {K : Type*} [Field K]

/-- For a one-term `B`, the actual unique-product coefficients and the seven
integer budget rows rule out a strict affine counterexample. The endpoint
hypothesis is explicit so this can be used within the strong induction. -/
theorem middle_affine_row_lower_of_weight_one (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (h2 : (2 : K) ≠ 0) (D B : Poly K) (hB : weight B = 1)
    (hendpoint : Arithmetic.endpoint n ≤ weight (intervalCore n c * D)) :
    n ≤ weight (intervalCore n c * D) +
      Arithmetic.freshCount n * weight (D + intervalCore n c * B) +
      Arithmetic.squareCost n * weight B := by
  by_contra hlarge
  have hsmall := lt_of_not_ge hlarge
  have hbasic := Arithmetic.middleBasicBudgets hn hn'
  have hr : 0 < Arithmetic.freshCount n := by
    by_contra hr
    have hz : Arithmetic.freshCount n = 0 := by omega
    rw [hz, zero_mul] at hbasic
    omega
  have hR : 0 < Arithmetic.squareCost n := by
    unfold Arithmetic.squareCost
    apply Nat.div_pos _ (by decide)
    nlinarith
  have hE := (affine_counterexample_budgets n (Arithmetic.endpoint n)
    (Arithmetic.freshCount n) (Arithmetic.squareCost n)
    (weight (intervalCore n c * D)) (weight (D + intervalCore n c * B))
    (weight B) hr hR hendpoint hsmall).2
  rw [hB] at hE
  have hsq := uniqueProducts_card_le_square_mul_weight_one n c hc h2 B hB
  have hbudget := Arithmetic.middle_unique_product_budget hn hn'
  have hcombined : n + (n - 2 * Arithmetic.freshCount n) *
      Arithmetic.affineLinearBudget n 1 ≤
      weight (intervalCore n c ^ 2 * B) + Arithmetic.squareCost n * weight B := by
    rw [hB, mul_one]
    omega
  exact (not_le_of_gt hsmall) (affine_row_budget (intervalCore n c) D B n
    (Arithmetic.freshCount n) (Arithmetic.squareCost n) (Arithmetic.affineLinearBudget n 1)
    (weight_intervalCore_add_freshCount n c hc)
    (Arithmetic.middle_natural_budgets hn hn').1 hE hcombined)

/-- The middle affine argument with nonzero leading row is complete away
from the four exceptional binomial cases. No field-bound hypothesis remains. -/
theorem middle_affine_rows_lower_of_not_exception (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (h2 : (2 : K) ≠ 0) (D B : Poly K) (hB : B ≠ 0)
    (hex : n ∉ ({26, 27, 28, 40} : Finset ℕ)) :
    n ≤ weight (intervalCore n c * D) +
      Arithmetic.freshCount n * weight (D + intervalCore n c * B) +
      Arithmetic.squareCost n * weight B := by
  have hbasic := Arithmetic.middleBasicBudgets hn hn'
  have hr : 0 < Arithmetic.freshCount n := by
    by_contra hr
    have hz : Arithmetic.freshCount n = 0 := by omega
    rw [hz, zero_mul] at hbasic
    omega
  have hR : 0 < Arithmetic.squareCost n := by
    unfold Arithmetic.squareCost
    apply Nat.div_pos _ (by decide)
    nlinarith
  by_cases hD : D = 0
  · subst D
    have hCB := middle_core_mul_endpoint n c hc hn hn' B hB
    have hmul := Nat.mul_le_mul_left (Arithmetic.freshCount n) hCB
    simp only [mul_zero, weight_zero, zero_add]
    omega
  by_contra hlarge
  have hsmall := lt_of_not_ge hlarge
  have hd := middle_core_mul_endpoint n c hc hn hn' D hD
  have ht := (affine_counterexample_budgets n (Arithmetic.endpoint n)
    (Arithmetic.freshCount n) (Arithmetic.squareCost n)
    (weight (intervalCore n c * D)) (weight (D + intervalCore n c * B))
    (weight B) hr hR hd hsmall).1
  have hquot : (n - 1 - Arithmetic.endpoint n) / Arithmetic.squareCost n < 2 := by
    by_contra hquot
    apply hex
    rw [← Arithmetic.affine_two_term_exceptions]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn, hn'⟩, by omega⟩
  have hBone : weight B = 1 := by have := weight_pos hB; omega
  exact hlarge (middle_affine_row_lower_of_weight_one n c hc hn hn' h2 D B hBone hd)

/-- The normalized interval multiple itself, for aggregate fresh degree one
and middle indices outside the four finite-binomial exceptions. -/
theorem middle_affine_lower_of_not_exception (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (hr : (intervalFreshPrimes n).Nonempty) (h2 : (2 : K) ≠ 0)
    (D B : Poly K)
    (hD : (intervalFreshData n c (by omega) hc hr).BaseOnly D)
    (hBbase : (intervalFreshData n c (by omega) hc hr).BaseOnly B) (hB : B ≠ 0)
    (hex : n ∉ ({26, 27, 28, 40} : Finset ℕ)) :
    n ≤ weight ((intervalFreshData n c (by omega) hc hr).F *
      (D + (intervalFreshData n c (by omega) hc hr).freshSum * B)) := by
  rw [FreshData.weight_mul_affine _ D B hD hBbase h2]
  change n ≤ weight (intervalCore n c * D) +
    (intervalFreshPrimes n).card * weight (D + intervalCore n c * B) +
    ((intervalFreshPrimes n).card * ((intervalFreshPrimes n).card + 1) / 2) * weight B
  rw [Pilz.card_freshPrimes]
  exact middle_affine_rows_lower_of_not_exception n c hc hn hn' h2 D B hB hex

end WeightedPilz

import WeightedPilz.MiddleAffine
import WeightedPilz.FiniteBinomialSquares
import WeightedPilz.MiddleBase

/-! All middle-interval affine cofactors of aggregate fresh degree one.
The four finite binomial-square exceptions are discharged here. -/

noncomputable section
namespace WeightedPilz

open MvPolynomial
variable {K : Type*} [Field K]

theorem middle_affine_rows_lower (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (h2 : (2 : K) ≠ 0) (D B : Poly K) (hB : B ≠ 0) :
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
  have hbounds := affine_counterexample_budgets n (Arithmetic.endpoint n)
    (Arithmetic.freshCount n) (Arithmetic.squareCost n)
    (weight (intervalCore n c * D)) (weight (D + intervalCore n c * B))
    (weight B) hr hR hd hsmall
  have ht : weight B ≤ 2 := hbounds.1.trans hbasic.2.2
  have htpos := weight_pos hB
  rcases (show weight B = 1 ∨ weight B = 2 by omega) with hBone | hBtwo
  · exact hlarge (middle_affine_row_lower_of_weight_one n c hc hn hn' h2 D B hBone hd)
  have hmem : n ∈ ({26, 27, 28, 40} : Finset ℕ) := by
    rw [← Arithmetic.affine_two_term_exceptions]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn, hn'⟩, by omega⟩
  have hcases : n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 40 := by simpa using hmem
  have hsquare := finite_binomial_square_bounds n hcases c hc h2 B hBtwo
  have hnum : n + (n - 2 * Arithmetic.freshCount n) * Arithmetic.affineLinearBudget n 2 ≤
      (if n = 26 then 16 else if n = 40 then 20 else 44) + 2 * Arithmetic.squareCost n := by
    rcases hcases with rfl | rfl | rfl | rfl
    · simpa using Arithmetic.affine_two_term_output_budgets.1
    · simpa using Arithmetic.affine_two_term_output_budgets.2.1
    · simpa using Arithmetic.affine_two_term_output_budgets.2.2.1
    · simpa using Arithmetic.affine_two_term_output_budgets.2.2.2
  have hcombined : n + (n - 2 * Arithmetic.freshCount n) * Arithmetic.affineLinearBudget n 2 ≤
      weight (intervalCore n c ^ 2 * B) + Arithmetic.squareCost n * weight B := by
    rw [hBtwo]
    omega
  have hE := hbounds.2
  rw [hBtwo] at hE
  exact hlarge (affine_row_budget (intervalCore n c) D B n
    (Arithmetic.freshCount n) (Arithmetic.squareCost n) (Arithmetic.affineLinearBudget n 2)
    (weight_intervalCore_add_freshCount n c hc)
    (Arithmetic.middle_natural_budgets hn hn').1 hE hcombined)

theorem middle_affine_lower (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (hr : (intervalFreshPrimes n).Nonempty) (h2 : (2 : K) ≠ 0)
    (D B : Poly K)
    (hD : (intervalFreshData n c (by omega) hc hr).BaseOnly D)
    (hBbase : (intervalFreshData n c (by omega) hc hr).BaseOnly B) (hB : B ≠ 0) :
    n ≤ weight ((intervalFreshData n c (by omega) hc hr).F *
      (D + (intervalFreshData n c (by omega) hc hr).freshSum * B)) := by
  rw [FreshData.weight_mul_affine _ D B hD hBbase h2]
  change n ≤ weight (intervalCore n c * D) +
    (intervalFreshPrimes n).card * weight (D + intervalCore n c * B) +
    ((intervalFreshPrimes n).card * ((intervalFreshPrimes n).card + 1) / 2) * weight B
  rw [Pilz.card_freshPrimes]
  exact middle_affine_rows_lower n c hc hn hn' h2 D B hB

/-- `lem:fin-affine`, including the base-only case `B = 0`. -/
theorem middle_affine_lower_all (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (hr : (intervalFreshPrimes n).Nonempty) (h2 : (2 : K) ≠ 0)
    (D B : Poly K)
    (hD : (intervalFreshData n c (by omega) hc hr).BaseOnly D)
    (hBbase : (intervalFreshData n c (by omega) hc hr).BaseOnly B)
    (hH : D + (intervalFreshData n c (by omega) hc hr).freshSum * B ≠ 0) :
    n ≤ weight ((intervalFreshData n c (by omega) hc hr).F *
      (D + (intervalFreshData n c (by omega) hc hr).freshSum * B)) := by
  by_cases hB : B = 0
  · subst B
    have hDne : D ≠ 0 := by simpa using hH
    rw [FreshData.weight_mul_affine _ D 0 hD hBbase h2]
    simp only [mul_zero, weight_zero, add_zero]
    change n ≤ weight (intervalCore n c * D) + (intervalFreshPrimes n).card * weight D
    rw [Pilz.card_freshPrimes]
    exact middle_base n c hc hn hn' D hDne hD
  · exact middle_affine_lower n c hc hn hn' hr h2 D B hD hBbase hB

end WeightedPilz

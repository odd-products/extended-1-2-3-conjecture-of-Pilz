import WeightedPilz.IntegerResidueRefinement
import WeightedPilz.Arithmetic.AggregateBudgets
import WeightedPilz.Arithmetic.UniqueProducts

/-! The full middle-interval residue capacities for primes at least five,
and the refined cube-residue capacities including the two exceptions. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators Pointwise
variable {K : Type*} [Field K]

theorem intervalCore_middle_residue_capacity (n p j : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hj : 0 < j) (hjp : j < p) :
    residueSigma p (intervalCore n c ^ j) ≤
      (Arithmetic.freshCount n + j - 1).choose j :=
  residueSigma_intervalCore_pow_le n p j _ c hc hp.pos
    (Arithmetic.middle_residue_budget hn hn' hp hp5 hj hjp)

private theorem mem_arithmetic_core_of_interval {n a : ℕ}
    (ha : a ∈ Finset.Icc 1 n \ intervalFreshPrimes n) : a ∈ Arithmetic.core n := by
  obtain ⟨ha, hnot⟩ := Finset.mem_sdiff.mp ha
  apply Finset.mem_filter.mpr
  refine ⟨ha, ?_⟩
  rintro ⟨hp, hhalf⟩
  exact hnot ((Pilz.mem_freshPrimes_iff n a).mpr ⟨hp, (Finset.mem_Icc.mp ha).2, hhalf⟩)

theorem intervalCore_square_support_subset_products (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) :
    (intervalCore n c ^ 2).support ⊆ (Arithmetic.products n).image Nat.factorization := by
  intro d hd
  rw [pow_two] at hd
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    Finset.mem_add.mp (MvPolynomial.support_mul _ _ hd)
  rw [intervalCore_support n c hc] at ha hb
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
  have hu0 : u ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hu).1).1; omega
  have hv0 : v ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hv).1).1; omega
  refine Finset.mem_image.mpr ⟨u * v, ?_, Nat.factorization_mul hu0 hv0⟩
  exact Finset.mem_image.mpr ⟨(u, v),
    Finset.mem_product.mpr ⟨mem_arithmetic_core_of_interval hu,
      mem_arithmetic_core_of_interval hv⟩, rfl⟩

theorem not_mem_core_square_support_of_not_product (n a : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (ha : 0 < a) (hnot : a ∉ Arithmetic.products n) :
    a.factorization ∉ (intervalCore n c ^ 2).support := by
  intro hmem
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp
    (intervalCore_square_support_subset_products n c hc hmem)
  have hb0 := (Arithmetic.products_mem_bounds hb).1
  have hbne : b ≠ 0 := by omega
  have hba' : b = a := Nat.factorization_inj hbne ha.ne' hba
  exact hnot (hba' ▸ hb)

private theorem cube_zero_small (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c)
    (hn : n ≤ 28) (m : ℕ) (hNm : n ^ 2 < (m + 1) ^ 3) :
    residueWeight 3 (intervalCore n c ^ 2) 0 ≤ ((Finset.Icc 1 m) \ {7, 8}).card := by
  apply residueWeight_zero_le_of_excluded_powers 3 (n ^ 2) m (by decide) _
    ((integerSupported_intervalCore n c hc).pow 2) hNm
  intro b hb
  have hb' : b = 7 ∨ b = 8 := by simpa using hb
  rcases hb' with rfl | rfl
  · exact not_mem_core_square_support_of_not_product n (7 ^ 3) c hc (by decide)
      (Arithmetic.small_cube_exclusions hn).1
  · exact not_mem_core_square_support_of_not_product n (8 ^ 3) c hc (by decide)
      (Arithmetic.small_cube_exclusions hn).2

theorem residueSigma_cube_square_26 (c : ℕ → K) (hc : NonzeroWeights 26 c) :
    residueSigma 3 (intervalCore 26 c ^ 2) ≤ 6 := by
  apply Finset.sup_le
  intro α hα
  by_cases hz : α = 0
  · subst α
    have h := cube_zero_small 26 c hc (by decide) 8 (by decide)
    convert h using 1 <;> decide
  · exact residueWeight_nonzero_le_of_integerSupported 3 (26 ^ 2) 6 (by decide) _
      ((integerSupported_intervalCore 26 c hc).pow 2) α hz (by decide)

theorem residueSigma_cube_square_27_28 (n : ℕ) (hn : n = 27 ∨ n = 28)
    (c : ℕ → K) (hc : NonzeroWeights n c) : residueSigma 3 (intervalCore n c ^ 2) ≤ 7 := by
  have hn28 : n ≤ 28 := by omega
  apply Finset.sup_le
  intro α hα
  by_cases hz : α = 0
  · subst α
    have h := cube_zero_small n c hc hn28 9 (by rcases hn with rfl | rfl <;> decide)
    convert h using 1 <;> decide
  · apply residueWeight_nonzero_le_of_integerSupported 3 (n ^ 2) 7 (by decide) _
      ((integerSupported_intervalCore n c hc).pow 2) α hz
    rcases hn with rfl | rfl <;> decide

theorem residueSigma_cube_square_38_40 (n : ℕ) (hn : 38 ≤ n) (hn' : n ≤ 40)
    (c : ℕ → K) (hc : NonzeroWeights n c) : residueSigma 3 (intervalCore n c ^ 2) ≤ 9 := by
  have hN : n ^ 2 ≤ 40 ^ 2 := Nat.pow_le_pow_left hn' 2
  apply Finset.sup_le
  intro α hα
  by_cases hz : α = 0
  · subst α
    have h := residueWeight_zero_le_of_excluded_powers 3 (n ^ 2) 11 (by decide)
      (intervalCore n c ^ 2) ((integerSupported_intervalCore n c hc).pow 2)
      (by omega) ({7, 11} : Finset ℕ) (by
        intro b hb
        have hb' : b = 7 ∨ b = 11 := by simpa using hb
        rcases hb' with rfl | rfl
        · exact not_mem_core_square_support_of_not_product n (7 ^ 3) c hc (by decide)
            (Arithmetic.middle_cube_exclusions hn').1
        · exact not_mem_core_square_support_of_not_product n (11 ^ 3) c hc (by decide)
            (Arithmetic.middle_cube_exclusions hn').2)
    convert h using 1 <;> decide
  · apply residueWeight_nonzero_le_of_integerSupported 3 (n ^ 2) 9 (by decide) _
      ((integerSupported_intervalCore n c hc).pow 2) α hz
    omega

theorem intervalCore_middle_cube_square_capacity (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (h27 : n ≠ 27) (h28 : n ≠ 28) :
    residueSigma 3 (intervalCore n c ^ 2) ≤ Arithmetic.squareCost n := by
  by_cases hnaive : n ^ 2 < (Arithmetic.squareCost n + 1) ^ 3
  · exact residueSigma_intervalCore_pow_le n 3 2 _ c hc (by decide) hnaive
  have hmem : n ∈ ({26, 27, 28, 38, 39, 40} : Finset ℕ) := by
    rw [← Arithmetic.cube_residue_naive_exceptions]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn, hn'⟩, by omega⟩
  have hcases : n = 26 ∨ n = 38 ∨ n = 39 ∨ n = 40 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    tauto
  rcases hcases with rfl | rfl | rfl | rfl
  · exact (residueSigma_cube_square_26 c hc).trans (by decide)
  · exact (residueSigma_cube_square_38_40 38 (by decide) (by decide) c hc).trans (by decide)
  · exact (residueSigma_cube_square_38_40 39 (by decide) (by decide) c hc).trans (by decide)
  · exact (residueSigma_cube_square_38_40 40 (by decide) (by decide) c hc).trans (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem cube_first_budget_checked : ∀ n ∈ Finset.Icc 25 66,
    n < (Arithmetic.freshCount n + 1) ^ 3 := by
  weighted_decide

theorem intervalCore_middle_cube_first_capacity (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66) :
    residueSigma 3 (intervalCore n c) ≤ Arithmetic.freshCount n := by
  simpa using residueSigma_intervalCore_pow_le n 3 1 (Arithmetic.freshCount n) c hc
    (by decide) (by simpa using cube_first_budget_checked n (Finset.mem_Icc.mpr ⟨hn, hn'⟩))

theorem intervalCore_middle_cube_capacity (n j : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (h27 : n ≠ 27) (h28 : n ≠ 28) (hj : 0 < j) (hj3 : j < 3) :
    residueSigma 3 (intervalCore n c ^ j) ≤
      (Arithmetic.freshCount n + j - 1).choose j := by
  have hjcases : j = 1 ∨ j = 2 := by omega
  rcases hjcases with rfl | rfl
  · simpa using intervalCore_middle_cube_first_capacity n c hc hn hn'
  · have h := intervalCore_middle_cube_square_capacity n c hc hn hn' h27 h28
    simpa only [← Arithmetic.aggregateCost_two n, Arithmetic.aggregateCost] using h

end WeightedPilz

import WeightedPilz.ProductCoefficients
import WeightedPilz.IntervalFresh
import WeightedPilz.Arithmetic.UniqueProducts
import Mathlib.Tactic.Tauto

noncomputable section
namespace WeightedPilz

open scoped BigOperators
open MvPolynomial
variable {K : Type*} [Field K]

theorem arithmetic_core_eq_interval_set (n : ℕ) :
    Arithmetic.core n = Finset.Icc 1 n \ intervalFreshPrimes n := by
  ext a
  simp only [Arithmetic.core, Finset.mem_filter, Finset.mem_sdiff,
    Pilz.mem_freshPrimes_iff, Finset.mem_Icc]
  tauto

theorem intervalCore_eq_arithmetic_core (n : ℕ) (c : ℕ → K) :
    intervalCore n c = polynomialOf (Arithmetic.core n) c := by
  rw [arithmetic_core_eq_interval_set]
  rfl

/-- Every actual unique integer product occurs in the support of the square. -/
theorem uniqueProducts_subset_square_support (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (h2 : (2 : K) ≠ 0) :
    (Arithmetic.uniqueProducts n).image Nat.factorization ⊆ (intervalCore n c ^ 2).support := by
  intro e he
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp he
  apply MvPolynomial.mem_support_iff.mpr
  rw [intervalCore_eq_arithmetic_core]
  exact coeff_square_ne_zero_of_unique_product (Arithmetic.core n) c
    (fun a ha => (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1)
    (fun a ha => hc a (Finset.mem_filter.mp ha).1) h2
    (Finset.mem_filter.mp hm).2

theorem uniqueProducts_card_le_square_weight (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (h2 : (2 : K) ≠ 0) :
    (Arithmetic.uniqueProducts n).card ≤ weight (intervalCore n c ^ 2) := by
  classical
  have h := Finset.card_le_card (uniqueProducts_subset_square_support n c hc h2)
  have hinj : Set.InjOn Nat.factorization (Arithmetic.uniqueProducts n) := by
    intro a ha b hb hab
    exact Nat.factorization_inj
      (ne_of_gt (Arithmetic.products_mem_bounds (Finset.mem_filter.mp ha).1).1)
      (ne_of_gt (Arithmetic.products_mem_bounds (Finset.mem_filter.mp hb).1).1) hab
  rw [Finset.card_image_iff.mpr hinj] at h
  exact h

/-- Every one-term multiplier retains the unique-product square lower bound,
including monomials involving variables outside the interval. -/
theorem uniqueProducts_card_le_square_mul_weight_one (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (h2 : (2 : K) ≠ 0) (B : Poly K) (hB : weight B = 1) :
    (Arithmetic.uniqueProducts n).card ≤ weight (intervalCore n c ^ 2 * B) := by
  obtain ⟨e, a, ha, hBa⟩ := Finsupp.card_support_eq_one'.mp hB
  change B = monomial e a at hBa
  rw [hBa, mul_comm, weight_scalar_monomial_mul e ha]
  exact uniqueProducts_card_le_square_weight n c hc h2

end WeightedPilz


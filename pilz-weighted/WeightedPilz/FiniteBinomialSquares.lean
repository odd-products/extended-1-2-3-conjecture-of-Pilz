import WeightedPilz.BinomialZeroSlices
import WeightedPilz.UniqueProductCoefficients
import WeightedPilz.Arithmetic.BinomialSquareWitnesses

/-! The four finite square times binomial bounds. A coordinate-zero slice
is transverse to any direction with nonzero component in that coordinate.
The finite unique-product certificates therefore supply enough occupied
lines, including directions involving additional variables. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial

variable {σ K : Type*} [Field K]

/-- Any certified family of unique products with uniformly large
coordinate-zero slices bounds every binomial multiple of the square. -/
theorem square_mul_binomial_bound_of_witnesses (n N : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Arithmetic.uniqueProducts n)
    (hN : ∀ j, N ≤ (S.filter (fun m => m.factorization j = 0)).card)
    (c : ℕ → K) (hc : NonzeroWeights n c) (h2 : (2 : K) ≠ 0)
    (B : Poly K) (hB : weight B = 2) :
    2 * N ≤ weight (intervalCore n c ^ 2 * B) := by
  classical
  obtain ⟨a, b, u, v, hab, hu, hv, rfl⟩ := exists_two_monomials_of_weight_two B hB
  have hex : ∃ j, a j ≠ b j := by
    by_contra! h
    exact hab (Finsupp.ext h)
  obtain ⟨j, hj⟩ := hex
  let T := S.filter (fun m => m.factorization j = 0)
  have hT : T.image Nat.factorization ⊆ (intervalCore n c ^ 2).support := by
    apply Finset.Subset.trans _ (uniqueProducts_subset_square_support n c hc h2)
    apply Finset.image_subset_image
    exact (Finset.filter_subset _ _).trans hS
  have hinj : Set.InjOn Nat.factorization T := by
    intro x hx y hy hxy
    have hxpos := (Arithmetic.products_mem_bounds (Finset.mem_filter.mp
      (hS (Finset.mem_filter.mp hx).1)).1).1
    have hypos := (Arithmetic.products_mem_bounds (Finset.mem_filter.mp
      (hS (Finset.mem_filter.mp hy).1)).1).1
    exact Nat.factorization_inj (ne_of_gt hxpos) (ne_of_gt hypos) hxy
  have hlines := weight_mul_binomial_of_zero_slice (intervalCore n c ^ 2)
    (T.image Nat.factorization) hT a b u v hu hv j hj (by
      intro e he
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp he
      exact (Finset.mem_filter.mp hm).2)
  rw [Finset.card_image_iff.mpr hinj] at hlines
  exact (Nat.mul_le_mul_left 2 (hN j)).trans hlines

theorem small_square_mul_binomial_bound (n : ℕ) (hn : n = 26 ∨ n = 27 ∨ n = 28)
    (c : ℕ → K) (hc : NonzeroWeights n c) (h2 : (2 : K) ≠ 0)
    (B : Poly K) (hB : weight B = 2) :
    44 ≤ weight (intervalCore n c ^ 2 * B) :=
  square_mul_binomial_bound_of_witnesses n 22 Arithmetic.smallSquareWitnesses
    (Arithmetic.smallSquareWitnesses_subset n hn)
    Arithmetic.smallSquareWitnesses_zero_slice c hc h2 B hB

theorem forty_square_mul_binomial_bound
    (c : ℕ → K) (hc : NonzeroWeights 40 c) (h2 : (2 : K) ≠ 0)
    (B : Poly K) (hB : weight B = 2) :
    20 ≤ weight (intervalCore 40 c ^ 2 * B) :=
  square_mul_binomial_bound_of_witnesses 40 10 Arithmetic.fortySquareWitnesses
    Arithmetic.fortySquareWitnesses_subset
    Arithmetic.fortySquareWitnesses_zero_slice c hc h2 B hB

/-- `lem:finite-binomial-squares`, with the manuscript's exact four bounds. -/
theorem finite_binomial_square_bounds (n : ℕ)
    (hn : n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 40)
    (c : ℕ → K) (hc : NonzeroWeights n c) (h2 : (2 : K) ≠ 0)
    (B : Poly K) (hB : weight B = 2) :
    (if n = 26 then 16 else if n = 40 then 20 else 44) ≤
      weight (intervalCore n c ^ 2 * B) := by
  rcases hn with rfl | rfl | rfl | rfl
  · have h := small_square_mul_binomial_bound 26 (Or.inl rfl) c hc h2 B hB
    change 16 ≤ weight (intervalCore 26 c ^ 2 * B)
    exact (by decide : 16 ≤ 44).trans h
  · simpa using small_square_mul_binomial_bound 27 (Or.inr (Or.inl rfl)) c hc h2 B hB
  · simpa using small_square_mul_binomial_bound 28 (Or.inr (Or.inr rfl)) c hc h2 B hB
  · simpa using forty_square_mul_binomial_bound c hc h2 B hB

end WeightedPilz

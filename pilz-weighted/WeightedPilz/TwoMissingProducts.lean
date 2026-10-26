import WeightedPilz.TranslateCover
import WeightedPilz.UniqueProductCoefficients
import WeightedPilz.Arithmetic.TwoMissingCertificates

/-! The two-missing-products estimate for the exceptional cube-residue
indices. All polynomial multipliers may use additional variables. -/

noncomputable section
namespace WeightedPilz

open MvPolynomial
variable {K : Type*} [Field K]

theorem two_missing_products_translate (n : ℕ) (hn : n = 27 ∨ n = 28)
    (b d : ℕ →₀ ℕ) :
    ((Arithmetic.uniqueProducts n).image (fun u => u.factorization + b) ∩
      (Arithmetic.core n).image (fun a => a.factorization + d)).card + 2 ≤
      (Arithmetic.core n).card := by
  refine translated_integer_support_inter_card (Arithmetic.core n) (Arithmetic.uniqueProducts n)
    ?_ ?_ ?_ (Arithmetic.two_missing_anchored n hn) b d
  · intro a ha
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
  · intro u hu
    exact (Arithmetic.products_mem_bounds (Finset.mem_filter.mp hu).1).1
  · rcases hn with rfl | rfl <;> decide +kernel

/-- Equation `fin-unique-cover-bound`, with truncated subtraction avoided.
`E` may contain fresh-cube variables or any other additional variables. -/
theorem unique_cover_bound (n : ℕ) (hn : n = 27 ∨ n = 28)
    (c : ℕ → K) (hc : NonzeroWeights n c) (h2 : (2 : K) ≠ 0)
    (B E : Poly K) (hB : weight B = 1) :
    (Arithmetic.uniqueProducts n).card ≤
      weight (intervalCore n c ^ 2 * B - intervalCore n c * E) +
      (weight (intervalCore n c) - 2) * weight E := by
  classical
  obtain ⟨b, a, ha, hBa⟩ := Finsupp.card_support_eq_one'.mp hB
  change B = monomial b a at hBa
  rw [hBa]
  let T := (Arithmetic.uniqueProducts n).image (fun u => u.factorization + b)
  have hT : T ⊆ (intervalCore n c ^ 2 * monomial b a).support := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
    have hsupport : (intervalCore n c ^ 2 * monomial b a).support =
        (intervalCore n c ^ 2).support.map (addRightEmbedding b) :=
      AddMonoidAlgebra.support_mul_single (intervalCore n c ^ 2) a (by simp [ha]) b
    rw [hsupport]
    exact Finset.mem_map.mpr ⟨u.factorization,
      uniqueProducts_subset_square_support n c hc h2 (Finset.mem_image.mpr ⟨u, hu, rfl⟩), rfl⟩
  have hcardT : T.card = (Arithmetic.uniqueProducts n).card := by
    apply Finset.card_image_iff.mpr
    intro u hu v hv heq
    exact Nat.factorization_inj
      (ne_of_gt (Arithmetic.products_mem_bounds (Finset.mem_filter.mp hu).1).1)
      (ne_of_gt (Arithmetic.products_mem_bounds (Finset.mem_filter.mp hv).1).1)
      (add_right_cancel heq)
  have hcoreWeight : weight (intervalCore n c) = (Arithmetic.core n).card := by
    rw [intervalCore_eq_arithmetic_core]
    exact weight_polynomialOf _ c
      (fun a ha => (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1)
      (fun a ha => hc a (Finset.mem_filter.mp ha).1)
  have hcover (d : ℕ →₀ ℕ) :
      (T ∩ (intervalCore n c).support.image (fun e => e + d)).card ≤
        weight (intervalCore n c) - 2 := by
    rw [intervalCore_support n c hc, ← arithmetic_core_eq_interval_set,
      Finset.image_image, hcoreWeight]
    have h := two_missing_products_translate n hn b d
    change ((Arithmetic.uniqueProducts n).image (fun u => u.factorization + b) ∩
      (Arithmetic.core n).image (fun a => a.factorization + d)).card ≤ _
    omega
  have h := weight_sub_lower_of_translate_cover
    (intervalCore n c ^ 2 * monomial b a) (intervalCore n c) E T hT
    (weight (intervalCore n c) - 2) hcover
  rw [hcardT] at h
  exact h

theorem unique_cover_bound_reverse (n : ℕ) (hn : n = 27 ∨ n = 28)
    (c : ℕ → K) (hc : NonzeroWeights n c) (h2 : (2 : K) ≠ 0)
    (B E : Poly K) (hB : weight B = 1) :
    (Arithmetic.uniqueProducts n).card ≤
      weight (intervalCore n c * E - intervalCore n c ^ 2 * B) +
      (weight (intervalCore n c) - 2) * weight E := by
  have h := unique_cover_bound n hn c hc h2 B E hB
  have heq : weight (intervalCore n c * E - intervalCore n c ^ 2 * B) =
      weight (intervalCore n c ^ 2 * B - intervalCore n c * E) := by
    rw [← neg_sub (intervalCore n c ^ 2 * B) (intervalCore n c * E)]
    simp only [weight, MvPolynomial.support_neg]
  rw [heq]
  exact h

end WeightedPilz

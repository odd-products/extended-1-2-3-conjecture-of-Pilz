import Pilz.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Ring.Canonical

/-!
# Finite sets and the arithmetic polynomial model

This file defines the paper's `A * B` directly by odd representation counts,
then proves its encoding by multiplication over `ZMod 2`. Positivity of the
integer inputs is explicit throughout: zero is not an integer in the paper's
convention for `ℕ`.
-/

noncomputable section

namespace Pilz

open scoped BigOperators

/-- Number of ordered representations `m = a * b` with `a ∈ A`, `b ∈ B`. -/
def representationCount (A B : Finset ℕ) (m : ℕ) : ℕ :=
  ((A ×ˢ B).filter fun ab => ab.1 * ab.2 = m).card

/-- Products that can occur before parity cancellation. -/
def productCandidates (A B : Finset ℕ) : Finset ℕ :=
  (A ×ˢ B).image fun ab => ab.1 * ab.2

/-- The paper's odd product of two finite sets. -/
def oddProduct (A B : Finset ℕ) : Finset ℕ :=
  (productCandidates A B).filter fun m => Odd (representationCount A B m)

theorem mem_oddProduct_iff (A B : Finset ℕ) (m : ℕ) :
    m ∈ oddProduct A B ↔ Odd (representationCount A B m) := by
  classical
  constructor
  · intro hm
    exact (Finset.mem_filter.mp hm).2
  · intro hm
    apply Finset.mem_filter.mpr
    refine ⟨?_, hm⟩
    have hcount : 0 < representationCount A B m := hm.pos
    obtain ⟨ab, hab⟩ := Finset.card_pos.mp hcount
    exact Finset.mem_image.mpr ⟨ab, (Finset.mem_filter.mp hab).1,
      (Finset.mem_filter.mp hab).2⟩

theorem oddProduct_positive (A B : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hB : ∀ b ∈ B, 0 < b) :
    ∀ m ∈ oddProduct A B, 0 < m := by
  classical
  intro m hm
  obtain ⟨⟨a, b⟩, hab, rfl⟩ :=
    Finset.mem_image.mp (Finset.mem_filter.mp hm).1
  exact Nat.mul_pos (hA a (Finset.mem_product.mp hab).1)
    (hB b (Finset.mem_product.mp hab).2)

private theorem nsmul_monomialOf (k m : ℕ) :
    k • monomialOf m = if Odd k then monomialOf m else 0 := by
  classical
  simp only [monomialOf, MvPolynomial.smul_monomial, nsmul_eq_mul, mul_one]
  by_cases hk : Odd k
  · simp [hk, ZMod.natCast_eq_one_iff_odd.mpr hk]
  · simp [hk, ZMod.natCast_eq_zero_iff_even.mpr (Nat.not_odd_iff_even.mp hk)]

/-- The multiplication identity in the paper's polynomial encoding. -/
theorem polynomialOf_oddProduct (A B : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hB : ∀ b ∈ B, 0 < b) :
    polynomialOf (oddProduct A B) = polynomialOf A * polynomialOf B := by
  classical
  symm
  calc
    polynomialOf A * polynomialOf B =
        ∑ ab ∈ A ×ˢ B, monomialOf (ab.1 * ab.2) := by
      simp only [polynomialOf, Finset.sum_mul, Finset.mul_sum, Finset.sum_product]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact (monomialOf_mul (ne_of_gt (hA a ha)) (ne_of_gt (hB b hb))).symm
    _ = ∑ m ∈ productCandidates A B,
        representationCount A B m • monomialOf m := by
      symm
      simpa only [representationCount, Finset.sum_const] using
        (Finset.sum_fiberwise_of_maps_to'
          (s := A ×ˢ B) (t := productCandidates A B)
          (g := fun ab : ℕ × ℕ => ab.1 * ab.2)
          (fun ab hab => Finset.mem_image_of_mem _ hab) monomialOf)
    _ = ∑ m ∈ productCandidates A B,
        if Odd (representationCount A B m) then monomialOf m else 0 := by
      apply Finset.sum_congr rfl
      intro m _
      exact nsmul_monomialOf _ _
    _ = polynomialOf (oddProduct A B) := by
      simp only [polynomialOf, oddProduct, Finset.sum_filter]

/-- Weight is exactly the size of the odd product, with no loss in encoding. -/
theorem weight_mul_polynomialOf (A B : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hB : ∀ b ∈ B, 0 < b) :
    weight (polynomialOf A * polynomialOf B) = (oddProduct A B).card := by
  rw [← polynomialOf_oddProduct A B hA hB]
  exact weight_polynomialOf _ (oddProduct_positive A B hA hB)

/-- A polynomial instance of Theorem A gives the original finite-set statement. -/
theorem oddProduct_interval_lower_bound {n : ℕ} (hn : ConjectureAt n)
    (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    n ≤ (oddProduct A (Finset.Icc 1 n)).card := by
  have hI : ∀ b ∈ Finset.Icc 1 n, 0 < b :=
    fun _ hb => (Finset.mem_Icc.mp hb).1
  rw [← weight_mul_polynomialOf A (Finset.Icc 1 n) hA hI]
  simpa [interval_eq_polynomialOf, mul_comm] using
    hn (polynomialOf A) (polynomialOf_ne_zero A hA hne)

end Pilz

import Pilz.Basic
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Removing a common monomial factor

This is the normalization step in the elementary reductions of Section 2.
It uses the coordinatewise minimum of the support, and the quotient by that
monomial. Removing this factor preserves all product weights and introduces
no new variable names.
-/

noncomputable section

namespace Pilz

open MvPolynomial

private theorem weight_monomial_mul' (s : ℕ →₀ ℕ) (P : Poly) :
    weight ((monomial s 1 : Poly) * P) = weight P := by
  have hs : (monomial s 1 * P : Poly).support = P.support.map (addLeftEmbedding s) :=
    AddMonoidAlgebra.support_single_mul P 1 (by simp) s
  simp only [weight, hs, Finset.card_map]

/-- If every term is divisible by a monomial, monomial division is exact. -/
theorem monomial_mul_divMonomial_eq (H : Poly) (e : ℕ →₀ ℕ)
    (he : ∀ d ∈ H.support, e ≤ d) :
    (monomial e 1 : Poly) * divMonomial H e = H := by
  have hrem : modMonomial H e = 0 := by
    ext d
    by_cases hd : d ∈ H.support
    · exact coeff_modMonomial_of_le H (he d hd)
    · by_cases hed : e ≤ d
      · exact coeff_modMonomial_of_le H hed
      · rw [coeff_modMonomial_of_not_le H hed]
        exact notMem_support_iff.mp hd
  simpa [hrem] using divMonomial_add_modMonomial H e

/-- Normalization preserves weight, product weight, and the set of variables
that may occur. The coordinate-zero witnesses express that no nonconstant
monomial divides every term of the normalized quotient. -/
theorem exists_normalization (H : Poly) (hH : H ≠ 0) :
    ∃ (e : ℕ →₀ ℕ) (D : Poly),
      H = monomial e 1 * D ∧ D ≠ 0 ∧
      (∀ p : ℕ, ∃ d ∈ D.support, d p = 0) ∧
      weight D = weight H ∧
      (∀ P : Poly, weight (P * D) = weight (P * H)) ∧
      (∀ p : ℕ, (∃ d ∈ D.support, 0 < d p) → ∃ d ∈ H.support, 0 < d p) := by
  classical
  have hs : H.support.Nonempty := support_nonempty.mpr hH
  let e : ℕ →₀ ℕ := H.support.inf' hs id
  let D : Poly := divMonomial H e
  have he : ∀ d ∈ H.support, e ≤ d := by
    intro d hd
    exact Finset.inf'_le id hd
  have hfactor : H = monomial e 1 * D :=
    (monomial_mul_divMonomial_eq H e he).symm
  have hD : D ≠ 0 := by
    intro hz
    rw [hfactor, hz, mul_zero] at hH
    exact hH rfl
  refine ⟨e, D, hfactor, hD, ?_, ?_, ?_, ?_⟩
  · intro p
    have heval : e p = H.support.inf' hs (fun d => d p) := by
      exact Finset.comp_inf'_eq_inf'_comp hs (fun d : ℕ →₀ ℕ => d p)
        (fun x y => rfl)
    obtain ⟨d, hd, hde⟩ := Finset.exists_mem_eq_inf' hs (fun d : ℕ →₀ ℕ => d p)
    have hcoord : e p = d p := heval.trans hde
    refine ⟨d - e, ?_, ?_⟩
    · apply mem_support_iff.mpr
      change coeff (d - e) (divMonomial H e) ≠ 0
      rw [coeff_divMonomial, add_tsub_cancel_of_le (he d hd)]
      exact mem_support_iff.mp hd
    · simp [Finsupp.tsub_apply, hcoord]
  · rw [hfactor, weight_monomial_mul']
  · intro P
    rw [hfactor]
    calc
      weight (P * D) = weight (monomial e 1 * (P * D)) :=
        (weight_monomial_mul' e (P * D)).symm
      _ = weight (P * (monomial e 1 * D)) := by rw [mul_left_comm]
  · intro p hp
    obtain ⟨d, hd, hdp⟩ := hp
    refine ⟨e + d, ?_, ?_⟩
    · apply mem_support_iff.mpr
      exact (mem_support_iff.mp hd : coeff d (divMonomial H e) ≠ 0)
    · change 0 < e p + d p
      exact hdp.trans_le (Nat.le_add_left _ _)

end Pilz

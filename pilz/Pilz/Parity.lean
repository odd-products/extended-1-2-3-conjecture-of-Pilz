import Pilz.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Weight parity and Frobenius squares

This file formalizes the weight-parity lemma and the first assertion of the
paper's subsection "Parity classes".  Coefficients are exactly `ZMod 2`.
-/

noncomputable section

namespace Pilz

private theorem coefficient_eq_one {c : ZMod 2} (hc : c ≠ 0) : c = 1 := by
  fin_cases c <;> simp_all

/-- Evaluating every variable at one gives the weight modulo two. -/
theorem eval_one_eq_weight (P : Poly) :
    MvPolynomial.eval (fun _ : ℕ => (1 : ZMod 2)) P = (weight P : ZMod 2) := by
  classical
  rw [MvPolynomial.eval_eq]
  simp only [one_pow, Finset.prod_const_one, mul_one]
  calc
    ∑ d ∈ P.support, MvPolynomial.coeff d P = ∑ _d ∈ P.support, (1 : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact coefficient_eq_one (MvPolynomial.mem_support_iff.mp hd)
    _ = (weight P : ZMod 2) := by simp [weight]

/-- Paper, Lemma "Weight parity": multiplication multiplies weights modulo two. -/
theorem weight_mul_parity (P H : Poly) :
    (weight (P * H) : ZMod 2) = (weight P : ZMod 2) * (weight H : ZMod 2) := by
  rw [← eval_one_eq_weight, map_mul, eval_one_eq_weight, eval_one_eq_weight]

/-- The natural-number congruence form of the paper's parity identity. -/
theorem weight_mul_mod_two (P H : Poly) :
    weight (P * H) % 2 = (weight P * weight H) % 2 := by
  apply (ZMod.natCast_eq_natCast_iff' _ _ 2).mp
  simpa only [Nat.cast_mul] using weight_mul_parity P H

/-- A nonzero multiple of an even-weight polynomial has even weight. -/
theorem even_weight_mul {P : Poly} (hP : Even (weight P)) (H : Poly) :
    Even (weight (P * H)) := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  rw [weight_mul_parity, ZMod.natCast_eq_zero_iff_even.mpr hP, zero_mul]

/-- Doubling every exponent is the monomial map induced by squaring. -/
def doubleExponent (d : ℕ →₀ ℕ) : ℕ →₀ ℕ := 2 • d

theorem doubleExponent_injective : Function.Injective doubleExponent := by
  intro a b h
  ext i
  have hi := congrArg (fun d : ℕ →₀ ℕ => d i) h
  simp only [doubleExponent, two_smul, Finsupp.add_apply] at hi
  omega

/-- Frobenius squares coefficients trivially and doubles monomial exponents. -/
theorem square_eq_mapDomain (P : Poly) :
    P ^ 2 = Finsupp.mapDomain doubleExponent P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [MvPolynomial.monomial_pow]
      have hc : c ^ 2 = c := by fin_cases c <;> norm_num
      rw [hc]
      exact Finsupp.mapDomain_single.symm
  | add P Q hP hQ =>
      rw [CharTwo.add_sq, hP, hQ, Finsupp.mapDomain_add]

/-- The support of a square is obtained by doubling each support exponent. -/
theorem support_square (P : Poly) :
    (P ^ 2).support = P.support.image doubleExponent := by
  rw [square_eq_mapDomain]
  exact Finsupp.mapDomain_support_of_injective doubleExponent_injective P

/-- Every exponent in the support of a square is even. -/
theorem exponent_mod_two_of_mem_support_square {P : Poly} {d : ℕ →₀ ℕ}
    (hd : d ∈ (P ^ 2).support) (i : ℕ) : d i % 2 = 0 := by
  classical
  rw [support_square] at hd
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hd
  simp only [doubleExponent, two_smul, Finsupp.add_apply]
  omega

/-- Squaring preserves the number of terms in characteristic two. -/
theorem weight_square (P : Poly) : weight (P ^ 2) = weight P := by
  classical
  unfold weight
  rw [support_square]
  exact Finset.card_image_of_injective _ doubleExponent_injective

/-- Formal derivatives kill Frobenius squares, as used in the descent section. -/
theorem pderiv_square (P : Poly) (i : ℕ) : MvPolynomial.pderiv i (P ^ 2) = 0 := by
  rw [MvPolynomial.pderiv_pow]
  simp [CharTwo.two_eq_zero]

/-- The equality example `A = [n]` from the paper's introduction, for every `n`. -/
theorem weight_interval_self_mul (n : ℕ) :
    weight (interval n * interval n) = n := by
  rw [← pow_two, weight_square, weight_interval]

/-- Theorem A at interval length two, using parity and the domain property. -/
theorem conjectureAt_two : ConjectureAt 2 := by
  intro H hH
  have hpos : 0 < weight (interval 2 * H) :=
    weight_pos (mul_ne_zero (interval_ne_zero (by norm_num)) hH)
  have hpar : (weight (interval 2 * H) : ZMod 2) = 0 := by
    rw [weight_mul_parity, weight_interval]
    simp [CharTwo.two_eq_zero]
  by_contra hsmall
  have hw : weight (interval 2 * H) = 1 := by omega
  rw [hw] at hpar
  norm_num at hpar

end Pilz

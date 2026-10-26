import WeightedPilz.Frobenius
import WeightedPilz.TwoRowGeneral

/-! Unique product coefficients with an odd exponent cannot belong to a
scalar multiple of a square in characteristic two. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ K : Type*} [Field K] [DecidableEq σ]

theorem coeff_mul_of_unique_support_sum (A B : MvPolynomial σ K)
    (a b : σ →₀ ℕ) (ha : a ∈ A.support) (hb : b ∈ B.support)
    (hunique : ∀ u ∈ A.support, ∀ v ∈ B.support,
      u + v = a + b → u = a ∧ v = b) :
    coeff (a + b) (A * B) = coeff a A * coeff b B := by
  rw [coeff_mul]
  apply Finset.sum_eq_single (a, b)
  · intro x hx hne
    by_cases hxa : x.1 ∈ A.support
    · by_cases hxb : x.2 ∈ B.support
      · obtain ⟨h1, h2⟩ := hunique x.1 hxa x.2 hxb (Finset.mem_antidiagonal.mp hx)
        exact False.elim (hne (Prod.ext h1 h2))
      · rw [notMem_support_iff.mp hxb, mul_zero]
    · rw [notMem_support_iff.mp hxa, zero_mul]
  · intro hnot
    exact False.elim (hnot (Finset.mem_antidiagonal.mpr rfl))

theorem coeff_mul_ne_zero_of_unique_support_sum (A B : MvPolynomial σ K)
    (a b : σ →₀ ℕ) (ha : a ∈ A.support) (hb : b ∈ B.support)
    (hunique : ∀ u ∈ A.support, ∀ v ∈ B.support,
      u + v = a + b → u = a ∧ v = b) : coeff (a + b) (A * B) ≠ 0 := by
  rw [coeff_mul_of_unique_support_sum A B a b ha hb hunique]
  exact mul_ne_zero (mem_support_iff.mp ha) (mem_support_iff.mp hb)

theorem coeff_square_zero_of_odd [CharP K 2] (P : MvPolynomial σ K)
    (d : σ →₀ ℕ) (j : σ) (hodd : d j % 2 = 1) : coeff d (P ^ 2) = 0 := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial e a =>
      have hne : 2 • e ≠ d := by
        intro heq
        have hval := congrArg (fun f : σ →₀ ℕ => f j % 2) heq
        simp [Finsupp.smul_apply, smul_eq_mul, hodd] at hval
      simp only [monomial_pow, coeff_monomial, if_neg hne]
  | add P Q hP hQ => rw [CharTwo.add_sq, coeff_add, hP, hQ, add_zero]

theorem mul_ne_scalar_square_of_unique_odd_sum [CharP K 2]
    (A B H : MvPolynomial σ K) (a b : σ →₀ ℕ)
    (ha : a ∈ A.support) (hb : b ∈ B.support)
    (hunique : ∀ u ∈ A.support, ∀ v ∈ B.support,
      u + v = a + b → u = a ∧ v = b)
    (j : σ) (hodd : (a + b) j % 2 = 1) (c : K) :
    A * B ≠ C c * H ^ 2 := by
  intro heq
  have hcoeff := coeff_mul_ne_zero_of_unique_support_sum A B a b ha hb hunique
  rw [heq, coeff_C_mul, coeff_square_zero_of_odd H (a + b) j hodd, mul_zero] at hcoeff
  exact hcoeff rfl

end WeightedPilz

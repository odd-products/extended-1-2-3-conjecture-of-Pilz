import WeightedPilz.Distance
import Mathlib.Algebra.MvPolynomial.Eval

/-! Diagonal changes of variables by nonzero scalars preserve exact supports. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ K : Type*} [Field K]

def rescale (u : σ → Kˣ) : MvPolynomial σ K →+* MvPolynomial σ K :=
  eval₂Hom C (fun i => C (u i : K) * X i)

@[simp] theorem rescale_C (u : σ → Kˣ) (a : K) : rescale u (C a) = C a := by
  simp [rescale]

@[simp] theorem rescale_X (u : σ → Kˣ) (i : σ) :
    rescale u (X i) = C (u i : K) * X i := by
  simp [rescale]

theorem rescale_monomial (u : σ → Kˣ) (d : σ →₀ ℕ) (a : K) :
    rescale u (monomial d a) = monomial d (a * d.prod (fun i n => (u i : K) ^ n)) := by
  classical
  rw [rescale, eval₂Hom_monomial]
  simp only [monomial_eq, Finsupp.prod, mul_pow,
    ← map_pow, Finset.prod_mul_distrib, ← map_prod, map_mul]
  ring

theorem coeff_rescale (u : σ → Kˣ) (P : MvPolynomial σ K) (d : σ →₀ ℕ) :
    coeff d (rescale u P) = coeff d P * d.prod (fun i n => (u i : K) ^ n) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [rescale_monomial]
    by_cases h : s = d
    · subst s
      simp
    · simp [coeff_monomial, h]
  | add P Q hP hQ =>
    simp only [map_add, coeff_add, hP, hQ, add_mul]

theorem support_rescale (u : σ → Kˣ) (P : MvPolynomial σ K) :
    (rescale u P).support = P.support := by
  classical
  ext d
  have hprod : d.prod (fun i n => (u i : K) ^ n) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (u i).ne_zero)
  simp [mem_support_iff, coeff_rescale, hprod]

@[simp] theorem weight_rescale (u : σ → Kˣ) (P : MvPolynomial σ K) :
    weight (rescale u P) = weight P := by
  simp only [weight, support_rescale]

@[simp] theorem rescale_eq_zero (u : σ → Kˣ) (P : MvPolynomial σ K) :
    rescale u P = 0 ↔ P = 0 := by
  rw [← MvPolynomial.support_eq_empty, support_rescale, MvPolynomial.support_eq_empty]

theorem rescale_inv_rescale (u : σ → Kˣ) (P : MvPolynomial σ K) :
    rescale (fun i => (u i)⁻¹) (rescale u P) = P := by
  classical
  ext d
  rw [coeff_rescale, coeff_rescale, mul_assoc]
  have hprod : d.prod (fun i n => (u i : K) ^ n) *
      d.prod (fun i n => ((↑((u i)⁻¹)) : K) ^ n) = 1 := by
    simp only [Finsupp.prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i hi
    simp only [← mul_pow, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (u i).ne_zero, one_pow]
  rw [hprod, mul_one]

/-- A diagonal change of variables preserves the attained minimum support. -/
theorem distance_rescale (u : σ → Kˣ) (P : MvPolynomial σ K) :
    distance (rescale u P) = distance P := by
  have upper : ∀ (v : σ → Kˣ) (Q : MvPolynomial σ K),
      distance (rescale v Q) ≤ distance Q := by
    intro v Q
    obtain ⟨H, hH, hw⟩ := exists_weight_eq_distance Q
    have hRH : rescale v H ≠ 0 := by simpa using hH
    have h := distance_le_weight_mul (rescale v Q) (rescale v H) hRH
    rw [← map_mul, weight_rescale, hw] at h
    exact h
  apply Nat.le_antisymm (upper u P)
  simpa only [rescale_inv_rescale] using upper (fun i => (u i)⁻¹) (rescale u P)

end WeightedPilz

import WeightedPilz.Distance
import WeightedPilz.Support
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.Ring

/-!
# Euler operators and the power gap

The Euler operator is diagonal on monomials. Subtracting one occupied
exponent deletes a term, while the power rule keeps the result divisible by
the original polynomial. This is the differential step of `lem:powergap`.
-/

noncomputable section

namespace WeightedPilz

open MvPolynomial

variable {σ K : Type*} [Field K]

/-- The Euler operator in one coordinate. -/
def euler (i : σ) (P : MvPolynomial σ K) : MvPolynomial σ K :=
  X i * pderiv i P

theorem coeff_euler (i : σ) (P : MvPolynomial σ K) (d : σ →₀ ℕ) :
    coeff d (euler i P) = (d i : K) * coeff d P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [euler, X_mul_pderiv_monomial, coeff_smul]
    by_cases he : e = d
    · subst e
      simp [coeff_monomial, nsmul_eq_mul]
    · simp [coeff_monomial, he, nsmul_eq_mul]
  | add P Q hP hQ =>
    simp only [euler, map_add, mul_add, coeff_add] at hP hQ ⊢
    rw [hP, hQ]

/-- The Euler operator shifted by a scalar. -/
def eulerShift (i : σ) (a : K) (P : MvPolynomial σ K) : MvPolynomial σ K :=
  euler i P - C a * P

theorem coeff_eulerShift (i : σ) (a : K) (P : MvPolynomial σ K) (d : σ →₀ ℕ) :
    coeff d (eulerShift i a P) = ((d i : K) - a) * coeff d P := by
  simp [eulerShift, coeff_euler, sub_mul]

theorem support_eulerShift_subset (i : σ) (a : K) (P : MvPolynomial σ K) :
    (eulerShift i a P).support ⊆ P.support := by
  intro d hd
  apply mem_support_iff.mpr
  intro hz
  have hne := mem_support_iff.mp hd
  exact hne (by rw [coeff_eulerShift, hz, mul_zero])

/-- Shifting by an occupied exponent strictly reduces the number of terms. -/
theorem weight_eulerShift_lt (i : σ) (P : MvPolynomial σ K)
    {d : σ →₀ ℕ} (hd : d ∈ P.support) :
    weight (eulerShift i (d i : K) P) < weight P := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨support_eulerShift_subset i _ P, ?_⟩
  intro hs
  have hd' : d ∈ (eulerShift i (d i : K) P).support := hs.symm ▸ hd
  have hn := mem_support_iff.mp hd'
  exact hn (by simp [coeff_eulerShift])

/-- A coordinate that varies in the coefficient field makes every scalar
shift of the Euler operator nonzero. -/
theorem eulerShift_ne_zero_of_variation (i : σ) (a : K) (P : MvPolynomial σ K)
    {d e : σ →₀ ℕ} (hd : d ∈ P.support) (he : e ∈ P.support)
    (hde : (d i : K) ≠ (e i : K)) : eulerShift i a P ≠ 0 := by
  intro hz
  have hd0 : ((d i : K) - a) * coeff d P = 0 := by
    rw [← coeff_eulerShift, hz, coeff_zero]
  have he0 : ((e i : K) - a) * coeff e P = 0 := by
    rw [← coeff_eulerShift, hz, coeff_zero]
  have hd1 : (d i : K) = a := sub_eq_zero.mp
    ((mul_eq_zero.mp hd0).resolve_right (mem_support_iff.mp hd))
  have he1 : (e i : K) = a := sub_eq_zero.mp
    ((mul_eq_zero.mp he0).resolve_right (mem_support_iff.mp he))
  exact hde (hd1.trans he1.symm)

theorem eulerShift_pow (i : σ) (a : K) (P : MvPolynomial σ K)
    {n : ℕ} (hn : 0 < n) (hnK : (n : K) ≠ 0) :
    eulerShift i a (P ^ n) =
      C (n : K) * P ^ (n - 1) * eulerShift i (a / (n : K)) P := by
  have hpow : P ^ n = P ^ (n - 1) * P := by
    rw [← pow_succ]
    congr 1
    omega
  have hnat : (n : MvPolynomial σ K) = C (n : K) := by simp
  have hscale : C (n : K) * C (a / (n : K)) = (C a : MvPolynomial σ K) := by
    rw [← map_mul]
    congr 1
    exact mul_div_cancel₀ a hnK
  unfold eulerShift euler
  rw [pderiv_pow, hnat, hpow]
  calc
    X i * (C (n : K) * P ^ (n - 1) * pderiv i P) - C a * (P ^ (n - 1) * P) =
      C (n : K) * P ^ (n - 1) * (X i * pderiv i P) -
        (C (n : K) * C (a / (n : K))) * (P ^ (n - 1) * P) := by rw [hscale]; ring
    _ = _ := by ring

/-- The differential power gap when two exponents remain different in the
coefficient field. No perfectness assumption is involved. -/
theorem power_gap_of_residue_variation (P : MvPolynomial σ K) (i : σ)
    {d e : σ →₀ ℕ} (hd : d ∈ P.support) (he : e ∈ P.support)
    (hde : (d i : K) ≠ (e i : K)) {n : ℕ} (hn : 2 ≤ n)
    (hnK : (n : K) ≠ 0) : distance P + 1 ≤ weight (P ^ n) := by
  classical
  have hP : P ≠ 0 := support_nonempty.mp ⟨d, hd⟩
  obtain ⟨f, hf⟩ := support_nonempty.mpr (pow_ne_zero n hP)
  let T := eulerShift i ((f i : K) / (n : K)) P
  have hT : T ≠ 0 := eulerShift_ne_zero_of_variation i _ P hd he hde
  let H := C (n : K) * P ^ (n - 2) * T
  have hnC : (C (n : K) : MvPolynomial σ K) ≠ 0 := by
    intro hz
    exact hnK (MvPolynomial.C_injective σ K (hz.trans (map_zero C).symm))
  have hH : H ≠ 0 := mul_ne_zero (mul_ne_zero
    hnC (pow_ne_zero _ hP)) hT
  have hfactor : eulerShift i (f i : K) (P ^ n) = P * H := by
    rw [eulerShift_pow i _ P (by omega) hnK]
    have hp : P ^ (n - 1) = P ^ (n - 2) * P := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hp]
    dsimp [H, T]
    ring
  have hlow := distance_le_weight_mul P H hH
  have hhigh := weight_eulerShift_lt i (P ^ n) hf
  rw [hfactor] at hhigh
  omega

/-- The characteristic-zero assertion of `lem:powergap`. -/
theorem power_gap_charZero [CharZero K] (P : MvPolynomial σ K)
    (hP : 2 ≤ weight P) {n : ℕ} (hn : 2 ≤ n) :
    distance P + 1 ≤ weight (P ^ n) := by
  classical
  have hc : 1 < P.support.card := by change 2 ≤ P.support.card at hP; omega
  obtain ⟨d, hd, e, he, hde⟩ := Finset.one_lt_card.mp hc
  have hdiff : ¬ ∀ i, d i = e i := fun h => hde (Finsupp.ext h)
  obtain ⟨i, hi⟩ := not_forall.mp hdiff
  exact power_gap_of_residue_variation P i hd he
    (fun h => hi (Nat.cast_injective h)) hn (by exact_mod_cast (show n ≠ 0 by omega))

end WeightedPilz

import WeightedPilz.BinomialPowerEquality
import WeightedPilz.ShortFreshTest

/-! Lowest rows of shifted polynomial sums and noncancellation of two base powers. -/
noncomputable section
namespace WeightedPilz
open Polynomial
variable {R : Type*} [CommRing R] [IsDomain R]

theorem trailingDegree_shifted_sum (P Q : R[X]) (a b : ℕ) (hab : a < b)
    (hP : P.coeff 0 ≠ 0) :
    (P * X ^ a + Q * X ^ b).natTrailingDegree = a ∧
    (P * X ^ a + Q * X ^ b).trailingCoeff = P.coeff 0 := by
  let W := P * X ^ a + Q * X ^ b
  have hc : W.coeff a = P.coeff 0 := by
    simp [W, coeff_mul_X_pow', show ¬b ≤ a by omega]
  have hW : W ≠ 0 := by intro hz; exact hP (by simpa [hz] using hc.symm)
  have hu : W.natTrailingDegree ≤ a := natTrailingDegree_le_of_ne_zero (hc ▸ hP)
  have hl : a ≤ W.natTrailingDegree := by
    by_contra hlt
    have hz : W.coeff W.natTrailingDegree = 0 := by
      simp [W, coeff_mul_X_pow', show ¬a ≤ W.natTrailingDegree by omega,
        show ¬b ≤ W.natTrailingDegree by omega]
    exact hW (coeff_natTrailingDegree_eq_zero.mp hz)
  have heq : W.natTrailingDegree = a := by omega
  exact ⟨heq, by rw [trailingCoeff, heq, hc]⟩

variable {σ K : Type*} [Field K]
open MvPolynomial

theorem two_monomial_base_powers_constant_ne_zero (P M N : MvPolynomial σ K)
    (hP : P ≠ 0) (hPd : 2 ≤ distance P) (hM : weight M = 1) (hN : weight N = 1)
    {i j : ℕ} (hij : i < j) : M * P ^ i + N * P ^ j ≠ 0 := by
  classical
  intro hz
  have hp : P ^ j = P ^ i * P ^ (j - i) := by rw [← pow_add, Nat.add_sub_of_le hij.le]
  have heq : M * P ^ i + N * P ^ j = P ^ i * (M + N * P ^ (j - i)) := by
    rw [hp]
    ring
  rw [heq] at hz
  have hrel : M + N * P ^ (j - i) = 0 := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero i hP)
  have hM' : M = -(N * P ^ (j - i)) := eq_neg_of_add_eq_zero_left hrel
  have hcost : 2 ≤ weight (P ^ (j - i)) := by
    have hk : 0 < j - i := by omega
    have h := hPd.trans (distance_le_weight_mul P (P ^ (j - i - 1)) (pow_ne_zero _ hP))
    rw [← pow_succ', Nat.sub_add_cancel hk] at h
    exact h
  have hw : weight M = weight (P ^ (j - i)) := by
    rw [hM']
    simp only [weight, MvPolynomial.support_neg]
    change weight (N * P ^ (j - i)) = _
    rw [mul_comm]
    exact FreshData.weight_mul_of_weight_one _ _ hN
  omega

end WeightedPilz

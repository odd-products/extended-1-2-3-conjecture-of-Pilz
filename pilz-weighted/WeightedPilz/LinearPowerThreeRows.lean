import WeightedPilz.LinearExtensionOps
import WeightedPilz.PolynomialPowerRows
import WeightedPilz.BivariatePower

/-! Three explicit rows of a reduced positive power of a linear extension. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ K : Type*} [Field K]

theorem linearExtension_power_three_rows (R D : MvPolynomial σ K) (hD : D ≠ 0)
    {n : ℕ} (hn : 2 ≤ n) :
    weight (R ^ n) + weight ((n : MvPolynomial σ K) * R * D ^ (n - 1)) +
      weight (D ^ n) ≤ weight (linearExtension R D ^ n) := by
  classical
  let Q : Polynomial (MvPolynomial σ K) := Polynomial.C R + Polynomial.C D * Polynomial.X
  have hdeg : Q.natDegree = 1 := by
    simpa only [Q, add_comm] using Polynomial.natDegree_linear hD (b := R)
  have hlc : Q.leadingCoeff = D := by
    simpa only [Q, add_comm] using Polynomial.leadingCoeff_linear hD (b := R)
  have hzero : (Q ^ n).coeff 0 = R ^ n := by
    rw [polynomial_coeff_zero_pow]
    simp [Q]
  have hnext : (Q ^ n).coeff (n - 1) = (n : MvPolynomial σ K) * R * D ^ (n - 1) := by
    have h := polynomial_coeff_penultimate_pow Q (by omega) (by omega : 0 < n)
    simpa [hdeg, hlc, Q] using h
  have htop : (Q ^ n).coeff n = D ^ n := by
    simpa only [hdeg, mul_one, hlc] using Polynomial.coeff_pow_mul_natDegree Q n
  have hmap : optionEquivLeft K σ (linearExtension R D ^ n) = Q ^ n := by
    rw [map_pow, optionEquiv_linearExtension]
  have h := weight_option_slices_le (linearExtension R D ^ n) {0, n - 1, n}
  rw [hmap] at h
  simpa only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton, show 0 ≠ n - 1 by omega, show 0 ≠ n by omega,
    show n - 1 ≠ n by omega, or_self, not_false_eq_true, add_assoc,
    hzero, hnext, htop] using h

theorem linearExtension_power_nine (R D : MvPolynomial σ K) (hD : D ≠ 0)
    (hRdist : 4 ≤ distance R) (hDdist : 2 ≤ distance D)
    (hRpower : ∀ n : ℕ, 0 < n → 6 ≤ weight (R ^ n))
    (hweight : 9 ≤ weight (linearExtension R D)) {n : ℕ} (hn : 0 < n) :
    9 ≤ weight (linearExtension R D ^ n) := by
  apply weight_pow_bound_of_reduced _ 9 _ hn
  intro k hk hkK
  by_cases hk1 : k = 1
  · simpa [hk1] using hweight
  have hk2 : 2 ≤ k := by omega
  have hzero := hRpower k hk
  have htop : 2 ≤ weight (D ^ k) := by
    have h := hDdist.trans (distance_le_weight_mul D (D ^ (k - 1)) (pow_ne_zero _ hD))
    rw [← pow_succ', Nat.sub_add_cancel hk] at h
    exact h
  have hmid : 4 ≤ weight ((k : MvPolynomial σ K) * R * D ^ (k - 1)) := by
    have heq : (k : MvPolynomial σ K) * R * D ^ (k - 1) =
        C (k : K) * (R * D ^ (k - 1)) := by simp only [map_natCast]; ring
    rw [heq, C_apply, weight_scalar_monomial_mul 0 hkK]
    exact hRdist.trans (distance_le_weight_mul R (D ^ (k - 1)) (pow_ne_zero _ hD))
  have h := linearExtension_power_three_rows R D hD hk2
  omega

end WeightedPilz

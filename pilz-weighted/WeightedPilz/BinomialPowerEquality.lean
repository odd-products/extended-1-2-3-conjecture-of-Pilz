import WeightedPilz.BivariatePower

/-! A linear binomial has only two terms in a positive power exactly at a Frobenius exponent. -/
noncomputable section
namespace WeightedPilz
open Polynomial
variable {K : Type*} [Field K]

theorem polynomial_power_support_three_of_degree_product (P : K[X])
    (h0 : P.coeff 0 ≠ 0) (h1 : P.coeff 1 ≠ 0)
    {n : ℕ} (hnK : (n : K) ≠ 0) (hdeg : 2 ≤ n * P.natDegree) :
    3 ≤ (P ^ n).support.card := by
  classical
  have hP : P ≠ 0 := fun hz => h0 (by rw [hz, coeff_zero])
  have hc0 : (P ^ n).coeff 0 ≠ 0 := by
    rw [polynomial_coeff_zero_pow]
    exact pow_ne_zero _ h0
  have hc1 : (P ^ n).coeff 1 ≠ 0 := by
    rw [polynomial_coeff_one_pow]
    exact mul_ne_zero (mul_ne_zero hnK h1) (pow_ne_zero _ h0)
  have hct : (P ^ n).coeff (n * P.natDegree) ≠ 0 := by
    rw [coeff_pow_mul_natDegree]
    exact pow_ne_zero _ (leadingCoeff_ne_zero.mpr hP)
  have hs : ({0, 1, n * P.natDegree} : Finset ℕ) ⊆ (P ^ n).support := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact mem_support_iff.mpr hc0
    · exact mem_support_iff.mpr hc1
    · exact mem_support_iff.mpr hct
  have hcard : ({0, 1, n * P.natDegree} : Finset ℕ).card = 3 := by
    simp [show 0 ≠ n * P.natDegree by omega, show 1 ≠ n * P.natDegree by omega]
  rw [← hcard]
  exact Finset.card_le_card hs

theorem distinguished_of_univariate_linear_power_two (P : K[X])
    (h0 : P.coeff 0 ≠ 0) (h1 : P.coeff 1 ≠ 0) (hdeg : P.natDegree = 1)
    (p : ℕ) [hpK : ExpChar K p] {n : ℕ} (hn : 0 < n)
    (hw : weight (((MvPolynomial.pUnitAlgEquiv.{_, 0} K).symm P) ^ n) ≤ 2) :
    ∃ e : ℕ, n = p ^ e := by
  have reduced (k : ℕ) (hk : 0 < k) (hkK : (k : K) ≠ 0)
      (hkw : weight (((MvPolynomial.pUnitAlgEquiv.{_, 0} K).symm P) ^ k) ≤ 2) : k = 1 := by
    by_contra hk1
    have hthree := polynomial_power_support_three_of_degree_product P h0 h1 hkK
      (by rw [hdeg, mul_one]; omega)
    rw [← map_pow, weight_pUnitAlgEquiv_symm] at hkw
    omega
  cases hpK with
  | zero =>
    have hn1 := reduced n hn (Nat.cast_ne_zero.mpr (ne_of_gt hn)) hw
    exact ⟨0, by simpa using hn1⟩
  | prime hp =>
    letI : ExpChar K p := ExpChar.prime hp
    obtain ⟨e, k, hpk, hfactor⟩ := Nat.exists_eq_pow_mul_and_not_dvd (ne_of_gt hn) p hp.ne_one
    have hk : 0 < k := by
      by_contra hk
      have hk0 : k = 0 := by omega
      simp [hk0] at hfactor
      omega
    have hkK : (k : K) ≠ 0 := fun hz => hpk ((CharP.cast_eq_zero_iff K p k).mp hz)
    have hkw : weight (((MvPolynomial.pUnitAlgEquiv.{_, 0} K).symm P) ^ k) ≤ 2 := by
      rw [hfactor, Nat.mul_comm, pow_mul, weight_pow_expChar] at hw
      exact hw
    have hk1 := reduced k hk hkK hkw
    exact ⟨e, by simpa [hk1] using hfactor⟩

end WeightedPilz

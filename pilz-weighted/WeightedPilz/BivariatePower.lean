import WeightedPilz.UnivariateWeight

/-! Bare-power lower bounds for the quadratic bases with constant top row. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

/-- Frobenius reduces a bare-power support estimate to exponents nonzero in
the coefficient field. -/
theorem weight_pow_bound_of_reduced {σ : Type*} (P : MvPolynomial σ K) (b : ℕ)
    (hbound : ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → b ≤ weight (P ^ n))
    {n : ℕ} (hn : 0 < n) : b ≤ weight (P ^ n) := by
  obtain ⟨p, hpK⟩ := ExpChar.exists K
  cases hpK with
  | zero => exact hbound n hn (Nat.cast_ne_zero.mpr (ne_of_gt hn))
  | prime hp =>
    letI : ExpChar K p := ExpChar.prime hp
    obtain ⟨e, h, hnp, hfactor⟩ := Nat.exists_eq_pow_mul_and_not_dvd (ne_of_gt hn) p hp.ne_one
    have hh : 0 < h := by
      by_contra hz
      have hz' : h = 0 := by omega
      simp [hz'] at hfactor
      omega
    have hhK : (h : K) ≠ 0 := fun hz => hnp ((CharP.cast_eq_zero_iff K p h).mp hz)
    rw [hfactor, Nat.mul_comm, pow_mul, weight_pow_expChar]
    exact hbound h hh hhK

theorem bivariateQuadratic_power_three_rows (A B D : Polynomial K) (hD : D ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    weight (((pUnitAlgEquiv.{_, 0} K).symm A) ^ n) +
      weight ((n : MvPolynomial PUnit.{1} K) * (pUnitAlgEquiv.{_, 0} K).symm B *
        ((pUnitAlgEquiv.{_, 0} K).symm D) ^ (n - 1)) +
      weight (((pUnitAlgEquiv.{_, 0} K).symm D) ^ n) ≤
      weight (bivariateQuadratic A B D ^ n) := by
  classical
  let U := pUnitAlgEquiv.{_, 0} K
  let E := optionEquivLeft K PUnit.{1}
  let P := bivariateQuadratic A B D
  have hDne : U.symm D ≠ 0 := by
    intro hz
    exact hD (by simpa only [U.apply_symm_apply, map_zero] using congrArg U hz)
  have hrows := quadratic_power_rows (U.symm A) (U.symm B) (U.symm D) 1 hDne hn
  dsimp only at hrows
  simp only [map_one, mul_one] at hrows
  have hE : E (P ^ n) =
      (Polynomial.C (U.symm A) + Polynomial.C (U.symm B) * Polynomial.X +
        Polynomial.C (U.symm D) * Polynomial.X ^ 2) ^ n := by
    rw [map_pow]
    exact congrArg (fun Q => Q ^ n) (optionEquiv_bivariateQuadratic A B D)
  have hs := weight_option_slices_le (P ^ n) {0, 2 * n - 1, 2 * n}
  have hsum : weight ((E (P ^ n)).coeff 0) +
      weight ((E (P ^ n)).coeff (2 * n - 1)) +
      weight ((E (P ^ n)).coeff (2 * n)) ≤ weight (P ^ n) := by
    have h01 : 0 ≠ 2 * n - 1 := by omega
    have h02 : 0 ≠ 2 * n := by omega
    have h12 : 2 * n - 1 ≠ 2 * n := by omega
    simpa only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
      Finset.mem_singleton, h01, h02, h12, or_self, not_false_eq_true, add_assoc] using hs
  rw [hE, hrows.1, hrows.2.1, hrows.2.2] at hsum
  exact hsum

theorem bivariateQuadratic_constant_power_reduced (A B : Polynomial K) (d : K)
    (hd : d ≠ 0) (hA0 : A.coeff 0 ≠ 0) (hA1 : A.coeff 1 ≠ 0)
    (hdeg : 2 ≤ A.natDegree) {n : ℕ} (hn : 0 < n) (hnK : (n : K) ≠ 0) :
    B.support.card + 4 ≤ weight (bivariateQuadratic A B (Polynomial.C d) ^ n) := by
  classical
  let U := pUnitAlgEquiv.{_, 0} K
  let P := bivariateQuadratic A B (Polynomial.C d)
  have hD : U.symm (Polynomial.C d) = C d := by
    simp [U, pUnitAlgEquiv_symm_apply]
  have hlo : weight ((U.symm A) ^ n) ≥ 3 :=
    univariate_power_weight_three A hA0 hA1 hdeg hn hnK
  have hhi : weight ((U.symm (Polynomial.C d)) ^ n) = 1 := by
    rw [hD, ← map_pow]
    rw [weight, C_apply, support_monomial, if_neg (pow_ne_zero n hd)]
    rfl
  have hmid : weight ((n : MvPolynomial PUnit.{1} K) * U.symm B *
      (U.symm (Polynomial.C d)) ^ (n - 1)) = B.support.card := by
    rw [hD]
    have heq : (n : MvPolynomial PUnit.{1} K) * U.symm B * C d ^ (n - 1) =
        C ((n : K) * d ^ (n - 1)) * U.symm B := by
      rw [map_mul, map_pow]
      simp only [map_natCast]
      ring
    rw [heq, C_apply, weight_scalar_monomial_mul 0 (mul_ne_zero hnK (pow_ne_zero _ hd))]
    exact weight_pUnitAlgEquiv_symm B
  have hsum := bivariateQuadratic_power_three_rows A B (Polynomial.C d)
    (Polynomial.C_ne_zero.mpr hd) hn
  dsimp only [U, P] at hlo hhi hmid ⊢
  omega

theorem bivariateQuadratic_constant_power (A B : Polynomial K) (d : K)
    (hd : d ≠ 0) (hA0 : A.coeff 0 ≠ 0) (hA1 : A.coeff 1 ≠ 0)
    (hdeg : 2 ≤ A.natDegree) {n : ℕ} (hn : 0 < n) :
    B.support.card + 4 ≤ weight (bivariateQuadratic A B (Polynomial.C d) ^ n) := by
  exact weight_pow_bound_of_reduced _ _
    (fun h hh hhK => bivariateQuadratic_constant_power_reduced A B d hd hA0 hA1 hdeg hh hhK) hn

theorem bivariateQuadratic_power_seven_reduced (A B D : Polynomial K)
    (hA0 : A.coeff 0 ≠ 0) (hA1 : A.coeff 1 ≠ 0) (hdeg : 2 ≤ A.natDegree)
    (hB0 : B.coeff 0 ≠ 0) (hB1 : B.coeff 1 ≠ 0)
    (hD0 : D.coeff 0 ≠ 0) (hD1 : D.coeff 1 ≠ 0)
    {n : ℕ} (hn : 0 < n) (hnK : (n : K) ≠ 0) :
    7 ≤ weight (bivariateQuadratic A B D ^ n) := by
  let U := pUnitAlgEquiv.{_, 0} K
  have hD : D ≠ 0 := fun hz => hD0 (by rw [hz, Polynomial.coeff_zero])
  have hDne : U.symm D ≠ 0 := by
    intro hz
    exact hD (by simpa only [U.apply_symm_apply, map_zero] using congrArg U hz)
  have hlow : 3 ≤ weight ((U.symm A) ^ n) :=
    univariate_power_weight_three A hA0 hA1 hdeg hn hnK
  have hdb := distance_pUnit_symm_two B hB0 hB1
  have hdd := distance_pUnit_symm_two D hD0 hD1
  have hhigh : 2 ≤ weight ((U.symm D) ^ n) := by
    have h := hdd.trans (distance_le_weight_mul (U.symm D) ((U.symm D) ^ (n - 1))
      (pow_ne_zero _ hDne))
    rw [← pow_succ', Nat.sub_add_cancel hn] at h
    exact h
  have hmiddle : 2 ≤ weight ((n : MvPolynomial PUnit.{1} K) * U.symm B *
      (U.symm D) ^ (n - 1)) := by
    have h := hdb.trans (distance_le_weight_mul (U.symm B) ((U.symm D) ^ (n - 1))
      (pow_ne_zero _ hDne))
    have hs : weight ((n : MvPolynomial PUnit.{1} K) *
        (U.symm B * (U.symm D) ^ (n - 1))) =
        weight (U.symm B * (U.symm D) ^ (n - 1)) := by
      simpa only [← C_apply, map_natCast] using
        weight_scalar_monomial_mul (0 : PUnit.{1} →₀ ℕ) hnK (U.symm B * (U.symm D) ^ (n - 1))
    rwa [mul_assoc, hs]
  have hsum := bivariateQuadratic_power_three_rows A B D hD hn
  dsimp only [U] at hlow hhigh hmiddle
  omega

theorem bivariateQuadratic_power_seven (A B D : Polynomial K)
    (hA0 : A.coeff 0 ≠ 0) (hA1 : A.coeff 1 ≠ 0) (hdeg : 2 ≤ A.natDegree)
    (hB0 : B.coeff 0 ≠ 0) (hB1 : B.coeff 1 ≠ 0)
    (hD0 : D.coeff 0 ≠ 0) (hD1 : D.coeff 1 ≠ 0)
    {n : ℕ} (hn : 0 < n) : 7 ≤ weight (bivariateQuadratic A B D ^ n) := by
  exact weight_pow_bound_of_reduced _ _
    (fun h hh hhK => bivariateQuadratic_power_seven_reduced A B D hA0 hA1 hdeg
      hB0 hB1 hD0 hD1 hh hhK) hn

end WeightedPilz

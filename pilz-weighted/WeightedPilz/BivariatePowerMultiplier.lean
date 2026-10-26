import WeightedPilz.BivariatePower
import WeightedPilz.ReducedPowerTransfer
import WeightedPilz.ShortFreshTest
import WeightedPilz.Completion

/-! Powers of a quadratic base times an arbitrary univariate multiplier. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem exists_rename_some_of_none_zero {σ : Type*}
    (J : MvPolynomial (Option σ) K) (hJ : ∀ d ∈ J.support, d none = 0) :
    ∃ M : MvPolynomial σ K, J = rename some M := by
  let E := optionEquivLeft K σ
  have hd : (E J).natDegree ≤ 0 := by
    rw [natDegree_optionEquivLeft]
    exact degreeOf_le_iff.mpr (fun d hd => le_of_eq (hJ d hd))
  refine ⟨(E J).coeff 0, ?_⟩
  apply E.injective
  rw [optionEquivLeft_rename_some]
  exact Polynomial.eq_C_of_natDegree_le_zero hd

theorem none_zero_rename_some {σ : Type*} (M : MvPolynomial σ K) :
    ∀ d ∈ (rename some M).support, d none = 0 := by
  have hd : (rename some M).degreeOf none ≤ 0 := by
    rw [← natDegree_optionEquivLeft, optionEquivLeft_rename_some, Polynomial.natDegree_C]
  intro d hd'
  exact Nat.eq_zero_of_le_zero (degreeOf_le_iff.mp hd d hd')

theorem bivariateQuadratic_power_mul_three_rows (A B D : Polynomial K)
    (hD : D ≠ 0) (M : MvPolynomial PUnit.{1} K) {n : ℕ} (hn : 0 < n) :
    weight (((pUnitAlgEquiv.{_, 0} K).symm A) ^ n * M) +
      weight ((n : MvPolynomial PUnit.{1} K) * (pUnitAlgEquiv.{_, 0} K).symm B *
        ((pUnitAlgEquiv.{_, 0} K).symm D) ^ (n - 1) * M) +
      weight (((pUnitAlgEquiv.{_, 0} K).symm D) ^ n * M) ≤
      weight (bivariateQuadratic A B D ^ n * rename some M) := by
  classical
  let U := pUnitAlgEquiv.{_, 0} K
  let E := optionEquivLeft K PUnit.{1}
  let P := bivariateQuadratic A B D
  have hDne : U.symm D ≠ 0 := by
    intro hz
    exact hD (by simpa only [U.apply_symm_apply, map_zero] using congrArg U hz)
  have hrows := quadratic_power_rows (U.symm A) (U.symm B) (U.symm D) M hDne hn
  dsimp only at hrows
  have hE : E (P ^ n * rename some M) =
      (Polynomial.C (U.symm A) + Polynomial.C (U.symm B) * Polynomial.X +
        Polynomial.C (U.symm D) * Polynomial.X ^ 2) ^ n * Polynomial.C M := by
    rw [map_mul, map_pow, optionEquivLeft_rename_some]
    rw [show E P = _ from optionEquiv_bivariateQuadratic A B D]
  have hs := weight_option_slices_le (P ^ n * rename some M) {0, 2 * n - 1, 2 * n}
  have hsum : weight ((E (P ^ n * rename some M)).coeff 0) +
      weight ((E (P ^ n * rename some M)).coeff (2 * n - 1)) +
      weight ((E (P ^ n * rename some M)).coeff (2 * n)) ≤
      weight (P ^ n * rename some M) := by
    have h01 : 0 ≠ 2 * n - 1 := by omega
    have h02 : 0 ≠ 2 * n := by omega
    have h12 : 2 * n - 1 ≠ 2 * n := by omega
    simpa only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
      Finset.mem_singleton, h01, h02, h12, or_self, not_false_eq_true, add_assoc] using hs
  rw [hE, hrows.1, hrows.2.1, hrows.2.2] at hsum
  exact hsum

theorem bivariateQuadratic_constant_power_mul_reduced (A B : Polynomial K) (d : K)
    (hd : d ≠ 0) (hA0 : A.coeff 0 ≠ 0) (hA1 : A.coeff 1 ≠ 0)
    (hdeg : 2 ≤ A.natDegree) (hB0 : B.coeff 0 ≠ 0) (hB1 : B.coeff 1 ≠ 0)
    (M : MvPolynomial PUnit.{1} K) (hM : M ≠ 0)
    {n : ℕ} (hn : 0 < n) (hnK : (n : K) ≠ 0) :
    6 ≤ weight (bivariateQuadratic A B (Polynomial.C d) ^ n * rename some M) := by
  let U := pUnitAlgEquiv.{_, 0} K
  have hAdist := distance_pUnit_symm_two A hA0 hA1
  have hBdist := distance_pUnit_symm_two B hB0 hB1
  by_cases hMone : weight M = 1
  · rw [FreshData.weight_mul_of_weight_one _ _ (by rwa [weight_rename_some])]
    have hBweight := hBdist.trans (distance_le_weight (U.symm B))
    rw [weight_pUnitAlgEquiv_symm] at hBweight
    have h := bivariateQuadratic_constant_power A B d hd hA0 hA1 hdeg hn
    omega
  · have hMmany : 2 ≤ weight M := by
      have hpos : 0 < weight M := by
        simpa [weight, Finset.card_pos, MvPolynomial.support_nonempty] using hM
      omega
    have hAne : U.symm A ≠ 0 := by
      intro hz
      have hAz : A = 0 := by simpa only [U.apply_symm_apply, map_zero] using congrArg U hz
      exact hA0 (by rw [hAz, Polynomial.coeff_zero])
    have hD : U.symm (Polynomial.C d) = C d := by simp [U, pUnitAlgEquiv_symm_apply]
    have hlo : 2 ≤ weight ((U.symm A) ^ n * M) := by
      have h := hAdist.trans (distance_le_weight_mul (U.symm A) ((U.symm A) ^ (n - 1) * M)
        (mul_ne_zero (pow_ne_zero _ hAne) hM))
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn] at h
      exact h
    have hhi : 2 ≤ weight ((U.symm (Polynomial.C d)) ^ n * M) := by
      rw [hD, ← map_pow, C_apply, weight_scalar_monomial_mul 0 (pow_ne_zero _ hd)]
      exact hMmany
    have hmid : 2 ≤ weight ((n : MvPolynomial PUnit.{1} K) * U.symm B *
        (U.symm (Polynomial.C d)) ^ (n - 1) * M) := by
      rw [hD]
      have heq : (n : MvPolynomial PUnit.{1} K) * U.symm B * C d ^ (n - 1) * M =
          C ((n : K) * d ^ (n - 1)) * (U.symm B * M) := by
        rw [map_mul, map_pow]
        simp only [map_natCast]
        ring
      rw [heq, C_apply, weight_scalar_monomial_mul 0 (mul_ne_zero hnK (pow_ne_zero _ hd))]
      exact hBdist.trans (distance_le_weight_mul (U.symm B) M hM)
    have hsum := bivariateQuadratic_power_mul_three_rows A B (Polynomial.C d)
      (Polynomial.C_ne_zero.mpr hd) M hn
    dsimp only [U] at hlo hhi hmid
    omega

theorem bivariateQuadratic_constant_power_mul (A B : Polynomial K) (d : K)
    (hd : d ≠ 0) (hA0 : A.coeff 0 ≠ 0) (hA1 : A.coeff 1 ≠ 0)
    (hdeg : 2 ≤ A.natDegree) (hB0 : B.coeff 0 ≠ 0) (hB1 : B.coeff 1 ≠ 0)
    (M : MvPolynomial PUnit.{1} K) (hM : M ≠ 0) {n : ℕ} (hn : 0 < n) :
    6 ≤ weight (bivariateQuadratic A B (Polynomial.C d) ^ n * rename some M) := by
  let P := bivariateQuadratic A B (Polynomial.C d)
  have hP : P ≠ 0 := by
    intro hz
    have hE := congrArg (optionEquivLeft K PUnit.{1}) hz
    rw [optionEquiv_bivariateQuadratic, map_zero] at hE
    have h0 := congrArg (fun Q => Q.coeff 0) hE
    have hAz : (pUnitAlgEquiv.{_, 0} K).symm A = 0 := by simpa using h0
    have hA : A = 0 := by
      simpa only [AlgEquiv.apply_symm_apply, map_zero] using congrArg (pUnitAlgEquiv.{_, 0} K) hAz
    exact hA0 (by rw [hA, Polynomial.coeff_zero])
  refine weight_pow_mul_bound_of_reduced P hP {none} 6 ?_ hn (rename some M) ?_ ?_
  · intro h hh hhK J hJ hJZ
    obtain ⟨N, rfl⟩ := exists_rename_some_of_none_zero J (hJZ none (by simp))
    have hN : N ≠ 0 := by intro hz; simp [hz] at hJ
    exact bivariateQuadratic_constant_power_mul_reduced A B d hd hA0 hA1 hdeg hB0 hB1 N hN hh hhK
  · intro hz
    have h := congrArg (optionEquivLeft K PUnit.{1}) hz
    rw [optionEquivLeft_rename_some, map_zero] at h
    exact hM (Polynomial.C_eq_zero.mp h)
  · intro z hz
    have hz' : z = none := Set.mem_singleton_iff.mp hz
    subst z
    exact none_zero_rename_some M

theorem bivariateQuadratic_power_mul_six_reduced (A B D : Polynomial K)
    (hA0 : A.coeff 0 ≠ 0) (hA1 : A.coeff 1 ≠ 0)
    (hB0 : B.coeff 0 ≠ 0) (hB1 : B.coeff 1 ≠ 0)
    (hD0 : D.coeff 0 ≠ 0) (hD1 : D.coeff 1 ≠ 0)
    (M : MvPolynomial PUnit.{1} K) (hM : M ≠ 0)
    {n : ℕ} (hn : 0 < n) (hnK : (n : K) ≠ 0) :
    6 ≤ weight (bivariateQuadratic A B D ^ n * rename some M) := by
  let U := pUnitAlgEquiv.{_, 0} K
  have hA : A ≠ 0 := fun hz => hA0 (by rw [hz, Polynomial.coeff_zero])
  have hD : D ≠ 0 := fun hz => hD0 (by rw [hz, Polynomial.coeff_zero])
  have hAne : U.symm A ≠ 0 := by
    intro hz
    exact hA (by simpa only [U.apply_symm_apply, map_zero] using congrArg U hz)
  have hDne : U.symm D ≠ 0 := by
    intro hz
    exact hD (by simpa only [U.apply_symm_apply, map_zero] using congrArg U hz)
  have hlo : 2 ≤ weight ((U.symm A) ^ n * M) := by
    have h := (distance_pUnit_symm_two A hA0 hA1).trans
      (distance_le_weight_mul (U.symm A) ((U.symm A) ^ (n - 1) * M)
        (mul_ne_zero (pow_ne_zero _ hAne) hM))
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn] at h
    exact h
  have hhi : 2 ≤ weight ((U.symm D) ^ n * M) := by
    have h := (distance_pUnit_symm_two D hD0 hD1).trans
      (distance_le_weight_mul (U.symm D) ((U.symm D) ^ (n - 1) * M)
        (mul_ne_zero (pow_ne_zero _ hDne) hM))
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn] at h
    exact h
  have hmid : 2 ≤ weight ((n : MvPolynomial PUnit.{1} K) * U.symm B *
      (U.symm D) ^ (n - 1) * M) := by
    have h := (distance_pUnit_symm_two B hB0 hB1).trans
      (distance_le_weight_mul (U.symm B) ((U.symm D) ^ (n - 1) * M)
        (mul_ne_zero (pow_ne_zero _ hDne) hM))
    have hs : weight ((n : MvPolynomial PUnit.{1} K) *
        (U.symm B * ((U.symm D) ^ (n - 1) * M))) =
        weight (U.symm B * ((U.symm D) ^ (n - 1) * M)) := by
      simpa only [← C_apply, map_natCast] using
        weight_scalar_monomial_mul (0 : PUnit.{1} →₀ ℕ) hnK
          (U.symm B * ((U.symm D) ^ (n - 1) * M))
    simpa only [mul_assoc, hs] using h
  have hsum := bivariateQuadratic_power_mul_three_rows A B D hD M hn
  dsimp only [U] at hlo hhi hmid
  omega

theorem bivariateQuadratic_power_mul_six (A B D : Polynomial K)
    (hA0 : A.coeff 0 ≠ 0) (hA1 : A.coeff 1 ≠ 0)
    (hB0 : B.coeff 0 ≠ 0) (hB1 : B.coeff 1 ≠ 0)
    (hD0 : D.coeff 0 ≠ 0) (hD1 : D.coeff 1 ≠ 0)
    (M : MvPolynomial PUnit.{1} K) (hM : M ≠ 0) {n : ℕ} (hn : 0 < n) :
    6 ≤ weight (bivariateQuadratic A B D ^ n * rename some M) := by
  let P := bivariateQuadratic A B D
  have hP : P ≠ 0 := by
    intro hz
    have hE := congrArg (optionEquivLeft K PUnit.{1}) hz
    rw [optionEquiv_bivariateQuadratic, map_zero] at hE
    have h0 := congrArg (fun Q => Q.coeff 0) hE
    have hAz : (pUnitAlgEquiv.{_, 0} K).symm A = 0 := by simpa using h0
    have hA : A = 0 := by
      simpa only [AlgEquiv.apply_symm_apply, map_zero] using congrArg (pUnitAlgEquiv.{_, 0} K) hAz
    exact hA0 (by rw [hA, Polynomial.coeff_zero])
  refine weight_pow_mul_bound_of_reduced P hP {none} 6 ?_ hn (rename some M) ?_ ?_
  · intro h hh hhK J hJ hJZ
    obtain ⟨N, rfl⟩ := exists_rename_some_of_none_zero J (hJZ none (by simp))
    have hN : N ≠ 0 := by intro hz; simp [hz] at hJ
    exact bivariateQuadratic_power_mul_six_reduced A B D hA0 hA1 hB0 hB1 hD0 hD1 N hN hh hhK
  · intro hz
    have h := congrArg (optionEquivLeft K PUnit.{1}) hz
    rw [optionEquivLeft_rename_some, map_zero] at h
    exact hM (Polynomial.C_eq_zero.mp h)
  · intro z hz
    have hz' : z = none := Set.mem_singleton_iff.mp hz
    subst z
    exact none_zero_rename_some M

end WeightedPilz

import WeightedPilz.ResidueCorrection
import WeightedPilz.Fresh

/-! The aggregate correction for an actual fresh-variable sum. -/

noncomputable section

namespace WeightedPilz

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K] [DecidableEq σ]

theorem coordinateEquiv_self_variable (z : σ) :
    coordinateEquiv (K := K) z (X z) = Polynomial.X := by
  simp [coordinateEquiv, renameEquiv_apply, rename_X,
    Equiv.optionSubtypeNe_symm_self, optionEquivLeft_X_none]

theorem coordinateEquiv_constant_of_support (z : σ) (P : MvPolynomial σ K)
    (hP : ∀ d ∈ P.support, d z = 0) :
    coordinateEquiv z P = Polynomial.C ((coordinateEquiv z P).coeff 0) := by
  classical
  apply Polynomial.ext
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · have hz : (coordinateEquiv z P).coeff n = 0 := by
      apply Polynomial.notMem_support_iff.mp
      rw [support_coordinateEquiv]
      intro hm
      obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp hm
      exact hn (heq.symm.trans (hP d hd))
    simp [Polynomial.coeff_C, hn, hz]

theorem support_pow_zero_at (z : σ) (P : MvPolynomial σ K)
    (hP : ∀ d ∈ P.support, d z = 0) (n : ℕ) :
    ∀ d ∈ (P ^ n).support, d z = 0 := by
  classical
  induction n with
  | zero =>
    intro d hd
    have hd0 : d = 0 := by
      simpa only [pow_zero, one_def, support_monomial, if_neg one_ne_zero, Finset.mem_singleton] using hd
    simp [hd0]
  | succ n ih =>
    intro d hd
    rw [pow_succ] at hd
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hd)
    simp [Finsupp.add_apply, ih a ha, hP b hb]

namespace FreshData

/-- Each designated fresh coordinate presents `F` as a monic linear
polynomial over the ring in the remaining variables. -/
theorem coordinate_F_linear (S : FreshData σ K) (z : σ) (hz : z ∈ S.vars) :
    ∃ a : MvPolynomial {i : σ // i ≠ z} K,
      coordinateEquiv z S.F = Polynomial.X - Polynomial.C a := by
  classical
  let Q := S.C + ∑ i ∈ S.vars.erase z, (X i : MvPolynomial σ K)
  have hQ : ∀ d ∈ Q.support, d z = 0 := by
    intro d hd
    rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
    · exact S.independent z hz d hd
    · obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
      rw [support_X] at hdi
      obtain rfl := Finset.mem_singleton.mp hdi
      simp [(Finset.mem_erase.mp hi).1]
  have hF : S.F = X z + Q := by
    have hsum := Finset.sum_erase_add S.vars (fun i => (X i : MvPolynomial σ K)) hz
    dsimp [F, freshSum, Q]
    rw [← hsum]
    ring
  refine ⟨-((coordinateEquiv z Q).coeff 0), ?_⟩
  rw [hF, map_add, coordinateEquiv_self_variable,
    coordinateEquiv_constant_of_support z Q hQ]
  simp

theorem frobenius_dvd_of_fresh_support (S : FreshData σ K)
    (p e : ℕ) [ExpChar K p] (z : σ) (hz : z ∈ S.vars)
    (U : MvPolynomial σ K) (hres : ∀ d ∈ U.support, p ^ e ∣ d z)
    (hdiv : S.F ∣ U) : S.F ^ (p ^ e) ∣ U := by
  obtain ⟨a, ha⟩ := S.coordinate_F_linear z hz
  exact coordinate_frobenius_dvd p e z S.F U a ha hres hdiv

/-- The displayed correction is an actual `F^(p^e)` multiple. The
coefficient polynomials are unchanged, including their fresh-power terms. -/
theorem aggregate_correction_frobenius_dvd (S : FreshData σ K)
    (p e : ℕ) [ExpChar K p] (z : σ) (hz : z ∈ S.vars)
    {ι : Type*} (s : Finset ι) (n : ι → ℕ) (A : ι → MvPolynomial σ K)
    (hA : ∀ j ∈ s, ∀ d ∈ (A j).support, p ^ e ∣ d z)
    (hG : S.F ∣ ∑ j ∈ s, S.freshSum ^ n j * A j) :
    S.F ^ (p ^ e) ∣ ∑ j ∈ s, (-S.C) ^ n j * A j := by
  classical
  apply S.frobenius_dvd_of_fresh_support p e z hz
  · intro d hd
    obtain ⟨j, hj, hdj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hdj)
    have hcore : ∀ a ∈ (-S.C).support, a z = 0 := by
      intro a ha
      rw [support_neg] at ha
      exact S.independent z hz a ha
    have hzero := support_pow_zero_at z (-S.C) hcore (n j) a ha
    simpa only [Finsupp.add_apply, hzero, zero_add] using hA j hj b hb
  · exact aggregate_correction_dvd s n A S.C S.freshSum hG

end FreshData

end WeightedPilz

import WeightedPilz.BivariateQuadratic
import WeightedPilz.PolynomialPowerRows
import WeightedPilz.PowerGapPositive

/-! Support and weight under the equivalence with one polynomial variable. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem support_pUnitAlgEquiv_symm (P : Polynomial K) :
    ((pUnitAlgEquiv.{_, 0} K).symm P).support =
      P.support.image (Finsupp.single ()) := by
  classical
  ext d
  have hd : Finsupp.single () (d ()) = d := by
    apply Finsupp.ext
    intro u
    cases u
    simp
  constructor
  · intro hm
    refine Finset.mem_image.mpr ⟨d (), ?_, hd⟩
    apply Polynomial.mem_support_iff.mpr
    have hc := coeff_pUnitAlgEquiv ((pUnitAlgEquiv.{_, 0} K).symm P) d
    rw [AlgEquiv.apply_symm_apply] at hc
    rw [hc]
    exact mem_support_iff.mp hm
  · intro hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    apply mem_support_iff.mpr
    rw [coeff_pUnitAlgEquiv_symm]
    exact Polynomial.mem_support_iff.mp hn

theorem weight_pUnitAlgEquiv_symm (P : Polynomial K) :
    weight ((pUnitAlgEquiv.{_, 0} K).symm P) = P.support.card := by
  classical
  rw [weight, support_pUnitAlgEquiv_symm]
  apply Finset.card_image_of_injective
  intro a b hab
  simpa using congrArg (fun d : PUnit.{1} →₀ ℕ => d ()) hab

theorem univariate_power_weight_three (P : Polynomial K)
    (h0 : P.coeff 0 ≠ 0) (h1 : P.coeff 1 ≠ 0) (hdeg : 2 ≤ P.natDegree)
    {n : ℕ} (hn : 0 < n) (hnK : (n : K) ≠ 0) :
    3 ≤ weight (((pUnitAlgEquiv.{_, 0} K).symm P) ^ n) := by
  rw [← map_pow, weight_pUnitAlgEquiv_symm]
  exact polynomial_power_support_three P h0 h1 hdeg hn hnK

/-- Every positive power retains at least three terms; the power gap handles
the exponent divisible by the characteristic without perfectness assumptions. -/
theorem univariate_power_weight_three_all (P : Polynomial K)
    (h0 : P.coeff 0 ≠ 0) (h1 : P.coeff 1 ≠ 0) (hdeg : 2 ≤ P.natDegree)
    {n : ℕ} (hn : 0 < n) :
    3 ≤ weight (((pUnitAlgEquiv.{_, 0} K).symm P) ^ n) := by
  have hw : 3 ≤ weight ((pUnitAlgEquiv.{_, 0} K).symm P) := by
    simpa only [pow_one] using univariate_power_weight_three P h0 h1 hdeg
      (n := 1) (by decide) (by simp)
  have hd := distance_pUnit_symm_two P h0 h1
  have h := min_weight_distance_add_one_le_weight_pow (ringExpChar K)
    ((pUnitAlgEquiv.{_, 0} K).symm P) (by omega) hn
  omega

end WeightedPilz

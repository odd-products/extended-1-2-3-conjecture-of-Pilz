import WeightedPilz.BivariateQuadratic

/-! The quadratic distance bounds for arbitrary transcendental coefficient ratio. -/
noncomputable section
namespace WeightedPilz
open Polynomial
variable {K : Type*} [Field K]
theorem quadratic_polynomial_multiple_three_rows_of_ratio {K : Type*} [Field K]
    (A B D : K[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0)
    (hratio : Transcendental K (algebraMap K[X] (RatFunc K) A * algebraMap K[X] (RatFunc K) D / (algebraMap K[X] (RatFunc K) B) ^ 2))
    (G : Polynomial K[X]) (hG : G ≠ 0)
    (hdiv : (C A + C B * X + C D * X ^ 2 : Polynomial K[X]) ∣ G) :
    3 ≤ G.support.card := by
  let f : K[X] →+* RatFunc K := algebraMap K[X] (RatFunc K)
  have hf : Function.Injective f := RatFunc.algebraMap_injective K
  have hmap : (C (f A) + C (f B) * X + C (f D) * X ^ 2 : (RatFunc K)[X]) ∣ G.map f := by
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X] using Polynomial.map_dvd f hdiv
  have hGmap : G.map f ≠ 0 := by
    intro hz
    apply hG
    exact Polynomial.map_injective f hf (by simpa using hz)
  have h := quadratic_multiple_three_rows (f A) (f B) (f D)
    (RatFunc.algebraMap_ne_zero hA) (RatFunc.algebraMap_ne_zero hB)
    (RatFunc.algebraMap_ne_zero hD) hratio (G.map f) hGmap hmap
  rwa [Polynomial.support_map_of_injective G hf] at h

open MvPolynomial

theorem bivariateQuadratic_distance_lower_of_ratio (A B D : Polynomial K)
    (hA : A ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0)
    (hratio : Transcendental K (algebraMap K[X] (RatFunc K) A * algebraMap K[X] (RatFunc K) D / (algebraMap K[X] (RatFunc K) B) ^ 2)) :
    distance ((pUnitAlgEquiv.{_, 0} K).symm A) + distance ((pUnitAlgEquiv.{_, 0} K).symm D) + 1 ≤
      distance (bivariateQuadratic A B D) := by
  let E := optionEquivLeft K PUnit.{1}
  let U := pUnitAlgEquiv.{_, 0} K
  let P := bivariateQuadratic A B D
  let Q := E P
  have hA' : U.symm A ≠ 0 := by
    intro hz
    exact hA (by simpa only [U.apply_symm_apply, map_zero] using congrArg U hz)
  have hD' : U.symm D ≠ 0 := by
    intro hz
    exact hD (by simpa only [U.apply_symm_apply, map_zero] using congrArg U hz)
  have hq : Q = Polynomial.C (U.symm A) + Polynomial.C (U.symm B) * Polynomial.X +
      Polynomial.C (U.symm D) * Polynomial.X ^ 2 := optionEquiv_bivariateQuadratic A B D
  have hq0 : Q.coeff 0 = U.symm A := by rw [hq]; simp
  have ht : Q.natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (by rw [hq0]; exact hA'))
  have hd : Q.natDegree = 2 := by rw [hq]; compute_degree <;> first | exact hD' | decide
  have htrail : Q.trailingCoeff = U.symm A := by rw [Polynomial.trailingCoeff, ht, hq0]
  have hlead : Q.leadingCoeff = U.symm D := by rw [Polynomial.leadingCoeff, hd, hq]; simp
  have hP : P ≠ 0 := by
    intro hz
    have hQ : Q = 0 := by simp [Q, hz]
    exact hA' (by rw [← hq0, hQ, Polynomial.coeff_zero])
  have hrows : ∀ H : MvPolynomial (Option PUnit.{1}) K, H ≠ 0 →
      3 ≤ (E (P * H)).support.card := by
    intro H hH
    let G := E (P * H)
    have hG : G ≠ 0 := by
      intro hz
      exact mul_ne_zero hP hH (E.injective (hz.trans (map_zero E).symm))
    have hdiv : Q ∣ G := ⟨E H, map_mul E P H⟩
    have hmapped :
        (Polynomial.C A + Polynomial.C B * Polynomial.X +
          Polynomial.C D * Polynomial.X ^ 2 : Polynomial (Polynomial K)) ∣ G.map U.toRingHom := by
      have h := Polynomial.map_dvd U.toRingHom hdiv
      rw [hq] at h
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_C, Polynomial.map_X] at h
      change Polynomial.C (U (U.symm A)) + Polynomial.C (U (U.symm B)) * Polynomial.X +
        Polynomial.C (U (U.symm D)) * Polynomial.X ^ 2 ∣ _ at h
      simpa only [U.apply_symm_apply] using h
    have hmapne : G.map U.toRingHom ≠ 0 := by
      intro hz
      exact hG (Polynomial.map_injective U.toRingHom U.injective (by simpa using hz))
    have h := quadratic_polynomial_multiple_three_rows_of_ratio A B D hA hB hD hratio
      (G.map U.toRingHom) hmapne hmapped
    rwa [Polynomial.support_map_of_injective G U.injective] at h
  have hbound := endpoint_distance_option_of_three_rows P (show Q.natTrailingDegree < Q.natDegree by
    rw [ht, hd]; decide) hrows
  change distance Q.trailingCoeff + distance Q.leadingCoeff + 1 ≤ distance P at hbound
  rwa [htrail, hlead] at hbound

theorem bivariateQuadratic_distance_four_of_ratio (A B D : Polynomial K)
    (hA0 : A.coeff 0 ≠ 0) (hA1 : A.coeff 1 ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0)
    (hratio : Transcendental K (algebraMap K[X] (RatFunc K) A * algebraMap K[X] (RatFunc K) D / (algebraMap K[X] (RatFunc K) B) ^ 2)) :
    4 ≤ distance (bivariateQuadratic A B D) := by
  have hA : A ≠ 0 := fun hz => hA0 (by rw [hz, Polynomial.coeff_zero])
  have h := bivariateQuadratic_distance_lower_of_ratio A B D hA hB hD hratio
  have hlow := distance_pUnit_symm_two A hA0 hA1
  have hhigh : 0 < distance ((pUnitAlgEquiv.{_, 0} K).symm D) := distance_pos (by
    intro hz
    apply hD
    simpa only [AlgEquiv.apply_symm_apply, map_zero] using congrArg (pUnitAlgEquiv.{_, 0} K) hz)
  omega

end WeightedPilz
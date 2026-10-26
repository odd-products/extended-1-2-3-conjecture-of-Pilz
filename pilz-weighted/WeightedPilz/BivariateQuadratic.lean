import WeightedPilz.QuadraticRows
import WeightedPilz.RowWeights
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! Weighted bivariate quadratic bases with an extra occupied row. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem coeff_pUnitAlgEquiv (P : MvPolynomial PUnit.{1} K) (d : PUnit.{1} →₀ ℕ) :
    ((pUnitAlgEquiv.{_, 0} K) P).coeff (d ()) = coeff d P := by
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [pUnitAlgEquiv_monomial]
    have heq : s () = d () ↔ s = d := by
      constructor
      · intro h
        apply Finsupp.ext
        intro u
        cases u
        exact h
      · intro h
        exact congrArg (fun e => e ()) h
    simp only [Polynomial.coeff_monomial, coeff_monomial, heq]
  | add P Q hP hQ =>
    simp only [map_add, Polynomial.coeff_add, coeff_add, hP, hQ]

theorem coeff_pUnitAlgEquiv_symm (P : Polynomial K) (n : ℕ) :
    coeff (Finsupp.single () n) ((pUnitAlgEquiv.{_, 0} K).symm P) = P.coeff n := by
  have h := coeff_pUnitAlgEquiv ((pUnitAlgEquiv.{_, 0} K).symm P) (Finsupp.single () n)
  simpa only [AlgEquiv.apply_symm_apply, Finsupp.single_eq_same] using h.symm

theorem distance_pUnit_symm_two (P : Polynomial K) (h0 : P.coeff 0 ≠ 0)
    (h1 : P.coeff 1 ≠ 0) : 2 ≤ distance ((pUnitAlgEquiv.{_, 0} K).symm P) := by
  have hzero : coeff 0 ((pUnitAlgEquiv.{_, 0} K).symm P) ≠ 0 := by
    have h := coeff_pUnitAlgEquiv_symm P 0
    have hn : coeff (Finsupp.single () 0) ((pUnitAlgEquiv.{_, 0} K).symm P) ≠ 0 := by
      rw [h]
      exact h0
    simpa only [Finsupp.single_zero] using hn
  have hlinear : coeff (Finsupp.single () 1) ((pUnitAlgEquiv.{_, 0} K).symm P) ≠ 0 := by
    rwa [coeff_pUnitAlgEquiv_symm]
  have h := pure_endpoints_distance {()} ((pUnitAlgEquiv.{_, 0} K).symm P) hzero (by
    intro p hp
    cases p
    exact ⟨1, by decide, hlinear⟩)
  simpa using h

def bivariateQuadratic (A B D : Polynomial K) : MvPolynomial (Option PUnit.{1}) K :=
  (optionEquivLeft K PUnit.{1}).symm
    (Polynomial.C ((pUnitAlgEquiv.{_, 0} K).symm A) +
      Polynomial.C ((pUnitAlgEquiv.{_, 0} K).symm B) * Polynomial.X +
      Polynomial.C ((pUnitAlgEquiv.{_, 0} K).symm D) * Polynomial.X ^ 2)

@[simp] theorem optionEquiv_bivariateQuadratic (A B D : Polynomial K) :
    optionEquivLeft K PUnit.{1} (bivariateQuadratic A B D) =
      Polynomial.C ((pUnitAlgEquiv.{_, 0} K).symm A) +
      Polynomial.C ((pUnitAlgEquiv.{_, 0} K).symm B) * Polynomial.X +
      Polynomial.C ((pUnitAlgEquiv.{_, 0} K).symm D) * Polynomial.X ^ 2 := by
  simp [bivariateQuadratic]

theorem bivariateQuadratic_distance_lower (A B D : Polynomial K)
    (hA : A ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0)
    (hdeg : A.natDegree + D.natDegree ≠ 2 * B.natDegree) :
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
    have h := quadratic_polynomial_multiple_three_rows A B D hA hB hD hdeg
      (G.map U.toRingHom) hmapne hmapped
    rwa [Polynomial.support_map_of_injective G U.injective] at h
  have hbound := endpoint_distance_option_of_three_rows P (show Q.natTrailingDegree < Q.natDegree by
    rw [ht, hd]; decide) hrows
  change distance Q.trailingCoeff + distance Q.leadingCoeff + 1 ≤ distance P at hbound
  rwa [htrail, hlead] at hbound

theorem bivariateQuadratic_distance_four (A B D : Polynomial K)
    (hA0 : A.coeff 0 ≠ 0) (hA1 : A.coeff 1 ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0)
    (hdeg : A.natDegree + D.natDegree ≠ 2 * B.natDegree) :
    4 ≤ distance (bivariateQuadratic A B D) := by
  have hA : A ≠ 0 := fun hz => hA0 (by rw [hz, Polynomial.coeff_zero])
  have h := bivariateQuadratic_distance_lower A B D hA hB hD hdeg
  have hlow := distance_pUnit_symm_two A hA0 hA1
  have hhigh : 0 < distance ((pUnitAlgEquiv.{_, 0} K).symm D) := distance_pos (by
    intro hz
    apply hD
    simpa only [AlgEquiv.apply_symm_apply, map_zero] using congrArg (pUnitAlgEquiv.{_, 0} K) hz)
  omega

theorem bivariateQuadratic_distance_five (A B D : Polynomial K)
    (hA0 : A.coeff 0 ≠ 0) (hA1 : A.coeff 1 ≠ 0) (hB : B ≠ 0)
    (hD0 : D.coeff 0 ≠ 0) (hD1 : D.coeff 1 ≠ 0)
    (hdeg : A.natDegree + D.natDegree ≠ 2 * B.natDegree) :
    5 ≤ distance (bivariateQuadratic A B D) := by
  have hA : A ≠ 0 := fun hz => hA0 (by rw [hz, Polynomial.coeff_zero])
  have hD : D ≠ 0 := fun hz => hD0 (by rw [hz, Polynomial.coeff_zero])
  have h := bivariateQuadratic_distance_lower A B D hA hB hD hdeg
  have hlow := distance_pUnit_symm_two A hA0 hA1
  have hhigh := distance_pUnit_symm_two D hD0 hD1
  omega

end WeightedPilz

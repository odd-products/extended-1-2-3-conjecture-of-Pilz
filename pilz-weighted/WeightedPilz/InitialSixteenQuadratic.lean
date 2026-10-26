import WeightedPilz.UnivariateWeight
import WeightedPilz.SharpCompletion
import Mathlib.FieldTheory.AlgebraicClosure

/-! The constant-ratio quadratic base at sixteen, over every coefficient field. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K L : Type*} [Field K] [Field L]

theorem map_pUnitAlgEquiv_symm (f : K →+* L) (P : Polynomial K) :
    MvPolynomial.map f ((pUnitAlgEquiv.{_, 0} K).symm P) =
      (pUnitAlgEquiv.{_, 0} L).symm (P.map f) := by
  ext d
  have hd : Finsupp.single () (d ()) = d := by
    apply Finsupp.ext
    intro u
    cases u
    simp
  rw [← hd, MvPolynomial.coeff_map, coeff_pUnitAlgEquiv_symm,
    coeff_pUnitAlgEquiv_symm, Polynomial.coeff_map]

theorem optionEquivLeft_map_coefficients {σ : Type*} (f : K →+* L)
    (P : MvPolynomial (Option σ) K) :
    optionEquivLeft L σ (MvPolynomial.map f P) =
      Polynomial.map (MvPolynomial.map f) (optionEquivLeft K σ P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c => simp only [MvPolynomial.map_monomial, optionEquivLeft_monomial,
      Polynomial.map_monomial]
  | add P Q hP hQ => simp only [map_add, Polynomial.map_add, hP, hQ]

theorem map_bivariateQuadratic (f : K →+* L) (A B D : Polynomial K) :
    MvPolynomial.map f (bivariateQuadratic A B D) =
      bivariateQuadratic (A.map f) (B.map f) (D.map f) := by
  apply (optionEquivLeft L PUnit.{1}).injective
  rw [optionEquivLeft_map_coefficients, optionEquiv_bivariateQuadratic,
    optionEquiv_bivariateQuadratic]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, map_pUnitAlgEquiv_symm]

/-- A nonzero root of the constant quadratic supplies a sharp linear factor. -/
theorem scalar_square_quadratic_distance_of_root (B : Polynomial K) (a d α : K)
    (hd : d ≠ 0) (hα : α ≠ 0) (hroot : a + α + d * α ^ 2 = 0)
    (hB0 : B.coeff 0 ≠ 0) (hB1 : B.coeff 1 ≠ 0) (hBdeg : 2 ≤ B.natDegree) :
    4 ≤ distance (bivariateQuadratic (Polynomial.C a * B ^ 2) B (Polynomial.C d)) := by
  let U := pUnitAlgEquiv.{_, 0} K
  let Q := Polynomial.C (-α) * B
  let C₀ := U.symm Q
  have hQ0 : Q.coeff 0 ≠ 0 := by
    simpa only [Q, Polynomial.coeff_C_mul] using mul_ne_zero (neg_ne_zero.mpr hα) hB0
  have hQ1 : Q.coeff 1 ≠ 0 := by
    simpa only [Q, Polynomial.coeff_C_mul] using mul_ne_zero (neg_ne_zero.mpr hα) hB1
  have hQdeg : 2 ≤ Q.natDegree := by
    rw [show Q = Polynomial.C (-α) * B from rfl,
      Polynomial.natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hα))]
    exact hBdeg
  have hC₀ : C₀ ≠ 0 := by
    intro hz
    have hQ : Q = 0 := by simpa only [C₀, U.apply_symm_apply, map_zero] using congrArg U hz
    exact hQ0 (by rw [hQ, Polynomial.coeff_zero])
  have hcore : 2 ≤ distance C₀ := distance_pUnit_symm_two Q hQ0 hQ1
  have hweight : 3 ≤ weight C₀ := by
    simpa only [pow_one] using univariate_power_weight_three_all Q hQ0 hQ1 hQdeg
      (n := 1) (by decide)
  have hlinear : 4 ≤ distance (freshCompletion C₀) := by
    have h := sharp_completion_one C₀ hC₀
    omega
  let P := bivariateQuadratic (Polynomial.C a * B ^ 2) B (Polynomial.C d)
  have hP : P ≠ 0 := by
    intro hz
    have hcoeff := congrArg (fun R => (optionEquivLeft K PUnit.{1} R).coeff 2) hz
    simp only [P, optionEquiv_bivariateQuadratic, map_zero, Polynomial.coeff_zero,
      Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow] at hcoeff
    have heq : U.symm (Polynomial.C d) = 0 := by simpa using hcoeff
    have hz' : Polynomial.C d = 0 := by
      simpa only [U.apply_symm_apply, map_zero] using congrArg U heq
    exact hd (Polynomial.C_eq_zero.mp hz')
  have hdiv : freshCompletion C₀ ∣ P := by
    apply (freshCompletion_dvd_iff C₀ P).mpr
    rw [show P = bivariateQuadratic (Polynomial.C a * B ^ 2) B (Polynomial.C d) from rfl,
      optionEquiv_bivariateQuadratic]
    apply U.injective
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, map_add, map_mul, map_pow, map_neg,
      C₀, U.apply_symm_apply, Q, map_zero]
    have hroot' := congrArg (Polynomial.C : K →+* Polynomial K) hroot
    simp only [map_add, map_mul, map_pow, map_zero] at hroot'
    simp only [U, AlgEquiv.apply_symm_apply]
    linear_combination B ^ 2 * hroot'
  obtain ⟨H, hH⟩ := hdiv
  have hHne : H ≠ 0 := by intro hz; apply hP; rw [hH, hz, mul_zero]
  have hmono := distance_le_distance_mul (freshCompletion C₀) H hHne
  rw [← hH] at hmono
  exact hlinear.trans hmono

/-- The difficult constant-ratio case of the dense quartic/quadratic base. -/
theorem scalar_square_quadratic_distance_four (B : Polynomial K) (a d : K)
    (ha : a ≠ 0) (hd : d ≠ 0)
    (hB0 : B.coeff 0 ≠ 0) (hB1 : B.coeff 1 ≠ 0) (hBdeg : 2 ≤ B.natDegree) :
    4 ≤ distance (bivariateQuadratic (Polynomial.C a * B ^ 2) B (Polynomial.C d)) := by
  let F := AlgebraicClosure K
  let f : K →+* F := algebraMap K F
  have hf : Function.Injective f := f.injective
  have ha' : f a ≠ 0 := (map_ne_zero f).mpr ha
  have hd' : f d ≠ 0 := (map_ne_zero f).mpr hd
  let q : Polynomial F := Polynomial.C (f a) + Polynomial.X +
    Polynomial.C (f d) * Polynomial.X ^ 2
  have hdeg : q.natDegree = 2 := by
    simpa only [q, map_one, one_mul] using quadratic_natDegree (f a) 1 (f d) hd'
  have hq : q ≠ 0 := by intro hz; simp [hz] at hdeg
  have hdeg' : q.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hq, hdeg]
    decide
  obtain ⟨α, hαroot⟩ := IsAlgClosed.exists_root q hdeg'
  have hroot : f a + α + f d * α ^ 2 = 0 := by
    simpa only [Polynomial.IsRoot, q, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] using hαroot
  have hα : α ≠ 0 := by intro hz; simp [hz] at hroot; exact ha hroot
  have hB0' : (B.map f).coeff 0 ≠ 0 := by rw [Polynomial.coeff_map]; exact (map_ne_zero f).mpr hB0
  have hB1' : (B.map f).coeff 1 ≠ 0 := by rw [Polynomial.coeff_map]; exact (map_ne_zero f).mpr hB1
  have hBdeg' : 2 ≤ (B.map f).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective hf]
    exact hBdeg
  have hbound := scalar_square_quadratic_distance_of_root (B.map f) (f a) (f d) α
    hd' hα hroot hB0' hB1' hBdeg'
  have hmap : MvPolynomial.map f
      (bivariateQuadratic (Polynomial.C a * B ^ 2) B (Polynomial.C d)) =
      bivariateQuadratic (Polynomial.C (f a) * B.map f ^ 2) (B.map f) (Polynomial.C (f d)) := by
    rw [map_bivariateQuadratic]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C]
  rwa [← hmap, distance_map f] at hbound

end WeightedPilz

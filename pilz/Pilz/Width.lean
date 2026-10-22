import Pilz.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Logic.Equiv.Option
import Lean.Elab.Tactic.Omega

/-!
# Coordinate orders and widths

The paper's `ord_x`, `deg_x`, and `width_x` are realized by viewing one
variable as the univariate polynomial variable and all remaining variables
as coefficients. Both endpoint degrees add under multiplication because
the coefficient ring is an integral domain.
-/

noncomputable section

namespace Pilz

open MvPolynomial
open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

/-- Separate one variable from the remaining variables. -/
def coordinateEquiv (p : σ) :
    MvPolynomial σ (ZMod 2) ≃ₐ[ZMod 2]
      Polynomial (MvPolynomial {q : σ // q ≠ p} (ZMod 2)) :=
  (renameEquiv (ZMod 2) (Equiv.optionSubtypeNe p).symm).trans
    (optionEquivLeft (ZMod 2) {q : σ // q ≠ p})

omit [DecidableEq σ] in
private theorem support_optionEquivLeft
    (P : MvPolynomial (Option σ) (ZMod 2)) :
    (optionEquivLeft (ZMod 2) σ P).support = P.support.image (fun d => d none) := by
  classical
  ext n
  constructor
  · intro hn
    have hc : (optionEquivLeft (ZMod 2) σ P).coeff n ≠ 0 :=
      Polynomial.mem_support_iff.mp hn
    obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr hc
    let d : Option σ →₀ ℕ := s.embDomain .some + Finsupp.single none n
    have hnone : d none = n := by simp [d]
    have hsome : d.some = s := by ext i; simp [d]
    refine Finset.mem_image.mpr ⟨d, ?_, hnone⟩
    apply MvPolynomial.mem_support_iff.mpr
    have hcoeff := optionEquivLeft_coeff_coeff (ZMod 2) σ d P
    rw [hnone, hsome] at hcoeff
    exact hcoeff ▸ MvPolynomial.mem_support_iff.mp hs
  · intro hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    apply Polynomial.mem_support_iff.mpr
    intro hz
    have hcoeff := optionEquivLeft_coeff_coeff (ZMod 2) σ d P
    rw [hz, coeff_zero] at hcoeff
    exact MvPolynomial.mem_support_iff.mp hd hcoeff.symm

/-- The occupied coordinate degrees are precisely the exponents that occur
in the original support; grouping the other variables loses no terms. -/
theorem support_coordinateEquiv (p : σ) (P : MvPolynomial σ (ZMod 2)) :
    (coordinateEquiv p P).support = P.support.image (fun d => d p) := by
  classical
  unfold coordinateEquiv
  rw [AlgEquiv.trans_apply, support_optionEquivLeft, renameEquiv_apply,
    support_rename_of_injective (Equiv.optionSubtypeNe p).symm.injective,
    Finset.image_image]
  apply Finset.image_congr
  intro d hd
  change d.mapDomain (Equiv.optionSubtypeNe p).symm none = d p
  rw [← Equiv.optionSubtypeNe_symm_self p, Finsupp.mapDomain_apply]
  exact (Equiv.optionSubtypeNe p).symm.injective

theorem coordinateEquiv_ne_zero (p : σ) {P : MvPolynomial σ (ZMod 2)} (hP : P ≠ 0) :
    coordinateEquiv p P ≠ 0 := by
  simpa using hP

/-- The greatest exponent is the usual multivariate coordinate degree. -/
theorem natDegree_coordinateEquiv (p : σ) (P : MvPolynomial σ (ZMod 2)) :
    (coordinateEquiv p P).natDegree = P.degreeOf p := by
  unfold coordinateEquiv
  rw [AlgEquiv.trans_apply, natDegree_optionEquivLeft, renameEquiv_apply]
  have h := degreeOf_rename_of_injective
    (p := P) (Equiv.optionSubtypeNe p).symm.injective p
  simpa only [Equiv.optionSubtypeNe_symm_self] using h

/-- The least occurring exponent. Its value at the zero polynomial is zero. -/
def orderOf (p : σ) (P : MvPolynomial σ (ZMod 2)) : ℕ :=
  (coordinateEquiv p P).natTrailingDegree

/-- Greatest exponent minus least exponent, as in the paper. -/
def widthOf (p : σ) (P : MvPolynomial σ (ZMod 2)) : ℕ :=
  P.degreeOf p - orderOf p P

/-- Width in a chosen finite set of base variables. Fresh variables are omitted. -/
def totalWidth (B : Finset σ) (P : MvPolynomial σ (ZMod 2)) : ℕ :=
  ∑ p ∈ B, widthOf p P

theorem orderOf_le_support (p : σ) {P : MvPolynomial σ (ZMod 2)}
    {d : σ →₀ ℕ} (hd : d ∈ P.support) : orderOf p P ≤ d p := by
  apply Polynomial.natTrailingDegree_le_of_mem_supp
  rw [support_coordinateEquiv]
  exact Finset.mem_image.mpr ⟨d, hd, rfl⟩

theorem exists_support_orderOf (p : σ) {P : MvPolynomial σ (ZMod 2)} (hP : P ≠ 0) :
    ∃ d ∈ P.support, d p = orderOf p P := by
  have hm := Polynomial.natTrailingDegree_mem_support_of_nonzero
    (coordinateEquiv_ne_zero p hP)
  rw [support_coordinateEquiv] at hm
  exact Finset.mem_image.mp hm

theorem orderOf_eq_inf_support (p : σ) {P : MvPolynomial σ (ZMod 2)} (hP : P ≠ 0) :
    orderOf p P = P.support.inf' (MvPolynomial.support_nonempty.mpr hP) (fun d => d p) := by
  apply le_antisymm
  · exact Finset.le_inf' _ _ (fun d hd => orderOf_le_support p hd)
  · obtain ⟨d, hd, heq⟩ := exists_support_orderOf p hP
    exact heq ▸ Finset.inf'_le (fun d : σ →₀ ℕ => d p) hd

theorem orderOf_le_degreeOf (p : σ) (P : MvPolynomial σ (ZMod 2)) :
    orderOf p P ≤ P.degreeOf p := by
  rw [← natDegree_coordinateEquiv p P]
  exact Polynomial.natTrailingDegree_le_natDegree _

theorem degreeOf_mul (p : σ) {P Q : MvPolynomial σ (ZMod 2)}
    (hP : P ≠ 0) (hQ : Q ≠ 0) : (P * Q).degreeOf p = P.degreeOf p + Q.degreeOf p := by
  rw [← natDegree_coordinateEquiv p (P * Q), map_mul,
    Polynomial.natDegree_mul (coordinateEquiv_ne_zero p hP) (coordinateEquiv_ne_zero p hQ),
    natDegree_coordinateEquiv, natDegree_coordinateEquiv]

theorem orderOf_mul (p : σ) {P Q : MvPolynomial σ (ZMod 2)}
    (hP : P ≠ 0) (hQ : Q ≠ 0) : orderOf p (P * Q) = orderOf p P + orderOf p Q := by
  unfold orderOf
  rw [map_mul, Polynomial.natTrailingDegree_mul
    (coordinateEquiv_ne_zero p hP) (coordinateEquiv_ne_zero p hQ)]

/-- The width-addition identity used throughout square-root descent. -/
theorem widthOf_mul (p : σ) {P Q : MvPolynomial σ (ZMod 2)}
    (hP : P ≠ 0) (hQ : Q ≠ 0) : widthOf p (P * Q) = widthOf p P + widthOf p Q := by
  have hp := orderOf_le_degreeOf p P
  have hq := orderOf_le_degreeOf p Q
  simp only [widthOf, degreeOf_mul p hP hQ, orderOf_mul p hP hQ]
  omega

theorem widthOf_mono_support (p : σ) {P Q : MvPolynomial σ (ZMod 2)}
    (hP : P ≠ 0) (hPQ : P.support ⊆ Q.support) : widthOf p P ≤ widthOf p Q := by
  obtain ⟨d, hd, horder⟩ := exists_support_orderOf p hP
  have hord : orderOf p Q ≤ orderOf p P := horder ▸ orderOf_le_support p (hPQ hd)
  have hdeg : P.degreeOf p ≤ Q.degreeOf p := by
    rw [degreeOf_le_iff]
    intro d hd
    exact monomial_le_degreeOf p (hPQ hd)
  unfold widthOf
  omega

theorem totalWidth_mul (B : Finset σ) {P Q : MvPolynomial σ (ZMod 2)}
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    totalWidth B (P * Q) = totalWidth B P + totalWidth B Q := by
  simp only [totalWidth, widthOf_mul _ hP hQ, Finset.sum_add_distrib]

theorem totalWidth_mono_support (B : Finset σ) {P Q : MvPolynomial σ (ZMod 2)}
    (hP : P ≠ 0) (hPQ : P.support ⊆ Q.support) : totalWidth B P ≤ totalWidth B Q := by
  exact Finset.sum_le_sum (fun p hp => widthOf_mono_support p hP hPQ)

/-- It suffices to preserve coordinate exponents, even when the other
coordinates change (as happens on taking a fresh-variable derivative). -/
theorem widthOf_mono_exponents (p : σ) {P Q : MvPolynomial σ (ZMod 2)}
    (hP : P ≠ 0)
    (hPQ : ∀ d ∈ P.support, ∃ e ∈ Q.support, d p = e p) :
    widthOf p P ≤ widthOf p Q := by
  obtain ⟨d, hd, horder⟩ := exists_support_orderOf p hP
  obtain ⟨e, he, hcoord⟩ := hPQ d hd
  have hord : orderOf p Q ≤ orderOf p P := by
    rw [← horder, hcoord]
    exact orderOf_le_support p he
  have hdeg : P.degreeOf p ≤ Q.degreeOf p := by
    rw [degreeOf_le_iff]
    intro d hd
    obtain ⟨e, he, hcoord⟩ := hPQ d hd
    rw [hcoord]
    exact monomial_le_degreeOf p he
  unfold widthOf
  omega

@[simp] theorem widthOf_monomial (p : σ) (d : σ →₀ ℕ) {c : ZMod 2} (hc : c ≠ 0) :
    widthOf p (monomial d c) = 0 := by
  classical
  have hm : (monomial d c : MvPolynomial σ (ZMod 2)) ≠ 0 := by
    simpa only [ne_eq, monomial_eq_zero] using hc
  have hord : orderOf p (monomial d c) = d p := by
    rw [orderOf_eq_inf_support p hm]
    simp [support_monomial, hc]
  simp only [widthOf, degreeOf_monomial_eq d p hc, hord, Nat.sub_self]

@[simp] theorem widthOf_monomial_mul (p : σ) (d : σ →₀ ℕ)
    {P : MvPolynomial σ (ZMod 2)} (hP : P ≠ 0) :
    widthOf p (monomial d 1 * P) = widthOf p P := by
  have hm : (monomial d 1 : MvPolynomial σ (ZMod 2)) ≠ 0 := by simp
  rw [widthOf_mul p hm hP, widthOf_monomial p d one_ne_zero, zero_add]

theorem widthOf_square (p : σ) {P : MvPolynomial σ (ZMod 2)} (hP : P ≠ 0) :
    widthOf p (P ^ 2) = 2 * widthOf p P := by
  rw [pow_two, widthOf_mul p hP hP]
  omega

theorem totalWidth_square (B : Finset σ) {P : MvPolynomial σ (ZMod 2)} (hP : P ≠ 0) :
    totalWidth B (P ^ 2) = 2 * totalWidth B P := by
  rw [pow_two, totalWidth_mul B hP hP]
  omega

end Pilz

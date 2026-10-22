import Pilz.Basic
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Maps that isolate one multivariate polynomial variable

The map `asUnivariate z` regards the variable `z` as the univariate variable,
while retaining every other variable in the coefficient ring. Evaluation at
the original variable retracts this map. Independence is stated directly on
support exponents, as in the manuscript.
-/

noncomputable section

namespace Pilz

/-- Every support exponent of `P` is zero in coordinate `z`. -/
def IndependentOf (P : Poly) (z : ℕ) : Prop :=
  ∀ d ∈ P.support, d z = 0

theorem notMem_vars_of_independent {P : Poly} {z : ℕ}
    (hP : IndependentOf P z) : z ∉ P.vars := by
  intro hz
  obtain ⟨d, hd, hz⟩ := (MvPolynomial.mem_vars z).mp hz
  exact (Finsupp.mem_support_iff.mp hz) (hP d hd)

/-- Homomorphisms agreeing away from an unused variable agree on `P`. -/
theorem hom_eq_of_independent {S : Type*} [CommSemiring S]
    (f g : Poly →+* S) (z : ℕ) (P : Poly) (hP : IndependentOf P z)
    (hC : ∀ c : ZMod 2, f (MvPolynomial.C c) = g (MvPolynomial.C c))
    (hX : ∀ i : ℕ, i ≠ z → f (MvPolynomial.X i) = g (MvPolynomial.X i)) :
    f P = g P := by
  apply MvPolynomial.hom_congr_vars (p₁ := P) (p₂ := P) ?_ ?_ rfl
  · exact RingHom.ext hC
  · intro i hi _
    apply hX i
    intro hiz
    subst i
    exact notMem_vars_of_independent hP hi

/-- Regard `z` as the univariate variable over the original coefficient ring. -/
def asUnivariate (z : ℕ) : Poly →+* Polynomial Poly :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => if i = z then Polynomial.X else Polynomial.C (MvPolynomial.X i))

@[simp] theorem asUnivariate_C (z : ℕ) (c : ZMod 2) :
    asUnivariate z (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
  simp [asUnivariate]

@[simp] theorem asUnivariate_X (z i : ℕ) :
    asUnivariate z (MvPolynomial.X i) =
      if i = z then Polynomial.X else Polynomial.C (MvPolynomial.X i) := by
  simp [asUnivariate]

/-- Evaluating the isolated variable at its original value is a retraction. -/
theorem eval_comp_asUnivariate (z : ℕ) :
    (Polynomial.evalRingHom (MvPolynomial.X z)).comp (asUnivariate z) =
      RingHom.id Poly := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    by_cases hi : i = z <;> simp [hi]

theorem eval_asUnivariate (z : ℕ) (P : Poly) :
    Polynomial.eval (MvPolynomial.X z) (asUnivariate z P) = P := by
  exact RingHom.congr_fun (eval_comp_asUnivariate z) P

/-- An independent polynomial becomes a constant under variable isolation. -/
theorem asUnivariate_of_independent (z : ℕ) (P : Poly)
    (hP : IndependentOf P z) : asUnivariate z P = Polynomial.C P := by
  apply hom_eq_of_independent (asUnivariate z) Polynomial.C z P hP
  · intro c
    simp
  · intro i hi
    simp [hi]

end Pilz

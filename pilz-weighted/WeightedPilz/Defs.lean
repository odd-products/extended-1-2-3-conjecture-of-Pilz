import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
Basic interfaces for the frozen weighted manuscript (23 October 2026).
Natural variable names permit `Nat.factorization` as the exponent encoding.
Encoded positive integers use only prime variables; arbitrary multipliers may
also use other variables. No restriction on the coefficient field is imposed.
-/

namespace WeightedPilz

open scoped BigOperators

abbrev Poly (K : Type*) [CommSemiring K] := MvPolynomial ℕ K
abbrev Laurent (K : Type*) [Semiring K] := AddMonoidAlgebra K (ℕ →₀ ℤ)

/-- Number of nonzero monomials, including weight zero for the zero polynomial. -/
def weight {σ R : Type*} [CommSemiring R] (P : MvPolynomial σ R) : ℕ :=
  P.support.card

/-- The valuation monomial. Arithmetic assertions require a positive input. -/
noncomputable def monomialOf {K : Type*} [CommSemiring K] (a : ℕ) : Poly K :=
  MvPolynomial.monomial a.factorization 1

/-- A polynomial on a finite integer support with arbitrary specified weights. -/
noncomputable def polynomialOf {K : Type*} [CommSemiring K]
    (A : Finset ℕ) (c : ℕ → K) : Poly K :=
  ∑ a ∈ A, MvPolynomial.monomial a.factorization (c a)

/-- The weighted interval polynomial from `thm:field`. -/
noncomputable def interval {K : Type*} [CommSemiring K] (n : ℕ) (c : ℕ → K) : Poly K :=
  polynomialOf (Finset.Icc 1 n) c

/-- The nonvanishing hypothesis applies precisely to the interval's weights. -/
def NonzeroWeights {K : Type*} [Zero K] (n : ℕ) (c : ℕ → K) : Prop :=
  ∀ a ∈ Finset.Icc 1 n, c a ≠ 0

/-- The requested field bound at a fixed interval and weight function. -/
def IntervalBound {K : Type*} [Field K] (n : ℕ) (c : ℕ → K) : Prop :=
  ∀ H : Poly K, H ≠ 0 → n ≤ weight (interval n c * H)

end WeightedPilz

import Pilz.Minimal
import Pilz.PrimeCounts

/-! Precise paper statements used by the final assembly. -/

namespace Pilz

/-- Some support monomial has positive exponent in the indicated variable. -/
def VariableOccurs (D : Poly) (p : ℕ) : Prop :=
  ∃ d ∈ D.support, 0 < d p

/-- Every variable has minimum exponent zero on the support. -/
def Normalized (D : Poly) : Prop :=
  ∀ p : ℕ, ∃ d ∈ D.support, d p = 0

/-- A largest occurring prime, as in the localized-support theorem. -/
def LargestPrime (D : Poly) (q : ℕ) : Prop :=
  Nat.Prime q ∧ VariableOccurs D q ∧
    ∀ p : ℕ, VariableOccurs D p → Nat.Prime p ∧ p ≤ q

/-- A multiplier using only prime variables at most `n/2`. -/
def FreshPrimeBounded (n : ℕ) (D : Poly) : Prop :=
  ∀ p : ℕ, VariableOccurs D p → Nat.Prime p ∧ p ≤ n / 2

/-- The interval consequence of the fresh-variable elimination theorem.
The threshold is part of the hypothesis, rather than an assumed fact. -/
def IntervalFreshElimination (n : ℕ) : Prop :=
  2 ≤ n → Nat.sqrt n ≤ freshCount n →
  ∀ H : Poly, H ≠ 0 → weight (interval n * H) < n →
    ∃ D : Poly, D ≠ 0 ∧ weight (interval n * D) < n ∧ FreshPrimeBounded n D

/-- Normalize a counterexample, make it minimal under deletion, and select
its largest occurring prime. Proved by `counterexamplePreparation`. -/
def CounterexamplePreparation (n : ℕ) : Prop :=
  ∀ H : Poly, H ≠ 0 → weight (interval n * H) < n → FreshPrimeBounded n H →
    ∃ (D : Poly) (q : ℕ), D ≠ 0 ∧ weight (interval n * D) < n ∧
      FreshPrimeBounded n D ∧ Normalized D ∧ DeletionMinimal n D ∧ LargestPrime D q

/-- The prime-bound consequence of the directed-cut lemma. -/
def DirectedCutAt (n : ℕ) : Prop :=
  ∀ (D : Poly) (q : ℕ), D ≠ 0 → weight (interval n * D) < n →
    Normalized D → DeletionMinimal n D → LargestPrime D q →
      q < 2 * (weight D - 1)

/-- Theorem `thm:localized-intro`, specialized to F2. -/
def LocalizedExpansionAt (n : ℕ) : Prop :=
  ∀ (D : Poly) (q : ℕ), D ≠ 0 → Normalized D → LargestPrime D q →
    q ≤ n / 2 → q < 2 * (weight D - 1) → n ≤ weight (interval n * D)

end Pilz

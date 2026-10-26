import WeightedPilz.FieldTheorem
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring

/-!
# Sharp scope of the weighted interval theorem

The universal interval bound is equivalent to nonvanishing of every interval
coefficient. The complete integer interval cannot be replaced by an arbitrary
collection of equally many monomials: over `ZMod 2`, three terms can multiply
to two terms.
-/

noncomputable section
namespace WeightedPilz

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- With zero coefficients allowed, the interval weight counts exactly the
nonzero coefficients. -/
theorem weight_interval_eq_nonzero_card {K : Type*} [CommSemiring K]
    (n : ℕ) (c : ℕ → K) :
    weight (interval n c) = ((Finset.Icc 1 n).filter (fun a => c a ≠ 0)).card := by
  classical
  have hp : polynomialOf ((Finset.Icc 1 n).filter (fun a => c a ≠ 0)) c =
      interval n c := by
    simp only [interval, polynomialOf]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a ha hna
    have hc : c a = 0 := by simpa [Finset.mem_filter, ha] using hna
    simp [hc]
  rw [← hp]
  apply weight_polynomialOf
  · intro a ha
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

/-- All interval coefficients being nonzero is both sufficient and necessary
for the universal support lower bound, including the vacuous case `n = 0`. -/
theorem intervalBound_iff_nonzeroWeights {K : Type*} [Field K]
    (n : ℕ) (c : ℕ → K) : IntervalBound n c ↔ NonzeroWeights n c := by
  classical
  constructor
  · intro h
    have hb : n ≤ weight (interval n c) := by
      simpa using h 1 one_ne_zero
    rw [weight_interval_eq_nonzero_card] at hb
    have hcard : (Finset.Icc 1 n).card = n := by simp
    have heq : ((Finset.Icc 1 n).filter (fun a => c a ≠ 0)).card =
        (Finset.Icc 1 n).card := by
      apply Nat.le_antisymm (Finset.card_filter_le _ _)
      simpa [hcard] using hb
    exact Finset.card_filter_eq_iff.mp heq
  · exact intervalBound_all n c

/-- The elementary characteristic-two cancellation behind the noninterval
counterexample, written in one of the natural-number-indexed variables. -/
theorem noninterval_binary_product :
    ((1 + MvPolynomial.X 0 + MvPolynomial.X 0 ^ 2) : Poly (ZMod 2)) *
      (1 + MvPolynomial.X 0) = 1 + MvPolynomial.X 0 ^ 3 := by
  let x : Poly (ZMod 2) := MvPolynomial.X 0
  change (1 + x + x ^ 2) * (1 + x) = 1 + x ^ 3
  calc
    (1 + x + x ^ 2) * (1 + x) = 1 + x ^ 3 + (x + x) + (x ^ 2 + x ^ 2) := by ring
    _ = _ := by simp only [CharTwo.add_self_eq_zero, add_zero]

private theorem noninterval_binary_support_one :
    (1 : Poly (ZMod 2)).support = {0} := by
  simpa using (MvPolynomial.support_X_pow (R := ZMod 2) (0 : ℕ) 0)

private theorem noninterval_binary_binomial_support (a : ℕ) (ha : a ≠ 0) :
    ((1 + MvPolynomial.X 0 ^ a) : Poly (ZMod 2)).support =
      {0, Finsupp.single 0 a} := by
  classical
  have hd : Disjoint (1 : Poly (ZMod 2)).support
      ((MvPolynomial.X 0 ^ a) : Poly (ZMod 2)).support := by
    simp [noninterval_binary_support_one, MvPolynomial.support_X_pow, ha]
  have heq : ((1 + MvPolynomial.X 0 ^ a) : Poly (ZMod 2)).support =
      (1 : Poly (ZMod 2)).support ∪ ((MvPolynomial.X 0 ^ a) : Poly (ZMod 2)).support :=
    Finsupp.support_add_eq hd
  ext d
  simp [heq, noninterval_binary_support_one, MvPolynomial.support_X_pow, or_comm]

private theorem noninterval_binary_support (a b : ℕ) (ha : a ≠ 0)
    (hb : b ≠ 0) (hab : a ≠ b) :
    ((1 + MvPolynomial.X 0 ^ a + MvPolynomial.X 0 ^ b) : Poly (ZMod 2)).support =
      {0, Finsupp.single 0 a, Finsupp.single 0 b} := by
  classical
  have hab' : (Finsupp.single 0 a : ℕ →₀ ℕ) ≠ Finsupp.single 0 b := by
    intro h
    exact hab (Finsupp.single_injective 0 h)
  have h1 : ((1 + MvPolynomial.X 0 ^ a) : Poly (ZMod 2)).support =
      {0, Finsupp.single 0 a} := by
    exact noninterval_binary_binomial_support a ha
  have hd : Disjoint ((1 + MvPolynomial.X 0 ^ a) : Poly (ZMod 2)).support
      ((MvPolynomial.X 0 ^ b) : Poly (ZMod 2)).support := by
    simp [h1, MvPolynomial.support_X_pow, hb, Ne.symm hab']
  have heq : ((1 + MvPolynomial.X 0 ^ a + MvPolynomial.X 0 ^ b) : Poly (ZMod 2)).support =
      ((1 + MvPolynomial.X 0 ^ a) : Poly (ZMod 2)).support ∪
        ((MvPolynomial.X 0 ^ b) : Poly (ZMod 2)).support := Finsupp.support_add_eq hd
  ext d
  simp [heq, h1, MvPolynomial.support_X_pow, or_comm, or_left_comm, or_assoc]

/-- Three nonzero monomials can have a nonzero multiplier giving only two
output monomials, so cardinality alone does not replace the interval structure. -/
theorem noninterval_binary_counterexample :
    let P : Poly (ZMod 2) := 1 + MvPolynomial.X 0 + MvPolynomial.X 0 ^ 2
    let H : Poly (ZMod 2) := 1 + MvPolynomial.X 0
    weight P = 3 ∧ H ≠ 0 ∧ weight (P * H) = 2 := by
  classical
  dsimp
  have hP : weight ((1 + MvPolynomial.X 0 + MvPolynomial.X 0 ^ 2) : Poly (ZMod 2)) =
      3 := by
    have hp := noninterval_binary_support 1 2 (by decide) (by decide) (by decide)
    simp only [pow_one] at hp
    rw [weight, hp]
    have h12 : (Finsupp.single 0 1 : ℕ →₀ ℕ) ≠ Finsupp.single 0 2 :=
      (Finsupp.single_injective 0).ne (by decide)
    simp [h12, Finsupp.single_eq_zero, eq_comm]
  have hH : weight ((1 + MvPolynomial.X 0) : Poly (ZMod 2)) = 2 := by
    simpa [weight, eq_comm] using
      congrArg Finset.card (noninterval_binary_binomial_support 1 (by decide))
  refine ⟨hP, ?_, ?_⟩
  · intro h
    simp [h] at hH
  · rw [noninterval_binary_product, weight, noninterval_binary_binomial_support 3 (by decide)]
    simp [eq_comm]

end WeightedPilz

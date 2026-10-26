import WeightedPilz.ResidueCapacity
import WeightedPilz.WidthDescent
import Mathlib.Algebra.Ring.Parity

/-!
# Residue cancellation after strict width descent

This file joins the actual Frobenius extraction to full residue capacities.
The geometric compression and the displayed disjoint fresh-sector
decomposition remain explicit hypotheses of this interface.
-/

noncomputable section

namespace WeightedPilz

open MvPolynomial
open scoped BigOperators

local instance residueDescentDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Support

variable {σ R : Type*} [CommSemiring R]

theorem support_add_disjoint_of_disjoint (U B T : MvPolynomial σ R)
    (hU : Disjoint U.support T.support) (hB : Disjoint B.support T.support) :
    Disjoint (U + B).support T.support := by
  apply Finset.disjoint_left.mpr
  intro d hd hT
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact Finset.disjoint_left.mp hU h hT
  · exact Finset.disjoint_left.mp hB h hT

/-- The precise capacity inequalities with the nonzero fresh-residue sector
included. The second inequality includes its exact cost `weight T`. -/
theorem residue_descent_capacity (q N : ℕ) (U B T : MvPolynomial σ R)
    (hUT : Disjoint U.support T.support) (hBT : Disjoint B.support T.support)
    (hcost : ∀ α ∈ residueIndices q U, N ≤ residueWeight q U α) :
    weight (B + T) + (residueIndices q U).card * N ≤
        weight (U + B + T) + 2 * ∑ α ∈ residueIndices q U, residueWeight q B α ∧
      (∑ α ∈ residueIndices q U, (N - residueWeight q B α)) + weight T ≤
        weight (U + B + T) := by
  obtain ⟨hfirst, hsecond⟩ := residue_correction_capacity q N U B hcost
  rw [weight_add_of_disjoint B T hBT,
    weight_add_of_disjoint (U + B) T (support_add_disjoint_of_disjoint U B T hUT hBT)]
  constructor <;> omega

theorem residue_descent_uniform_capacity (q N M : ℕ) (U B T : MvPolynomial σ R)
    (hUT : Disjoint U.support T.support) (hBT : Disjoint B.support T.support)
    (hcost : ∀ α ∈ residueIndices q U, N ≤ residueWeight q U α)
    (hcap : ∀ α ∈ residueIndices q U, residueWeight q B α ≤ M) :
    weight (B + T) + (residueIndices q U).card * N ≤
        weight (U + B + T) + 2 * (residueIndices q U).card * M ∧
      (residueIndices q U).card * (N - M) + weight T ≤ weight (U + B + T) := by
  obtain ⟨hfirst, hsecond⟩ := residue_correction_uniform_capacity q N M U B hcost hcap
  rw [weight_add_of_disjoint B T hBT,
    weight_add_of_disjoint (U + B) T (support_add_disjoint_of_disjoint U B T hUT hBT)]
  constructor <;> omega

/-- A class whose comparison capacity is at most the nonconstant fresh cost
cannot occur in a counterexample below `N`. -/
theorem protected_residue_class (q N : ℕ) (U B T : MvPolynomial σ R)
    (α : σ →₀ ℕ)
    (hUT : Disjoint U.support T.support) (hBT : Disjoint B.support T.support)
    (hcost : residuePart q U α ≠ 0 → N ≤ residueWeight q U α)
    (hshort : weight (U + B + T) < N)
    (hcap : residueWeight q B α ≤ weight T) : residuePart q U α = 0 := by
  by_contra hne
  have hc := hcost hne
  have ht := residueWeight_le_add q U B α
  have hw := weight_residuePart_le q (U + B) α
  have heq := weight_add_of_disjoint (U + B) T
    (support_add_disjoint_of_disjoint U B T hUT hBT)
  change residueWeight q (U + B) α ≤ weight (U + B) at hw
  omega

theorem correction_eq_zero_of_capacity (q N : ℕ) (U B T : MvPolynomial σ R)
    (hUT : Disjoint U.support T.support) (hBT : Disjoint B.support T.support)
    (hcost : ∀ α ∈ residueIndices q U, N ≤ residueWeight q U α)
    (hshort : weight (U + B + T) < N)
    (hcap : ∀ α ∈ residueIndices q U, residueWeight q B α ≤ weight T) : U = 0 := by
  by_contra hne
  obtain ⟨α, hα⟩ := exists_nonzero_residuePart q U hne
  have hm := mem_residueIndices_of_part_ne_zero q U hα
  exact hα (protected_residue_class q N U B T α hUT hBT
    (fun _ => hcost α hm) hshort (hcap α hm))

end Support

section Comparison

variable {σ R : Type*} [CommRing R]

@[simp] theorem residueWeight_neg (q : ℕ) (P : MvPolynomial σ R) (α : σ →₀ ℕ) :
    residueWeight q (-P) α = residueWeight q P α := by
  have heq : residuePart q (-P) α = -residuePart q P α := by
    apply MvPolynomial.ext
    intro d
    simp only [coeff_residuePart, MvPolynomial.coeff_neg]
    split_ifs <;> simp
  simp only [residueWeight, heq, weight, MvPolynomial.support_neg]

@[simp] theorem residueSigma_neg (q : ℕ) (P : MvPolynomial σ R) :
    residueSigma q (-P) = residueSigma q P := by
  have heq : residueWeight q (-P) = residueWeight q P := funext (residueWeight_neg q P)
  simp only [residueSigma, residueIndices, MvPolynomial.support_neg, heq]

theorem residueSigma_neg_pow (q j : ℕ) (C : MvPolynomial σ R) :
    residueSigma q ((-C) ^ j) = residueSigma q (C ^ j) := by
  rcases Nat.even_or_odd j with hj | hj
  · rw [hj.neg_pow]
  · rw [hj.neg_pow, residueSigma_neg]

/-- The displayed manuscript capacity, with the coefficient polynomials
fixed during replacement. -/
theorem aggregate_comparison_capacity (q : ℕ) (s : Finset ℕ)
    (C : MvPolynomial σ R) (A : ℕ → MvPolynomial σ R) (α : σ →₀ ℕ) :
    residueWeight q (-(∑ j ∈ s, (-C) ^ j * A j)) α ≤
      ∑ j ∈ s, residueSigma q (C ^ j) * weight (A j) := by
  rw [residueWeight_neg]
  simpa only [residueSigma_neg_pow] using
    residueWeight_sum_mul_le q s (fun j => (-C) ^ j) A α

end Comparison

section Width

variable {σ K : Type*} [Field K] [DecidableEq σ]

/-- Every support exponent of the correction lies in the interval obtained
from the coefficient rows of `G`, enlarged upwards by `(q-1) deg C`. -/
theorem aggregate_correction_support_bounds (q : ℕ) (s : Finset ℕ)
    (C G : MvPolynomial σ K) (A : ℕ → MvPolynomial σ K) (i : σ)
    (hindex : ∀ j ∈ s, j < q)
    (hA : ∀ j ∈ s, ∀ b ∈ (A j).support, ∃ d ∈ G.support, b i = d i) :
    ∀ d ∈ (∑ j ∈ s, (-C) ^ j * A j).support,
      orderOf i G ≤ d i ∧ d i ≤ G.degreeOf i + (q - 1) * C.degreeOf i := by
  intro d hd
  obtain ⟨j, hj, hdj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hdj)
  obtain ⟨d, hd, hcoord⟩ := hA j hj b hb
  have hlo : orderOf i G ≤ b i := hcoord ▸ orderOf_le_support i hd
  have hhi : b i ≤ G.degreeOf i := hcoord ▸ MvPolynomial.monomial_le_degreeOf i hd
  have haBound : a i ≤ j * C.degreeOf i := by
    apply (MvPolynomial.monomial_le_degreeOf i ha).trans
    simpa only [MvPolynomial.degreeOf_neg] using MvPolynomial.degreeOf_pow_le i (-C) j
  have hjbound : j ≤ q - 1 := by have := hindex j hj; omega
  have hmul := Nat.mul_le_mul_right (C.degreeOf i) hjbound
  simp only [Finsupp.add_apply]
  constructor <;> omega

theorem aggregate_correction_exponent_bounds (q : ℕ) (s : Finset ℕ)
    (C G : MvPolynomial σ K) (A : ℕ → MvPolynomial σ K) (i : σ)
    (hindex : ∀ j ∈ s, j < q)
    (hA : ∀ j ∈ s, ∀ b ∈ (A j).support, ∃ d ∈ G.support, b i = d i)
    (hU : (∑ j ∈ s, (-C) ^ j * A j) ≠ 0) :
    orderOf i G ≤ orderOf i (∑ j ∈ s, (-C) ^ j * A j) ∧
      (∑ j ∈ s, (-C) ^ j * A j).degreeOf i ≤
        G.degreeOf i + (q - 1) * C.degreeOf i := by
  have hb := aggregate_correction_support_bounds q s C G A i hindex hA
  constructor
  · obtain ⟨d, hd, heq⟩ := exists_support_orderOf i hU
    exact heq ▸ (hb d hd).1
  · rw [MvPolynomial.degreeOf_le_iff]
    exact fun d hd => (hb d hd).2

/-- Each occupied class of the actual correction polynomial has the target
weight. The lower bound is obtained by extracting a smaller-width multiple. -/
theorem correction_residue_cost (p e : ℕ) [ExpChar K p] (hq : 1 < p ^ e)
    (base : Finset σ) (P H E : MvPolynomial σ K) (N : ℕ)
    (hP : P ≠ 0) (hH : H ≠ 0) (hpos : 0 < totalWidth base H)
    (hmin : ∀ J : MvPolynomial σ K, J ≠ 0 → totalWidth base J < totalWidth base H →
      N ≤ weight (P * J))
    (hwidth : ∀ i ∈ base, widthOf i (P ^ p ^ e * E) ≤
      widthOf i (P * H) + (p ^ e - 1) * widthOf i P) :
    ∀ α ∈ residueIndices (p ^ e) (P ^ p ^ e * E),
      N ≤ residueWeight (p ^ e) (P ^ p ^ e * E) α := by
  intro α hα
  exact correction_residue_bound_of_minimal_width p e hq base P H E α N hP hH hpos hmin
    (residuePart_ne_zero_of_mem_indices (p ^ e) _ hα) hwidth

/-- The manuscript's two uniform residue bounds for an actual correction
`P^(p^e) E`, using strict width descent rather than a postulated class cost. -/
theorem frobenius_residue_descent_capacity (p e : ℕ) [ExpChar K p]
    (hq : 1 < p ^ e) (base : Finset σ) (P H E B T : MvPolynomial σ K) (N M : ℕ)
    (hP : P ≠ 0) (hH : H ≠ 0) (hpos : 0 < totalWidth base H)
    (hmin : ∀ J : MvPolynomial σ K, J ≠ 0 → totalWidth base J < totalWidth base H →
      N ≤ weight (P * J))
    (hwidth : ∀ i ∈ base, widthOf i (P ^ p ^ e * E) ≤
      widthOf i (P * H) + (p ^ e - 1) * widthOf i P)
    (hG : P * H = P ^ p ^ e * E + B + T)
    (hUT : Disjoint (P ^ p ^ e * E).support T.support)
    (hBT : Disjoint B.support T.support)
    (hcap : ∀ α ∈ residueIndices (p ^ e) (P ^ p ^ e * E),
      residueWeight (p ^ e) B α ≤ M) :
    weight (B + T) + (residueIndices (p ^ e) (P ^ p ^ e * E)).card * N ≤
        weight (P * H) + 2 * (residueIndices (p ^ e) (P ^ p ^ e * E)).card * M ∧
      (residueIndices (p ^ e) (P ^ p ^ e * E)).card * (N - M) + weight T ≤ weight (P * H) := by
  rw [hG]
  exact residue_descent_uniform_capacity (p ^ e) N M _ B T hUT hBT
    (correction_residue_cost p e hq base P H E N hP hH hpos hmin hwidth) hcap

theorem frobenius_correction_eq_zero_of_capacity (p e : ℕ) [ExpChar K p]
    (hq : 1 < p ^ e) (base : Finset σ) (P H E B T : MvPolynomial σ K) (N : ℕ)
    (hP : P ≠ 0) (hH : H ≠ 0) (hpos : 0 < totalWidth base H)
    (hmin : ∀ J : MvPolynomial σ K, J ≠ 0 → totalWidth base J < totalWidth base H →
      N ≤ weight (P * J))
    (hwidth : ∀ i ∈ base, widthOf i (P ^ p ^ e * E) ≤
      widthOf i (P * H) + (p ^ e - 1) * widthOf i P)
    (hG : P * H = P ^ p ^ e * E + B + T)
    (hUT : Disjoint (P ^ p ^ e * E).support T.support)
    (hBT : Disjoint B.support T.support)
    (hshort : weight (P * H) < N)
    (hcap : ∀ α ∈ residueIndices (p ^ e) (P ^ p ^ e * E),
      residueWeight (p ^ e) B α ≤ weight T) : P ^ p ^ e * E = 0 := by
  apply correction_eq_zero_of_capacity (p ^ e) N _ B T hUT hBT
    (correction_residue_cost p e hq base P H E N hP hH hpos hmin hwidth)
  · rwa [← hG]
  · exact hcap

end Width

end WeightedPilz

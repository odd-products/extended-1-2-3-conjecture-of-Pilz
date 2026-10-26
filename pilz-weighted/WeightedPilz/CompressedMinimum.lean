import WeightedPilz.ScalarCompression
import WeightedPilz.WidthZero
import WeightedPilz.FreshResidueWidth
import WeightedPilz.AggregateResidueGrouping

/-! Choose and compress a positive minimum-width counterexample. -/

noncomputable section

namespace WeightedPilz

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K] [DecidableEq σ]

namespace FreshData

/-- The characteristic-free scalar form of the positive minimum-width
selection, retaining the original base-only aggregate coefficients. -/
theorem exists_positive_scalar_minimum (S : FreshData σ K) (base : Finset σ)
    (hCB : S.C.vars ⊆ base) (hBV : Disjoint base S.vars)
    (N : ℕ) (hN : N ≤ weight S.C + S.vars.card)
    (hcounter : ∃ H : MvPolynomial σ K, H ≠ 0 ∧ weight (S.F * H) < N) :
    ∃ (H : MvPolynomial σ K) (T : Finset ℕ) (B : ℕ → MvPolynomial σ K),
      H ≠ 0 ∧ weight (S.F * H) < N ∧ 0 < totalWidth base H ∧
      (∀ J : MvPolynomial σ K, J ≠ 0 → totalWidth base J < totalWidth base H →
        N ≤ weight (S.F * J)) ∧
      (∀ n, S.BaseOnly (B n)) ∧ S.F * H = ∑ n ∈ T, B n * S.freshSum ^ n := by
  classical
  have hzero : ∀ H : MvPolynomial σ K, H ≠ 0 → totalWidth base H = 0 →
      N ≤ weight (S.F * H) := by
    intro H hH hw
    exact hN.trans (S.weight_mul_of_totalWidth_zero base hCB hBV H hH hw)
  obtain ⟨H, hH, hshort, hpos, hmin⟩ :=
    exists_positive_minimal_width_counterexample base S.F N hzero hcounter
  have hind : ∀ i ∈ S.vars, i ∉ S.C.vars := by
    intro i hi himem
    obtain ⟨d, hd, hdi⟩ := (MvPolynomial.mem_vars i).mp himem
    exact (Finsupp.mem_support_iff.mp hdi) (S.independent i hi d hd)
  obtain ⟨J, hJ, hweight, hwidth, T, B, hBvars, hcomp⟩ :=
    Compression.scalar_support_compression_multiplier S.vars S.nonempty S.C hind H
      (mul_ne_zero S.F_ne_zero hH)
  change weight (S.F * J) ≤ weight (S.F * H) at hweight
  change (∀ i ∉ S.vars, widthOf i (S.F * J) ≤ widthOf i (S.F * H)) at hwidth
  change S.F * J = ∑ n ∈ T, B n * S.freshSum ^ n at hcomp
  have htotal : totalWidth base (S.F * J) ≤ totalWidth base (S.F * H) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hwidth i (fun his => Finset.disjoint_left.mp hBV hi his)
  have hsame := minimal_width_preserved_by_compression base S.F H J N S.F_ne_zero hH hJ
    hshort hmin hweight htotal
  refine ⟨J, T, B, hJ, hweight.trans_lt hshort, ?_, ?_, ?_, hcomp⟩
  · rwa [hsame]
  · intro D hD hsmall
    apply hmin D hD
    rwa [← hsame]
  · intro n z hz d hd
    exact MvPolynomial.mem_support_notMem_vars_zero hd (hBvars n z hz)

theorem exists_positive_compressed_minimum (S : FreshData σ K)
    (p : ℕ) [ExpChar K p] (base : Finset σ)
    (hCB : S.C.vars ⊆ base) (hBV : Disjoint base S.vars)
    (N : ℕ) (hN : N ≤ weight S.C + S.vars.card)
    (hcounter : ∃ H : MvPolynomial σ K, H ≠ 0 ∧ weight (S.F * H) < N) :
    ∃ (H : MvPolynomial σ K) (A : ℕ → MvPolynomial σ K),
      H ≠ 0 ∧ weight (S.F * H) < N ∧ 0 < totalWidth base H ∧
      (∀ J : MvPolynomial σ K, J ≠ 0 → totalWidth base J < totalWidth base H →
        N ≤ weight (S.F * J)) ∧
      S.F * H = ∑ j ∈ Finset.range p, S.freshSum ^ j * A j ∧
      (∀ j < p, S.PowersInFresh p (A j)) := by
  classical
  have hzero : ∀ H : MvPolynomial σ K, H ≠ 0 → totalWidth base H = 0 →
      N ≤ weight (S.F * H) := by
    intro H hH hw
    exact hN.trans (S.weight_mul_of_totalWidth_zero base hCB hBV H hH hw)
  obtain ⟨H, hH, hshort, hpos, hmin⟩ :=
    exists_positive_minimal_width_counterexample base S.F N hzero hcounter
  have hind : ∀ i ∈ S.vars, i ∉ S.C.vars := by
    intro i hi himem
    obtain ⟨d, hd, hdi⟩ := (MvPolynomial.mem_vars i).mp himem
    exact (Finsupp.mem_support_iff.mp hdi) (S.independent i hi d hd)
  obtain ⟨J, hJ, hweight, hwidth, s, B, hBvars, hcomp⟩ :=
    Compression.scalar_support_compression_multiplier S.vars S.nonempty S.C hind H
      (mul_ne_zero S.F_ne_zero hH)
  change weight (S.F * J) ≤ weight (S.F * H) at hweight
  change (∀ i ∉ S.vars, widthOf i (S.F * J) ≤ widthOf i (S.F * H)) at hwidth
  change S.F * J = ∑ n ∈ s, B n * S.freshSum ^ n at hcomp
  have htotal : totalWidth base (S.F * J) ≤ totalWidth base (S.F * H) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hwidth i (fun his => Finset.disjoint_left.mp hBV hi his)
  have hsame := minimal_width_preserved_by_compression base S.F H J N S.F_ne_zero hH hJ
    hshort hmin hweight htotal
  have hBbase : ∀ n ∈ s, S.BaseOnly (B n) := by
    intro n hn z hz d hd
    exact MvPolynomial.mem_support_notMem_vars_zero hd (hBvars n z hz)
  obtain ⟨A, hA, hgroup⟩ := S.exists_aggregate_residue_grouping p s B hBbase
  refine ⟨J, A, hJ, hweight.trans_lt hshort, ?_, ?_, hcomp.trans hgroup, hA⟩
  · rwa [hsame]
  · intro D hD hsmall
    apply hmin D hD
    rwa [← hsame]

end FreshData

end WeightedPilz

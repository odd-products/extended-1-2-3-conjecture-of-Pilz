import WeightedPilz.FreshResidueWidth
import WeightedPilz.VariableSlices

/-! Remove fresh-power coefficients from a zero aggregate correction. -/

noncomputable section

namespace WeightedPilz

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K] [DecidableEq σ]

namespace FreshData

theorem baseOnly_vars_subset (S : FreshData σ K) (P : MvPolynomial σ K)
    (hP : S.BaseOnly P) : (P.vars : Set σ) ⊆ {i | i ∉ S.vars} := by
  intro i hi his
  obtain ⟨d, hd, hdi⟩ := (MvPolynomial.mem_vars i).mp hi
  exact (Finsupp.mem_support_iff.mp hdi) (hP i his d hd)

theorem baseOnly_powersInFresh (S : FreshData σ K) (p : ℕ) (P : MvPolynomial σ K)
    (hP : S.BaseOnly P) : S.PowersInFresh p P := by
  intro z hz d hd
  rw [hP z hz d hd]
  exact dvd_zero p

theorem aggregate_nonzero_of_nonzero_row (S : FreshData σ K) (p : ℕ)
    (A : ℕ → MvPolynomial σ K) (hA : ∀ j < p, S.PowersInFresh p (A j))
    (hne : ∃ j < p, A j ≠ 0) : (∑ j ∈ Finset.range p, S.freshSum ^ j * A j) ≠ 0 := by
  obtain ⟨j, hj, hAj⟩ := hne
  have hrow : S.freshSum ^ j * A j ≠ 0 := mul_ne_zero (pow_ne_zero j S.freshSum_ne_zero) hAj
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hrow
  apply MvPolynomial.support_nonempty.mp
  exact ⟨d, S.aggregate_row_mem_support p A hA hj hd⟩

theorem exists_nonzero_aggregate_row (S : FreshData σ K) (p : ℕ)
    (A : ℕ → MvPolynomial σ K)
    (hG : (∑ j ∈ Finset.range p, S.freshSum ^ j * A j) ≠ 0) :
    ∃ j < p, A j ≠ 0 := by
  by_contra h
  push_neg at h
  apply hG
  apply Finset.sum_eq_zero
  intro j hj
  rw [h j (Finset.mem_range.mp hj), mul_zero]

/-- Select one common fresh-variable exponent slice from all coefficients.
The zero correction relation survives, at least one row survives, and no
individual coefficient weight increases. -/
theorem exists_base_rows_of_zero_correction (S : FreshData σ K) (p : ℕ)
    (A : ℕ → MvPolynomial σ K) (hne : ∃ j < p, A j ≠ 0)
    (hzero : (∑ j ∈ Finset.range p, (-S.C) ^ j * A j) = 0) :
    ∃ B : ℕ → MvPolynomial σ K,
      (∀ j, S.BaseOnly (B j)) ∧ (∃ j < p, B j ≠ 0) ∧
      (∑ j ∈ Finset.range p, (-S.C) ^ j * B j) = 0 ∧
      (∀ j, weight (B j) ≤ weight (A j)) := by
  classical
  obtain ⟨j₀, hj₀, hAj₀⟩ := hne
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hAj₀
  let T : Set σ := {i | i ∉ S.vars}
  let β := outsideExponent T d
  have hβ : outsideExponent T β = β := outsideExponent_idempotent T d
  have hex : ∀ j, ∃ B : MvPolynomial σ K,
      outsideSlice T β (A j) = monomial β 1 * B ∧ (B.vars : Set σ) ⊆ T := by
    intro j
    exact outsideSlice_division T β hβ (A j)
  choose B hfactor hvars using hex
  have hbase : ∀ j, S.BaseOnly (B j) := by
    intro j z hz e he
    apply MvPolynomial.mem_support_notMem_vars_zero he
    intro hzvar
    exact hvars j hzvar hz
  have hnonzero : B j₀ ≠ 0 := by
    intro hBzero
    have hmem : d ∈ (outsideSlice T β (A j₀)).support := by
      rw [support_outsideSlice]
      exact Finset.mem_filter.mpr ⟨hd, rfl⟩
    rw [hfactor j₀, hBzero, mul_zero] at hmem
    simpa using hmem
  have hcore : (S.C.vars : Set σ) ⊆ T := S.baseOnly_vars_subset S.C S.independent
  have hcorepow : ∀ j, (((-S.C) ^ j).vars : Set σ) ⊆ T := by
    intro j i hi
    apply hcore
    have hi' := MvPolynomial.vars_pow (-S.C) j hi
    simpa only [MvPolynomial.vars_neg] using hi'
  have hrelation : monomial β 1 * (∑ j ∈ Finset.range p, (-S.C) ^ j * B j) = 0 := by
    calc
      _ = ∑ j ∈ Finset.range p, (-S.C) ^ j * outsideSlice T β (A j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hfactor j]
        ring
      _ = outsideSlice T β (∑ j ∈ Finset.range p, (-S.C) ^ j * A j) := by
        rw [outsideSlice_sum]
        apply Finset.sum_congr rfl
        intro j hj
        exact (outsideSlice_mul T β ((-S.C) ^ j) (A j) (hcorepow j)).symm
      _ = 0 := by
        rw [hzero]
        apply MvPolynomial.ext
        intro e
        simp [coeff_outsideSlice]
  have hmon : (monomial β 1 : MvPolynomial σ K) ≠ 0 := by simp
  refine ⟨B, hbase, ⟨j₀, hj₀, hnonzero⟩, (mul_eq_zero.mp hrelation).resolve_left hmon, ?_⟩
  intro j
  have hwt := weight_outsideSlice_le T β (A j)
  rwa [hfactor j, weight_monomial_mul] at hwt

end FreshData

end WeightedPilz

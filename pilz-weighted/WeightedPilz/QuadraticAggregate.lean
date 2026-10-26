import WeightedPilz.AggregateAlgebra

/-! Exact division of a quadratic aggregate multiple by the fresh linear factor. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [DecidableEq σ] [Field K]
namespace FreshData

/-- Vanishing of the higher scalar rows gives an actual affine cofactor. -/
theorem affine_cofactor_of_quadratic_rows (S : FreshData σ K)
    (t : Finset ℕ) (A : ℕ → MvPolynomial σ K)
    (hA : ∀ j ∈ t, S.BaseOnly (A j))
    (hhigher : ∀ j ∈ t, 3 ≤ j → A j = 0)
    (hne : (∑ j ∈ t, S.freshSum ^ j * A j) ≠ 0)
    (hdiv : S.F ∣ ∑ j ∈ t, S.freshSum ^ j * A j) :
    ∃ D B : MvPolynomial σ K, S.BaseOnly D ∧ S.BaseOnly B ∧
      D + S.freshSum * B ≠ 0 ∧
      (∑ j ∈ t, S.freshSum ^ j * A j) = S.F * (D + S.freshSum * B) := by
  classical
  let a : ℕ → MvPolynomial σ K := fun j => if j ∈ t then A j else 0
  have ha : ∀ j, S.BaseOnly (a j) := by
    intro j
    by_cases hj : j ∈ t
    · simpa only [a, if_pos hj] using hA j hj
    · intro z hz d hd
      simp only [a, if_neg hj, support_zero, Finset.notMem_empty] at hd
  have hsum : (∑ j ∈ t, S.freshSum ^ j * A j) =
      ∑ j ∈ Finset.range 3, S.freshSum ^ j * a j := by
    have heq : t.filter (· < 3) = (Finset.range 3).filter (· ∈ t) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      tauto
    calc
      _ = ∑ j ∈ t.filter (· < 3), S.freshSum ^ j * A j := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j hj hjnot
        have hj3 : 3 ≤ j := by
          have : ¬ j < 3 := fun h => hjnot (Finset.mem_filter.mpr ⟨hj, h⟩)
          omega
        rw [hhigher j hj hj3, mul_zero]
      _ = _ := by
        rw [heq, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjt : j ∈ t <;> simp [a, hjt]
  have hrel := S.aggregate_relation_of_dvd (Finset.range 3) a (fun j _ => ha j) (hsum ▸ hdiv)
  have hrelsimple : a 0 - S.C * a 1 + S.C ^ 2 * a 2 = 0 := by
    simpa [Finset.sum_range_succ, sub_eq_add_neg] using hrel
  have hpoly : (∑ j ∈ t, S.freshSum ^ j * A j) =
      S.F * ((a 1 - S.C * a 2) + S.freshSum * a 2) := by
    rw [hsum]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, one_mul, pow_one]
    dsimp only [F]
    linear_combination hrelsimple
  refine ⟨a 1 - S.C * a 2, a 2, (ha 1).sub (BaseOnly.mul S.independent (ha 2)), ha 2, ?_, hpoly⟩
  intro hz
  apply hne
  rw [hpoly, hz, mul_zero]

/-- Each excessive degree would by itself exhaust the permitted output budget. -/
theorem higher_rows_zero_of_short (S : FreshData σ K) (N : ℕ)
    (t : Finset ℕ) (A : ℕ → MvPolynomial σ K)
    (hA : ∀ j ∈ t, S.BaseOnly (A j))
    (hshort : weight (∑ j ∈ t, S.freshSum ^ j * A j) < N)
    (hcost : ∀ j ∈ t, 3 ≤ j → A j ≠ 0 → N ≤ weight (S.freshSum ^ j * A j)) :
    ∀ j ∈ t, 3 ≤ j → A j = 0 := by
  intro j hj hj3
  by_contra hne
  have hlow := hcost j hj hj3 hne
  have hrow : weight (S.freshSum ^ j * A j) ≤
      weight (∑ k ∈ t, S.freshSum ^ k * A k) := by
    rw [S.base_rows_weight t A hA]
    exact Finset.single_le_sum (f := fun k => weight (S.freshSum ^ k * A k))
      (fun _ _ => Nat.zero_le _) hj
  omega

/-- Characteristic zero: any hypothetical short multiple has an affine
representative once cubic-and-higher fresh costs exceed its target. -/
theorem affine_counterexample_charZero [CharZero K] (S : FreshData σ K) (N : ℕ)
    (hdegree : ∀ j, 3 ≤ j → N ≤ (S.vars.card + j - 1).choose j)
    (hcounter : ∃ H : MvPolynomial σ K, H ≠ 0 ∧ weight (S.F * H) < N) :
    ∃ D B : MvPolynomial σ K, S.BaseOnly D ∧ S.BaseOnly B ∧
      D + S.freshSum * B ≠ 0 ∧ weight (S.F * (D + S.freshSum * B)) < N := by
  obtain ⟨H, hH, hshort⟩ := hcounter
  obtain ⟨t, A, hA, hne, hdiv, hmin⟩ := S.exists_scalar_minimum
  have hGshort : weight (∑ j ∈ t, S.freshSum ^ j * A j) < N := by
    rw [hmin]
    exact (distance_le_weight_mul S.F H hH).trans_lt hshort
  have hhigh := S.higher_rows_zero_of_short N t A hA hGshort (by
    intro j hj hj3 hne
    rw [S.weight_base_row_charZero j (A j) (hA j hj)]
    exact (hdegree j hj3).trans (Nat.le_mul_of_pos_right _ (weight_pos hne)))
  obtain ⟨D, B, hDb, hBb, hDB, hfactor⟩ :=
    S.affine_cofactor_of_quadratic_rows t A hA hhigh hne hdiv
  exact ⟨D, B, hDb, hBb, hDB, hfactor ▸ hGshort⟩

end FreshData
end WeightedPilz

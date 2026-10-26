import WeightedPilz.Arithmetic.AggregateBudgets
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! Exact sparse configurations of a short middle-interval aggregate output
after reserving the nonzero constant row. -/

namespace WeightedPilz.Arithmetic
open scoped BigOperators

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem sparse_budget_checked :
    ∀ n ∈ Finset.Icc 25 66, ∀ j ∈ Finset.Icc 3 5,
      endpoint n + aggregateCost n j < n →
      n ≤ endpoint n + 2 * aggregateCost n j ∧
      ∀ k ∈ Finset.Icc 1 5, k ≠ j →
        if j = 3 ∧ n ≤ 28 ∧ k = 1 then
          n ≤ endpoint n + aggregateCost n j + 2 * aggregateCost n k
        else n ≤ endpoint n + aggregateCost n j + aggregateCost n k := by
  unfold aggregateCost
  weighted_decide

private theorem cost_pair_le (n : ℕ) (t : Finset ℕ) (u : ℕ → ℕ)
    (i j : ℕ) (hi : i ∈ t) (hj : j ∈ t) (hij : i ≠ j) :
    aggregateCost n i * u i + aggregateCost n j * u j ≤
      ∑ k ∈ t, aggregateCost n k * u k := by
  have hs : ({i, j} : Finset ℕ) ⊆ t := by
    intro k hk
    rcases (show k = i ∨ k = j from by simpa using hk) with rfl | rfl
    · exact hi
    · exact hj
  have h := Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun k _ _ => Nat.zero_le (aggregateCost n k * u k))
  simpa [hij] using h

private theorem cost_triple_le (n : ℕ) (t : Finset ℕ) (u : ℕ → ℕ)
    (j k : ℕ) (h0 : 0 ∈ t) (hj : j ∈ t) (hk : k ∈ t)
    (hj0 : j ≠ 0) (hk0 : k ≠ 0) (hjk : j ≠ k) :
    u 0 + aggregateCost n j * u j + aggregateCost n k * u k ≤
      ∑ l ∈ t, aggregateCost n l * u l := by
  have hs : ({0, j, k} : Finset ℕ) ⊆ t := by
    intro l hl
    rcases (show l = 0 ∨ l = j ∨ l = k from by simpa using hl) with rfl | rfl | rfl
    · exact h0
    · exact hj
    · exact hk
  have h := Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun l _ _ => Nat.zero_le (aggregateCost n l * u l))
  simpa [hj0, hk0, hjk, Ne.symm hj0, Ne.symm hk0, aggregateCost, add_assoc] using h

/-- Every occupied output degree at least three has one of the six listed
indices and a monomial coefficient. At most one linear coefficient can remain
in the cubic cases at 26, 27, and 28; all other positive rows vanish. -/
theorem sparse_higher_rows {n : ℕ} (hn : 25 ≤ n) (hn' : n ≤ 66)
    (t : Finset ℕ) (u : ℕ → ℕ) (h0 : 0 ∈ t) (hu0 : endpoint n ≤ u 0)
    (hshort : (∑ k ∈ t, aggregateCost n k * u k) < n)
    (j : ℕ) (hj : j ∈ t) (hj3 : 3 ≤ j) (huj : 0 < u j) :
    (n, j) ∈ ({(26, 3), (27, 3), (27, 4), (28, 3), (28, 4), (40, 3)} : Finset (ℕ × ℕ)) ∧
    u j = 1 ∧ ∀ k ∈ t, k ≠ 0 → k ≠ j →
      (j = 3 ∧ n ≤ 28 ∧ k = 1 ∧ u k ≤ 1) ∨ u k = 0 := by
  have hj0 : j ≠ 0 := by omega
  have hpair := cost_pair_le n t u 0 j h0 hj hj0.symm
  have hcost0 : aggregateCost n 0 = 1 := by simp [aggregateCost]
  rw [hcost0, one_mul] at hpair
  have hju : aggregateCost n j ≤ aggregateCost n j * u j :=
    Nat.le_mul_of_pos_right _ huj
  have hjcost : endpoint n + aggregateCost n j < n := by omega
  have hj6 : j < 6 := by
    by_contra h
    have := middle_higher_degree_cutoff hn hn' (by omega : 6 ≤ j)
    omega
  have hexc : (n, j) ∈ ({(26, 3), (27, 3), (27, 4), (28, 3), (28, 4), (40, 3)} : Finset (ℕ × ℕ)) := by
    rw [← higher_degree_exceptions]
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hn, hn'⟩, Finset.mem_Icc.mpr ⟨hj3, by omega⟩⟩, hjcost⟩
  obtain ⟨hdouble, hothers⟩ := sparse_budget_checked n (Finset.mem_Icc.mpr ⟨hn, hn'⟩)
    j (Finset.mem_Icc.mpr ⟨hj3, by omega⟩) hjcost
  have huj1 : u j = 1 := by
    by_contra hne
    have ht : 2 ≤ u j := by omega
    have hm := Nat.mul_le_mul_left (aggregateCost n j) ht
    nlinarith
  refine ⟨hexc, huj1, ?_⟩
  intro k hk hk0 hkj
  by_cases huk : u k = 0
  · exact Or.inr huk
  have hukpos : 0 < u k := Nat.pos_of_ne_zero huk
  have hkcost : aggregateCost n k ≤ aggregateCost n k * u k :=
    Nat.le_mul_of_pos_right _ hukpos
  have htriple := cost_triple_le n t u j k h0 hj hk hj0 hk0 hkj.symm
  rw [huj1, mul_one] at htriple
  have hk6 : k < 6 := by
    by_contra h
    have := middle_higher_degree_cutoff hn hn' (by omega : 6 ≤ k)
    omega
  have hother := hothers k (Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hk0, by omega⟩) hkj
  by_cases hallowed : j = 3 ∧ n ≤ 28 ∧ k = 1
  · rw [if_pos hallowed] at hother
    refine Or.inl ⟨hallowed.1, hallowed.2.1, hallowed.2.2, ?_⟩
    by_contra hnot
    have ht : 2 ≤ u k := by omega
    have hm := Nat.mul_le_mul_left (aggregateCost n k) ht
    nlinarith
  · rw [if_neg hallowed] at hother
    omega

end WeightedPilz.Arithmetic

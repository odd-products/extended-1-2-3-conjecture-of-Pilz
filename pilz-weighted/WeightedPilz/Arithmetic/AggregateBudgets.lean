import WeightedPilz.Arithmetic.MiddleBudgets

/-! Monotonicity extends the finite higher-degree certificates to every degree. -/

namespace WeightedPilz.Arithmetic

theorem aggregateCost_eq_fixed_choose {n : ℕ} (hr : 1 ≤ freshCount n) (j : ℕ) :
    aggregateCost n j = Nat.choose (freshCount n + j - 1) (freshCount n - 1) := by
  unfold aggregateCost
  exact Nat.choose_symm_of_eq_add (by omega)

theorem aggregateCost_mono_degree {n a b : ℕ} (hr : 1 ≤ freshCount n) (hab : a ≤ b) :
    aggregateCost n a ≤ aggregateCost n b := by
  rw [aggregateCost_eq_fixed_choose hr, aggregateCost_eq_fixed_choose hr]
  exact Nat.choose_le_choose _ (by omega)

theorem aggregateCost_one (n : ℕ) : aggregateCost n 1 = freshCount n := by
  simp [aggregateCost]

theorem freshCount_le_aggregateCost {n j : ℕ} (hr : 1 ≤ freshCount n) (hj : 1 ≤ j) :
    freshCount n ≤ aggregateCost n j := by
  rw [← aggregateCost_one n]
  exact aggregateCost_mono_degree hr hj

theorem aggregateCost_two (n : ℕ) : aggregateCost n 2 = squareCost n := by
  simp only [aggregateCost, squareCost]
  rw [show freshCount n + 2 - 1 = freshCount n + 1 by omega, Nat.choose_two_right]
  simp [Nat.mul_comm]

theorem squareCost_le_aggregateCost {n j : ℕ} (hr : 1 ≤ freshCount n) (hj : 2 ≤ j) :
    squareCost n ≤ aggregateCost n j := by
  rw [← aggregateCost_two n]
  exact aggregateCost_mono_degree hr hj

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem middle_fresh_count_checked :
    ∀ n ∈ Finset.Icc 25 66, 3 ≤ freshCount n := by weighted_decide

theorem middle_fresh_count {n : ℕ} (hn : 25 ≤ n) (hn' : n ≤ 66) :
    3 ≤ freshCount n := middle_fresh_count_checked n (Finset.mem_Icc.mpr ⟨hn, hn'⟩)

/-- No untested degree above six can escape the finite degree cutoff. -/
theorem middle_higher_degree_cutoff {n j : ℕ} (hn : 25 ≤ n) (hn' : n ≤ 66)
    (hj : 6 ≤ j) : n ≤ aggregateCost n j := by
  have hr : 1 ≤ freshCount n := by have := middle_fresh_count hn hn'; omega
  exact (higherResidueBudgets hn hn').1.trans (aggregateCost_mono_degree hr hj)

/-- The middle residue capacity in the strict integer-power form, for every odd
prime at least five and every nonzero residue degree. -/
theorem middle_residue_budget {n q j : ℕ} (hn : 25 ≤ n) (hn' : n ≤ 66)
    (hq : Nat.Prime q) (hq5 : 5 ≤ q) (hj : 0 < j) (hjq : j < q) :
    n ^ j < (aggregateCost n j + 1) ^ q := by
  by_cases hc : n ≤ aggregateCost n j
  · exact (Nat.pow_lt_pow_left (Nat.lt_succ_of_le hc) (Nat.ne_of_gt hj)).trans_le
      (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hjq))
  · have hcost : aggregateCost n j < n := by omega
    have hj6 : j < 6 := by
      by_contra h
      have := middle_higher_degree_cutoff hn hn' (by omega : 6 ≤ j)
      omega
    have hb := (higherResidueBudgets hn hn').2 j
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) hcost
    have hp : (if j ≤ 4 then 5 else 7) ≤ q := by
      split_ifs with hj4
      · exact hq5
      · have hq6 : q ≠ 6 := by
          intro h
          subst q
          exact (by decide : ¬ Nat.Prime 6) hq
        omega
    exact hb.trans_lt ((Nat.pow_lt_pow_left (Nat.lt_succ_self _)
      (by split_ifs <;> decide : (if j ≤ 4 then 5 else 7) ≠ 0)).trans_le
      (Nat.pow_le_pow_right (by omega) hp))

end WeightedPilz.Arithmetic

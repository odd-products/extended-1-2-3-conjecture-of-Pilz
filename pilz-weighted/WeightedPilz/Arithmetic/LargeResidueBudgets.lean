import WeightedPilz.Arithmetic.DigitCosts
import WeightedPilz.Arithmetic.Counts
import WeightedPilz.Arithmetic.Imported
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Exact all-degree numerical budgets in the large interval argument. -/

namespace WeightedPilz.Arithmetic

private theorem square_le_cubic_choose {r : ℕ} (hr : 8 ≤ r) :
    (r + 1) ^ 2 ≤ (r + 2).choose 3 := by
  have hc := Nat.ascFactorial_eq_factorial_mul_choose' r 3
  rw [show r + 3 - 1 = r + 2 by omega] at hc
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.factorial] at hc
  have hs := Nat.mul_le_mul_right r hr
  have hq : 6 * (r + 1) ≤ r * (r + 2) := by nlinarith
  have hm := Nat.mul_le_mul_right (r + 1) hq
  nlinarith

private theorem fourth_le_squareCost_cube {r : ℕ} (hr : 8 ≤ r) :
    (r + 1) ^ 4 ≤ ((r + 1).choose 2) ^ 3 := by
  have hc := Nat.ascFactorial_eq_factorial_mul_choose' r 2
  rw [show r + 2 - 1 = r + 1 by omega] at hc
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.factorial] at hc
  have htwo : 2 * (r + 1).choose 2 = r * (r + 1) := by nlinarith
  have hcube : 8 * ((r + 1).choose 2) ^ 3 = r ^ 3 * (r + 1) ^ 3 := by
    have h := congrArg (fun a : ℕ => a ^ 3) htwo
    simpa only [mul_pow, show (2 : ℕ) ^ 3 = 8 by decide] using h
  have hs := Nat.mul_le_mul_right r hr
  have hs' := Nat.mul_le_mul_right r hs
  have hsmall : 8 * (r + 1) ≤ r ^ 3 := by nlinarith
  have hm := Nat.mul_le_mul_right ((r + 1) ^ 3) hsmall
  have hfinal : 8 * (r + 1) ^ 4 ≤ 8 * ((r + 1).choose 2) ^ 3 := by
    calc
      8 * (r + 1) ^ 4 = (8 * (r + 1)) * (r + 1) ^ 3 := by ring
      _ ≤ r ^ 3 * (r + 1) ^ 3 := hm
      _ = 8 * ((r + 1).choose 2) ^ 3 := hcube.symm
  omega

private theorem large_lt_fresh_succ_square {n : ℕ} (hn : 67 ≤ n) :
    n < (freshCount n + 1) ^ 2 := by
  exact (Nat.lt_succ_sqrt' n).trans_le
    (pow_le_pow_left' (Nat.add_le_add_right (fresh_count_sqrt n hn) 1) 2)

/-- Every aggregate degree at least three already exceeds the large interval length. -/
theorem large_degree_cost {n j : ℕ} (hn : 67 ≤ n) (hj : 3 ≤ j) :
    n < (freshCount n + j - 1).choose j := by
  have hr : 8 ≤ freshCount n := fresh_count_eight n hn
  have hbase : n < (freshCount n + 3 - 1).choose 3 := by
    rw [show freshCount n + 3 - 1 = freshCount n + 2 by omega]
    exact (large_lt_fresh_succ_square hn).trans_le (square_le_cubic_choose hr)
  exact hbase.trans_le (choose_cost_mono (by omega : 1 ≤ freshCount n) hj)

/-- Exact integer-power capacities; no primality hypothesis on the modulus is needed. -/
theorem large_residue_budget {n q j : ℕ} (hn : 67 ≤ n) (hj : 0 < j) (hjq : j < q) :
    n ^ j < ((freshCount n + j - 1).choose j + 1) ^ q := by
  have hr : 8 ≤ freshCount n := fresh_count_eight n hn
  by_cases hj1 : j = 1
  · subst j
    simp only [Nat.add_sub_cancel, Nat.choose_one_right, pow_one]
    exact (large_lt_fresh_succ_square hn).trans_le
      (pow_le_pow_right' (by omega : 1 ≤ freshCount n + 1) (by omega : 2 ≤ q))
  by_cases hj2 : j = 2
  · subst j
    rw [show freshCount n + 2 - 1 = freshCount n + 1 by omega]
    have hlt : n ^ 2 < (freshCount n + 1) ^ 4 := by
      simpa only [← pow_mul] using
        (Nat.pow_lt_pow_left (large_lt_fresh_succ_square hn) (by decide : (2 : ℕ) ≠ 0))
    calc
      n ^ 2 < (freshCount n + 1) ^ 4 := hlt
      _ ≤ ((freshCount n + 1).choose 2) ^ 3 := fourth_le_squareCost_cube hr
      _ ≤ ((freshCount n + 1).choose 2 + 1) ^ 3 :=
        pow_le_pow_left' (Nat.le_succ _) 3
      _ ≤ ((freshCount n + 1).choose 2 + 1) ^ q :=
        pow_le_pow_right' (by omega) (by omega)
  · have hj3 : 3 ≤ j := by omega
    have hc := large_degree_cost hn hj3
    exact (Nat.pow_lt_pow_left (Nat.lt_succ_of_lt hc) (Nat.ne_of_gt hj)).trans_le
      (pow_le_pow_right' (by omega) (Nat.le_of_lt hjq))

end WeightedPilz.Arithmetic

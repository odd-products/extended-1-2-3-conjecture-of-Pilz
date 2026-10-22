import Pilz.Sieve30
import Pilz.SieveEstimates

/-!
# The initial two-prime real discrepancy bounds

The exact integer formulas give the endpoint errors needed for real inputs.
For `n = floor x`, the inequality `n ≤ x < n+1` interpolates those endpoint
bounds with the manuscript's errors `1/2` and `2/3`.
-/

noncomputable section

namespace Pilz

theorem roughCount_two_sharp (n : ℕ) :
    2 * roughCount {2} n ≤ n + 1 ∧ n ≤ 2 * roughCount {2} n := by
  rw [roughCount_two]
  omega

theorem roughCount_three_sharp (n : ℕ) :
    3 * roughCount {2, 3} n ≤ n + 2 ∧ n ≤ 3 * roughCount {2, 3} n + 1 := by
  rw [roughCount_two_three_formula]
  omega

/-- The uniform discrepancy for integers free of the prime 2. -/
theorem roughRealCount_two_discrepancy : RoughDiscrepancy {2} (1 / 2) (1 / 2) := by
  intro x hx
  let n := ⌊x⌋₊
  have hlo : (n : ℝ) ≤ x := Nat.floor_le hx
  have hhi : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hnat := roughCount_two_sharp n
  have hupper : 2 * (roughCount {2} n : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast hnat.1
  have hlower : (n : ℝ) ≤ 2 * (roughCount {2} n : ℝ) := by
    exact_mod_cast hnat.2
  change |(roughCount {2} n : ℝ) - (1 / 2 : ℝ) * x| ≤ 1 / 2
  apply abs_le.mpr
  constructor <;> linarith

/-- The uniform discrepancy after sieving by 2 and 3. -/
theorem roughRealCount_three_discrepancy : RoughDiscrepancy {2, 3} (1 / 3) (2 / 3) := by
  intro x hx
  let n := ⌊x⌋₊
  have hlo : (n : ℝ) ≤ x := Nat.floor_le hx
  have hhi : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hnat := roughCount_three_sharp n
  have hupper : 3 * (roughCount {2, 3} n : ℝ) ≤ (n : ℝ) + 2 := by
    exact_mod_cast hnat.1
  have hlower : (n : ℝ) ≤ 3 * (roughCount {2, 3} n : ℝ) + 1 := by
    exact_mod_cast hnat.2
  change |(roughCount {2, 3} n : ℝ) - (1 / 3 : ℝ) * x| ≤ 2 / 3
  apply abs_le.mpr
  constructor <;> linarith

end Pilz

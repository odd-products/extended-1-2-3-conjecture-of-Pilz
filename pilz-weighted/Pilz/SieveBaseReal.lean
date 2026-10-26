import Pilz.Sieve30
import Pilz.SieveEstimates

/-! The certified residue computations for the base sieve, interpolated to
all nonnegative real arguments with the manuscript's exact constants. -/

noncomputable section

namespace Pilz

/-- The base ordinary discrepancy is `14/15`. The sharper integer lower
error `10/15` compensates for the gap between a real input and its floor. -/
theorem roughRealCount_five_discrepancy :
    RoughDiscrepancy {2, 3, 5} (4 / 15) (14 / 15) := by
  intro x hx
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hnext : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hu : (15 : ℝ) * roughCount {2, 3, 5} ⌊x⌋₊ ≤ 4 * (⌊x⌋₊ : ℝ) + 14 := by
    exact_mod_cast (roughCount_five_discrepancy ⌊x⌋₊).1
  have hl : (4 : ℝ) * (⌊x⌋₊ : ℝ) ≤ 15 * roughCount {2, 3, 5} ⌊x⌋₊ + 10 := by
    exact_mod_cast roughCount_five_lower_ten ⌊x⌋₊
  unfold roughRealCount
  apply abs_le.mpr
  constructor <;> linarith

/-- The half-interval discrepancy `22/15` uses the independent period-60
calculation rather than twice the ordinary discrepancy. -/
theorem roughRealIntervalCount_five_discrepancy :
    RoughIntervalDiscrepancy {2, 3, 5} (4 / 15) (22 / 15) := by
  intro x hx
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hnext : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hu : (15 : ℝ) * roughIntervalCount {2, 3, 5} ⌊x⌋₊ ≤
      2 * (⌊x⌋₊ : ℝ) + 22 := by
    exact_mod_cast (roughIntervalCount_five_discrepancy ⌊x⌋₊).1
  have hl : (2 : ℝ) * (⌊x⌋₊ : ℝ) ≤
      15 * roughIntervalCount {2, 3, 5} ⌊x⌋₊ + 20 := by
    exact_mod_cast roughIntervalCount_five_lower_twenty ⌊x⌋₊
  rw [roughRealIntervalCount_eq_floor]
  apply abs_le.mpr
  constructor <;> linarith

end Pilz

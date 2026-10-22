import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Certified logarithmic constants in the Chebyshev estimate

These are the numerical inequalities at the end of the manuscript's
Chebyshev proof. The lower bounds use finite sums of the logarithm series.
The upper bound for `log (3/2)` uses the library's proved Taylor remainder
bound. No floating-point evaluation is used.
-/

namespace Pilz.Chebyshev

open scoped BigOperators

theorem log_two_lower : (693 : ℝ) / 1000 < Real.log 2 :=
  lt_trans (by norm_num) Real.log_two_gt_d9

theorem log_two_upper : Real.log 2 < (25 : ℝ) / 36 :=
  lt_trans Real.log_two_lt_d9 (by norm_num)

theorem twentyfive_thirtysix_lt_seven_tenths : (25 : ℝ) / 36 < 7 / 10 := by
  norm_num

theorem log_two_upper_seven_tenths : Real.log 2 < (7 : ℝ) / 10 :=
  log_two_upper.trans twentyfive_thirtysix_lt_seven_tenths

theorem log_two_bounds :
    (693 : ℝ) / 1000 < Real.log 2 ∧ Real.log 2 < 25 / 36 ∧ (25 : ℝ) / 36 < 7 / 10 :=
  ⟨log_two_lower, log_two_upper, twentyfive_thirtysix_lt_seven_tenths⟩

theorem log_three_lower : (1098 : ℝ) / 1000 < Real.log 3 := by
  have hs := Real.hasSum_log_one_add (show (0 : ℝ) ≤ 2 by norm_num)
  have h := sum_le_hasSum (Finset.range 4) (fun k _hk => by positivity) hs
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem log_five_fourths_lower : (223 : ℝ) / 1000 < Real.log (5 / 4) := by
  have hs := Real.hasSum_log_one_add (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  have h := sum_le_hasSum (Finset.range 2) (fun k _hk => by positivity) hs
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem log_five_lower : (1609 : ℝ) / 1000 < Real.log 5 := by
  have hid : Real.log (5 : ℝ) = Real.log (5 / 4) + 2 * Real.log 2 := by
    calc
      Real.log (5 : ℝ) = Real.log ((5 / 4 : ℝ) * 2 ^ 2) := by norm_num
      _ = Real.log (5 / 4) + Real.log ((2 : ℝ) ^ 2) :=
        Real.log_mul (by norm_num) (by norm_num)
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [hid]
  linarith [log_five_fourths_lower, log_two_lower]

theorem log_three_halves_upper : Real.log (3 / 2 : ℝ) < (73 : ℝ) / 180 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |(1 / 3 : ℝ)| < 1 by norm_num) 8
  norm_num [Finset.sum_range_succ] at h
  have hid : Real.log (2 / 3 : ℝ) = -Real.log (3 / 2 : ℝ) := by
    simpa using Real.log_inv (3 / 2 : ℝ)
  rw [hid] at h
  have hlo := (abs_le.mp h).1
  linarith

theorem log_six_eq : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
  have h := Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) (show (3 : ℝ) ≠ 0 by norm_num)
  norm_num at h
  exact h

theorem log_thirty_eq : Real.log (30 : ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
  calc
    Real.log (30 : ℝ) = Real.log ((2 : ℝ) * 3 * 5) := by norm_num
    _ = Real.log ((2 : ℝ) * 3) + Real.log 5 := Real.log_mul (by norm_num) (by norm_num)
    _ = _ := by rw [Real.log_mul (by norm_num) (by norm_num)]

theorem log_sixty_eq : Real.log (60 : ℝ) = 2 * Real.log 2 + Real.log 3 + Real.log 5 := by
  calc
    Real.log (60 : ℝ) = Real.log ((2 : ℝ) ^ 2 * 3 * 5) := by norm_num
    _ = Real.log ((2 : ℝ) ^ 2 * 3) + Real.log 5 := Real.log_mul (by norm_num) (by norm_num)
    _ = (Real.log ((2 : ℝ) ^ 2) + Real.log 3) + Real.log 5 := by
      rw [Real.log_mul (by norm_num) (by norm_num)]
    _ = _ := by rw [Real.log_pow]; norm_num

/-- The numerical lower bound on the explicitly displayed `mu1`. -/
theorem mu1_numeric :
    (23 : ℝ) / 25 < (14 * Real.log 2 + 9 * Real.log 3 + 5 * Real.log 5) / 30 := by
  linarith [log_two_lower, log_three_lower, log_five_lower]

theorem log_six_lower : (25 : ℝ) / 14 < Real.log 6 := by
  rw [log_six_eq]
  linarith [log_two_lower, log_three_lower]

theorem reciprocal_log_six_upper : (5 : ℝ) / (4 * Real.log 6) < 7 / 10 := by
  have hpos : 0 < 4 * Real.log (6 : ℝ) := by linarith [log_six_lower]
  apply (div_lt_iff₀ hpos).mpr
  linarith [log_six_lower]

theorem shift_lower : (99 : ℝ) / 100 < 6 / 5 - (1 / 2 : ℝ) * Real.log (3 / 2) := by
  linarith [log_three_halves_upper]

theorem log_sixty_constant : (2 : ℝ) < Real.log 60 - 2 := by
  rw [log_sixty_eq]
  linarith [log_two_lower, log_three_lower, log_five_lower]

theorem log_thirty_constant : -Real.log (30 : ℝ) + (1 - 3 * Real.log 2) / 2 < -3 := by
  rw [log_thirty_eq]
  linarith [log_two_lower, log_three_lower, log_five_lower]

end Pilz.Chebyshev

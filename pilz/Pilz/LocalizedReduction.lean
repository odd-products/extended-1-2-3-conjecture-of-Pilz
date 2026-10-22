import Pilz.LocalizedFinite
import Pilz.LogConstants

/-! The index-one components force a short localized multiplier to have few
terms, by comparison with the actual fresh-prime count. -/

noncomputable section

namespace Pilz

theorem weight_mul_freshCount_le (n q : ℕ) (D : Poly)
    (hqn : q ≤ n / 2) (hlargest : LargestPrime D q) :
    weight D * freshCount n ≤ weight (interval n * D) := by
  exact (Nat.mul_le_mul_left (weight D)
    (freshCount_le_roughIntervalCount n q hqn)).trans
    (weight_interval_mul_ge_index_one (primesUpTo q) n D (primesUpTo_prime q)
      (largestPrime_vars_subset D q hlargest))

theorem weight_lt_thirty_of_short (n q : ℕ) (D : Poly)
    (hqn : q ≤ n / 2) (hlargest : LargestPrime D q)
    (hshort : weight (interval n * D) < n)
    (hr : (n : ℝ) / 30 < freshCount n) : weight D < 30 := by
  have hbudget : (weight D : ℝ) * freshCount n < n := by
    exact_mod_cast (weight_mul_freshCount_le n q D hqn hlargest).trans_lt hshort
  by_contra hnot
  have hu : (30 : ℝ) ≤ weight D := by exact_mod_cast (show 30 ≤ weight D by omega)
  have hmul := mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg (freshCount n) : (0 : ℝ) ≤ _)
  linarith

theorem weight_lt_log_of_short (n q : ℕ) (D : Poly)
    (hn : 2 ≤ n) (hqn : q ≤ n / 2) (hlargest : LargestPrime D q)
    (hshort : weight (interval n * D) < n)
    (hr : 7 * (n : ℝ) / (20 * Real.log n) < freshCount n) :
    (weight D : ℝ) < (20 / 7) * Real.log n := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hr' := (div_lt_iff₀ (show (0 : ℝ) < 20 * Real.log n by positivity)).mp hr
  have hbudget : (weight D : ℝ) * freshCount n < n := by
    exact_mod_cast (weight_mul_freshCount_le n q D hqn hlargest).trans_lt hshort
  by_contra hnot
  have hu : (20 / 7) * Real.log n ≤ (weight D : ℝ) := le_of_not_gt hnot
  have hmul := mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg (freshCount n) : (0 : ℝ) ≤ _)
  nlinarith

end Pilz

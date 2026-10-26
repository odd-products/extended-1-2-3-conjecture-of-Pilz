import WeightedPilz.Arithmetic.Imported
import WeightedPilz.Arithmetic.EndpointBudgets

/-! The unbounded arithmetic tail for large affine multipliers. -/

namespace WeightedPilz.Arithmetic

theorem fresh_le_squareCost (n : ℕ) : freshCount n ≤ squareCost n := by
  unfold squareCost
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  by_cases hr : freshCount n = 0
  · simp [hr]
  · have hpos : 1 ≤ freshCount n := by omega
    nlinarith

theorem squareCost_ge_large {n : ℕ} (hn : 1800 ≤ n) : n ≤ squareCost n := by
  by_cases hmid : n ≤ 32768
  · have hr := fresh_count_div_thirty (show 1024 ≤ n by omega) hmid
    have hnR : (1800 : ℝ) ≤ n := by exact_mod_cast hn
    have hr60 : 60 ≤ freshCount n := by
      have hrR : (60 : ℝ) < freshCount n := by
        change (60 : ℝ) < Pilz.freshCount n
        linarith
      exact le_of_lt (by exact_mod_cast hrR)
    have hn30 : n < 30 * freshCount n := by
      have hR : (n : ℝ) < 30 * freshCount n := by
        change (n : ℝ) < 30 * Pilz.freshCount n
        linarith
      exact_mod_cast hR
    unfold squareCost
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    nlinarith
  · have hlarge : 32768 ≤ n := by omega
    have hr := fresh_count_six_sqrt hlarge
    have hsq := mul_self_lt_mul_self (by positivity : (0 : ℝ) ≤ 6 * Real.sqrt (n : ℝ)) hr
    have hsqrt := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hh : n * 2 ≤ freshCount n * (freshCount n + 1) := by
      have hR : (n : ℝ) * 2 ≤ (freshCount n : ℝ) * ((freshCount n : ℝ) + 1) := by
        change (n : ℝ) * 2 ≤ (Pilz.freshCount n : ℝ) * ((Pilz.freshCount n : ℝ) + 1)
        nlinarith [show (0 : ℝ) ≤ (Pilz.freshCount n : ℝ) by positivity]
      exact_mod_cast hR
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr hh

/-- The full `d+R≥n` bound, including all `n` beyond the finite table. -/
theorem dimension_square_budget {n : ℕ} (hn : 229 ≤ n) :
    n ≤ 1 + primeCount (n / 2) + squareCost n := by
  by_cases hsmall : n ≤ 1799
  · exact dimensionBudget hn hsmall
  · exact (squareCost_ge_large (by omega : 1800 ≤ n)).trans (Nat.le_add_left _ _)

end WeightedPilz.Arithmetic

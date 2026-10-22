import Pilz.SievePrimes
import Pilz.LogConstants
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The real inequalities in the large-support-prime estimate. The exponential
tail is certified with rational Taylor sums, as in the manuscript. -/

noncomputable section

namespace Pilz

open scoped BigOperators

theorem exp_eight_gt_2800 : (2800 : ℝ) < Real.exp 8 := by
  have h₃ := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num) 9
  have h₂ := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h₃ h₂
  have h₃' : (20 : ℝ) < Real.exp 3 := by linarith
  have h₂' : (7 : ℝ) < Real.exp 2 := by linarith
  have hsq : (400 : ℝ) < (Real.exp 3) ^ 2 := by nlinarith [Real.exp_pos 3]
  have hprod : (2800 : ℝ) < (Real.exp 3) ^ 2 * Real.exp 2 := by
    nlinarith [Real.exp_pos 2]
  have heq : Real.exp (8 : ℝ) = (Real.exp 3) ^ 2 * Real.exp 2 := by
    calc
      Real.exp (8 : ℝ) = Real.exp (3 + 3 + 2) := by norm_num
      _ = _ := by rw [Real.exp_add, Real.exp_add]; ring
  rwa [heq]

/-- The decreasing-tail calculation, expressed without invoking a derivative:
`exp t >= 1+t` bounds the ratio to the value at 48. -/
theorem large_sieve_exp_growth (L : ℝ) (hL : 48 ≤ L) :
    (175 / 3) * L < Real.exp ((13 / 77) * L) := by
  have hLpos : 0 < L := by linarith
  have h₀ : (2800 : ℝ) < Real.exp (624 / 77) :=
    exp_eight_gt_2800.trans (Real.exp_lt_exp.mpr (by norm_num))
  have hlin := Real.add_one_le_exp ((13 / 77) * (L - 48))
  have hratio : L / 48 ≤ Real.exp ((13 / 77) * (L - 48)) := by linarith
  have hm : 2800 * (L / 48) <
      Real.exp (624 / 77) * Real.exp ((13 / 77) * (L - 48)) := by
    exact (mul_lt_mul_of_pos_right h₀ (by positivity)).trans_le
      (mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le)
  rw [← Real.exp_add] at hm
  have hleft : (2800 : ℝ) * (L / 48) = (175 / 3) * L := by ring
  have harg : (624 / 77 : ℝ) + (13 / 77) * (L - 48) = (13 / 77) * L := by ring
  rwa [hleft, harg] at hm

/-- The manuscript's error estimate `2 u delta < 3 n / 4`, with `n=exp L`. -/
theorem large_sieve_error (L u δ : ℝ) (hL : 48 ≤ L) (hu : 0 ≤ u)
    (huL : u < (20 / 7) * L)
    (hδ : δ ≤ (112 / 15) * Real.exp ((64 / 77) * L)) :
    2 * u * δ < (3 / 4) * Real.exp L := by
  have hLpos : 0 < L := by linarith
  have hExp := large_sieve_exp_growth L hL
  have hmain : (175 / 3) * L * Real.exp ((64 / 77) * L) < Real.exp L := by
    have hm := mul_lt_mul_of_pos_right hExp (Real.exp_pos ((64 / 77) * L))
    rw [← Real.exp_add] at hm
    convert hm using 1 <;> congr 1 <;> ring
  have herr : 2 * u * δ < (128 / 3) * L * Real.exp ((64 / 77) * L) := by
    calc
      2 * u * δ ≤ 2 * u * ((112 / 15) * Real.exp ((64 / 77) * L)) :=
        mul_le_mul_of_nonneg_left hδ (by positivity)
      _ < 2 * ((20 / 7) * L) * ((112 / 15) * Real.exp ((64 / 77) * L)) :=
        mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left huL (by norm_num)) (by positivity)
      _ = _ := by ring
  have hpos : 0 < L * Real.exp ((64 / 77) * L) := by positivity
  nlinarith

/-- Conversion of the 11-rough prime-count estimate to the exponential
discrepancy bound used in the last support-prime range. -/
theorem large_sieve_delta_bound (q : ℕ) (L : ℝ) (hq : 5 ≤ q)
    (hπ : (primeCount q : ℝ) < (16 / 77) * q + 6)
    (hqL : (q : ℝ) < (40 / 7) * L) :
    sieveDelta q < (112 / 15) * Real.exp ((64 / 77) * L) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hπ3 := primeCount_ge_three hq
  have hexp : (2 : ℝ) ^ (primeCount q - 3) =
      Real.exp (((primeCount q : ℝ) - 3) * Real.log 2) := by
    rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul]
    rw [Real.log_exp, Nat.cast_sub hπ3]
    norm_num
  have hE : Real.exp (((primeCount q : ℝ) - 3) * Real.log 2) <
      8 * Real.exp ((16 / 77) * (q : ℝ) * Real.log 2) := by
    have harg : ((primeCount q : ℝ) - 3) * Real.log 2 <
        ((16 / 77) * (q : ℝ) + 3) * Real.log 2 := by
      nlinarith
    have hh := Real.exp_lt_exp.mpr harg
    have hsplit : ((16 / 77) * (q : ℝ) + 3) * Real.log 2 =
        (3 : ℝ) * Real.log 2 + (16 / 77) * (q : ℝ) * Real.log 2 := by ring
    have hthree : Real.exp ((3 : ℝ) * Real.log 2) = 8 := by
      calc
        Real.exp ((3 : ℝ) * Real.log 2) = Real.exp (Real.log 2 + Real.log 2 + Real.log 2) := by
          congr 1; ring
        _ = 8 := by rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]; norm_num
    rw [hsplit, Real.exp_add, hthree] at hh
    exact hh
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have harg : (16 / 77) * (q : ℝ) * Real.log 2 < (64 / 77) * L := by
    have hh := mul_lt_mul_of_pos_left Chebyshev.log_two_upper_seven_tenths
      (show (0 : ℝ) < (16 / 77) * (q : ℝ) by positivity)
    linarith
  have hh := mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr harg)
    (show (0 : ℝ) < 8 by norm_num)
  unfold sieveDelta
  rw [hexp]
  have hresult := mul_lt_mul_of_pos_left (hE.trans hh) (show (0 : ℝ) < 14 / 15 by norm_num)
  convert hresult using 1 <;> ring

end Pilz

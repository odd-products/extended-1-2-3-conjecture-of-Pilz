import Pilz.ChebyshevIteration
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The exact numerical tail estimate in the prime-power paragraph. -/

noncomputable section

namespace Pilz.Chebyshev

theorem log_256_eq : Real.log (256 : ℝ) = 8 * Real.log 2 := by
  calc
    Real.log (256 : ℝ) = Real.log ((2 : ℝ) ^ 8) := by norm_num
    _ = _ := by rw [Real.log_pow]; norm_num

def oddTail (L : ℝ) : ℝ :=
  (L / (2 * Real.log 2) - 3 / 2) * Real.exp (-3 * L / 10)

theorem oddTail_hasDerivAt (L : ℝ) :
    HasDerivAt oddTail
      (Real.exp (-3 * L / 10) *
        (1 / (2 * Real.log 2) - 3 / 10 * (L / (2 * Real.log 2) - 3 / 2))) L := by
  have h1 := ((hasDerivAt_id L).div_const (2 * Real.log 2)).sub_const (3 / 2)
  have h2 := (((hasDerivAt_id L).const_mul (-3)).div_const 10).exp
  convert h1.mul h2 using 1 <;> (try ext x) <;> dsimp [oddTail] <;> ring

theorem oddTail_antitone : AntitoneOn oddTail (Set.Ici (8 * Real.log 2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact fun L _ => (oddTail_hasDerivAt L).continuousAt.continuousWithinAt
  · exact fun L _ => (oddTail_hasDerivAt L).differentiableAt.differentiableWithinAt
  · intro L hL
    have hL' : 8 * Real.log 2 ≤ L := interior_subset hL
    have hb : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    rw [(oddTail_hasDerivAt L).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
    have hid : 1 / (2 * Real.log 2) -
        3 / 10 * (L / (2 * Real.log 2) - 3 / 2) =
        (10 - 3 * L + 9 * Real.log 2) / (20 * Real.log 2) := by
      field_simp
      ring
    rw [hid]
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith [log_two_lower]
    · positivity

theorem two_rpow_twelve_fifths_gt_five : (5 : ℝ) < (2 : ℝ) ^ (12 / 5 : ℝ) := by
  have heq : ((2 : ℝ) ^ (12 / 5 : ℝ)) ^ 5 = 4096 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  apply lt_of_pow_lt_pow_left₀ 5 (Real.rpow_nonneg (by norm_num) _)
  rw [heq]
  norm_num

theorem oddTail_endpoint : oddTail (8 * Real.log 2) < 1 / 2 := by
  have hb : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hcoef : (8 * Real.log 2) / (2 * Real.log 2) - (3 / 2 : ℝ) = 5 / 2 := by
    field_simp
    ring
  have hexp : Real.exp (-3 * (8 * Real.log 2) / 10) = (2 : ℝ) ^ (-12 / 5 : ℝ) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hinv : (2 : ℝ) ^ (-12 / 5 : ℝ) < 1 / 5 := by
    rw [show (-12 / 5 : ℝ) = -(12 / 5) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 5)
      two_rpow_twelve_fifths_gt_five
  unfold oddTail
  rw [hcoef, hexp]
  linarith

theorem cubic_tail_bound {x : ℝ} (hx : 256 ≤ x) : x ^ (-1 / 6 : ℝ) < 2 / 5 := by
  have hxpos : 0 < x := by linarith
  have hroot : (5 / 2 : ℝ) < x ^ (1 / 6 : ℝ) := by
    rw [one_div]
    apply (Real.lt_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 5 / 2)
      hxpos.le (by norm_num : (0 : ℝ) < 6)).mpr
    norm_num [Real.rpow_natCast]
    linarith
  rw [show (-1 / 6 : ℝ) = -(1 / 6) by ring, Real.rpow_neg hxpos.le]
  have hi := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 5 / 2) hroot
  norm_num at hi
  exact hi

theorem higher_odd_tail_bound {x : ℝ} (hx : 256 ≤ x) :
    (Real.log x / (2 * Real.log 2) - 3 / 2) * x ^ (-3 / 10 : ℝ) < 1 / 2 := by
  have hxpos : 0 < x := by linarith
  have hlog : 8 * Real.log 2 ≤ Real.log x := by
    rw [← log_256_eq]
    exact Real.log_le_log (by norm_num) hx
  have ha := oddTail_antitone
    (show 8 * Real.log 2 ∈ Set.Ici (8 * Real.log 2) by change 8 * Real.log 2 ≤ 8 * Real.log 2; rfl)
    (show Real.log x ∈ Set.Ici (8 * Real.log 2) by change 8 * Real.log 2 ≤ Real.log x; exact hlog) hlog
  have hid : oddTail (Real.log x) =
      (Real.log x / (2 * Real.log 2) - 3 / 2) * x ^ (-3 / 10 : ℝ) := by
    unfold oddTail
    rw [Real.rpow_def_of_pos hxpos]
    congr 2
    ring
  rw [hid] at ha
  exact ha.trans_lt oddTail_endpoint

theorem primePower_tail_factor {x : ℝ} (hx : 256 ≤ x) :
    Real.log 4 * (1 + x ^ (-1 / 6 : ℝ) +
      (Real.log x / (2 * Real.log 2) - 3 / 2) * x ^ (-3 / 10 : ℝ)) < 8 / 3 := by
  have hcube := cubic_tail_bound hx
  have hodd := higher_odd_tail_bound hx
  have hlogfour : Real.log (4 : ℝ) < 7 / 5 := by
    have hid : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      calc
        Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
        _ = _ := by rw [Real.log_pow]; norm_num
    rw [hid]
    linarith [log_two_upper_seven_tenths]
  have hlogpos : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  nlinarith

end Pilz.Chebyshev

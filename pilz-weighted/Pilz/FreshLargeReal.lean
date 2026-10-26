import Pilz.ChebyshevXi
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp

/-! The final calculus argument of the paper. The Chebyshev input is an explicit
premise, so these lemmas can be checked independently of the number-theoretic bridge. -/
noncomputable section

namespace Pilz.Chebyshev

def freshW (L : ℝ) : ℝ := (7 / 10) * (L - 99 / 100) ^ 2 + (5 / 2) * L + 7

def freshW' (L : ℝ) : ℝ := (7 / 5) * (L - 99 / 100) + 5 / 2

def freshG (L : ℝ) : ℝ := 46 / 125 - (8 / 3) * Real.exp (-L / 2) - Real.exp (-L) * freshW L

def freshG' (L : ℝ) : ℝ := (4 / 3) * Real.exp (-L / 2) + Real.exp (-L) * (freshW L - freshW' L)

def freshG'' (L : ℝ) : ℝ := -(2 / 3) * Real.exp (-L / 2) -
  Real.exp (-L) * (freshW L - 2 * freshW' L + 7 / 5)

theorem freshW_hasDerivAt (L : ℝ) : HasDerivAt freshW (freshW' L) L := by
  convert ((((hasDerivAt_id L).sub_const (99 / 100)).pow 2).const_mul (7 / 10)).add
    (((hasDerivAt_id L).const_mul (5 / 2)).add_const 7) using 1 <;>
    (try ext x) <;> simp [freshW, freshW'] <;> ring

theorem freshW'_hasDerivAt (L : ℝ) : HasDerivAt freshW' (7 / 5) L := by
  convert (((hasDerivAt_id L).sub_const (99 / 100)).const_mul (7 / 5)).add_const (5 / 2) using 1 <;>
    dsimp [freshW'] <;> ring

theorem freshG_hasDerivAt (L : ℝ) : HasDerivAt freshG (freshG' L) L := by
  have hhalf := (((hasDerivAt_id L).neg).div_const 2).exp
  have hneg := ((hasDerivAt_id L).neg).exp
  convert ((hhalf.const_mul (8 / 3)).const_sub (46 / 125)).sub
    (hneg.mul (freshW_hasDerivAt L)) using 1 <;>
    dsimp [freshG, freshG'] <;> ring

theorem freshG'_hasDerivAt (L : ℝ) : HasDerivAt freshG' (freshG'' L) L := by
  have hhalf := (((hasDerivAt_id L).neg).div_const 2).exp
  have hneg := ((hasDerivAt_id L).neg).exp
  convert (hhalf.const_mul (4 / 3)).add
    (hneg.mul ((freshW_hasDerivAt L).sub (freshW'_hasDerivAt L))) using 1 <;>
    dsimp [freshG', freshG''] <;> ring

theorem deriv_freshG : deriv freshG = freshG' := funext fun L => (freshG_hasDerivAt L).deriv

theorem deriv2_freshG (L : ℝ) : (deriv^[2] freshG) L = freshG'' L := by
  change deriv (deriv freshG) L = _
  rw [deriv_freshG]
  exact (freshG'_hasDerivAt L).deriv

theorem freshW_sub_deriv_pos {L : ℝ} (hL : 6 ≤ L) : 0 < freshW L - freshW' L := by
  dsimp [freshW, freshW']
  nlinarith [sq_nonneg (L - 199 / 100)]

theorem freshW_second_difference_pos {L : ℝ} (hL : 6 ≤ L) :
    0 < freshW L - 2 * freshW' L + 7 / 5 := by
  dsimp [freshW, freshW']
  nlinarith [sq_nonneg (L - 299 / 100)]

theorem freshG'_pos {L : ℝ} (hL : 6 ≤ L) : 0 < freshG' L := by
  unfold freshG'
  have h := freshW_sub_deriv_pos hL
  positivity

theorem freshG''_neg {L : ℝ} (hL : 6 ≤ L) : freshG'' L < 0 := by
  have h := freshW_second_difference_pos hL
  have h1 := Real.exp_pos (-L / 2)
  have h2 : 0 < Real.exp (-L) * (freshW L - 2 * freshW' L + 7 / 5) := mul_pos (Real.exp_pos _) h
  unfold freshG''
  linarith

theorem freshG_strictMonoOn : StrictMonoOn freshG (Set.Ici 6) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 6)
  · exact fun L _ => (freshG_hasDerivAt L).continuousAt.continuousWithinAt
  · intro L hL
    rw [deriv_freshG]
    exact freshG'_pos (interior_subset hL)

theorem freshG_strictConcaveOn : StrictConcaveOn ℝ (Set.Ici 6) freshG := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ici 6)
  · exact fun L _ => (freshG_hasDerivAt L).continuousAt.continuousWithinAt
  · intro L hL
    rw [deriv2_freshG]
    exact freshG''_neg hL




theorem freshW_strictMonoOn : StrictMonoOn freshW (Set.Ici 6) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 6)
  · exact fun L _ => (freshW_hasDerivAt L).continuousAt.continuousWithinAt
  · intro L hL
    rw [(freshW_hasDerivAt L).deriv]
    have h6 : 6 ≤ L := interior_subset hL
    dsimp [freshW']
    linarith

theorem log_1024_eq : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 10
  norm_num at h
  exact h

theorem log_32768_eq : Real.log (32768 : ℝ) = 15 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 15
  norm_num at h
  exact h

theorem log_1024_bounds : 6 < Real.log (1024 : ℝ) ∧ Real.log (1024 : ℝ) < 7 := by
  rw [log_1024_eq]
  constructor <;> linarith [log_two_lower, log_two_upper_seven_tenths]

theorem log_32768_bounds : 6 < Real.log (32768 : ℝ) ∧ Real.log (32768 : ℝ) < 21 / 2 := by
  rw [log_32768_eq]
  constructor <;> linarith [log_two_lower, log_two_upper_seven_tenths]

theorem sqrt_eq_exp_half_log {x : ℝ} (hx : 0 < x) :
    Real.sqrt x = Real.exp (Real.log x / 2) := by
  apply (Real.sqrt_eq_iff_mul_self_eq hx.le (Real.exp_pos _).le).mpr
  rw [← Real.exp_add, show Real.log x / 2 + Real.log x / 2 = Real.log x by ring,
    Real.exp_log hx]

theorem exp_neg_half_log {x : ℝ} (hx : 0 < x) :
    Real.exp (-Real.log x / 2) = (Real.sqrt x)⁻¹ := by
  rw [show -Real.log x / 2 = -(Real.log x / 2) by ring, Real.exp_neg,
    ← sqrt_eq_exp_half_log hx]

theorem freshG_log_mul {x : ℝ} (hx : 0 < x) :
    freshG (Real.log x) * x = (46 / 125) * x - (8 / 3) * Real.sqrt x - freshW (Real.log x) := by
  have hhalf : Real.exp (-Real.log x / 2) * x = Real.sqrt x := by
    calc
      _ = Real.exp (-Real.log x / 2) * Real.exp (Real.log x) := by rw [Real.exp_log hx]
      _ = Real.exp (Real.log x / 2) := by rw [← Real.exp_add]; congr 1; ring
      _ = Real.sqrt x := (sqrt_eq_exp_half_log hx).symm
  have hone : Real.exp (-Real.log x) * x = 1 := by
    rw [Real.exp_neg, Real.exp_log hx]
    exact inv_mul_cancel₀ hx.ne'
  calc
    freshG (Real.log x) * x = (46 / 125) * x - (8 / 3) * (Real.exp (-Real.log x / 2) * x) -
      (Real.exp (-Real.log x) * x) * freshW (Real.log x) := by unfold freshG; ring
    _ = _ := by rw [hhalf, hone]; ring

theorem freshG_endpoint_1024 :
    Real.log (1024 : ℝ) / 30 < freshG (Real.log 1024) := by
  obtain ⟨hlo, hhi⟩ := log_1024_bounds
  have hw : freshW (Real.log 1024) < 50 := by
    have h := freshW_strictMonoOn hlo.le (by norm_num : (6 : ℝ) ≤ 7) hhi
    norm_num [freshW] at h ⊢
    linarith
  have hg := freshG_log_mul (by norm_num : (0 : ℝ) < 1024)
  have hs : Real.sqrt (1024 : ℝ) = 32 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [hs] at hg
  nlinarith

theorem freshG_endpoint_32768 : (7 : ℝ) / 20 < freshG (Real.log 32768) := by
  obtain ⟨hlo, hhi⟩ := log_32768_bounds
  have hw : freshW (Real.log 32768) < 97 := by
    have h := freshW_strictMonoOn hlo.le (by norm_num : (6 : ℝ) ≤ 21 / 2) hhi
    norm_num [freshW] at h ⊢
    linarith
  have hs : (180 : ℝ) < Real.sqrt 32768 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-Real.log (32768 : ℝ) / 2) < 1 / 180 := by
    rw [exp_neg_half_log (by norm_num)]
    simpa [one_div] using (inv_lt_inv₀ (by norm_num) (by positivity)).mpr hs
  have hp : 0 < Real.exp (-Real.log (32768 : ℝ)) := Real.exp_pos _
  have hw' : Real.exp (-Real.log (32768 : ℝ)) * freshW (Real.log 32768) < 97 / 32768 := by
    have hm := mul_lt_mul_of_pos_left hw hp
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 32768)] at hm
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 32768)]
    norm_num at hm ⊢
    exact hm
  unfold freshG
  linarith

theorem freshG_gt_linear {L : ℝ} (hlo : Real.log (1024 : ℝ) ≤ L)
    (hhi : L ≤ Real.log (32768 : ℝ)) : L / 30 < freshG L := by
  have hconv : ConvexOn ℝ (Set.Ici (6 : ℝ)) (fun L : ℝ => L / 30) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (convexOn_id (convex_Ici (6 : ℝ))).smul (show (0 : ℝ) ≤ (30 : ℝ)⁻¹ by positivity)
  have hconc := freshG_strictConcaveOn.concaveOn.sub hconv
  have hend : 0 < freshG (Real.log 32768) - Real.log 32768 / 30 := by
    have h := freshG_endpoint_32768
    linarith [log_32768_bounds.2]
  have hstart : 0 < freshG (Real.log 1024) - Real.log 1024 / 30 := by
    linarith [freshG_endpoint_1024]
  have h := hconc.min_le_of_mem_Icc log_1024_bounds.1.le log_32768_bounds.1.le ⟨hlo, hhi⟩
  change min (freshG (Real.log 1024) - Real.log 1024 / 30)
    (freshG (Real.log 32768) - Real.log 32768 / 30) ≤ freshG L - L / 30 at h
  have hp := lt_min hstart hend
  linarith

theorem freshG_gt_seven_twentieths {L : ℝ} (hL : Real.log (32768 : ℝ) ≤ L) :
    (7 : ℝ) / 20 < freshG L :=
  freshG_endpoint_32768.trans_le
    (freshG_strictMonoOn.monotoneOn log_32768_bounds.1.le
      (log_32768_bounds.1.le.trans hL) hL)



/-- Exactly inequality (rlogn) in the journal manuscript. -/
def FreshLogLowerBound : Prop := ∀ n : ℕ, 256 ≤ n →
  (2 / 5) * mu1 * (n : ℝ) - (8 / 3) * Real.sqrt n - (5 / 2) * Real.log n +
    2 - eta ((n : ℝ) / 2) < (freshCount n : ℝ) * Real.log n

theorem eta_half_lt_freshW {x : ℝ} (hx : 0 < x) (hL : 6 ≤ Real.log x) :
    eta (x / 2) < (7 / 10) * (Real.log x - 99 / 100) ^ 2 + 9 := by
  let b : ℝ := 6 / 5 - (1 / 2) * Real.log (3 / 2)
  have hb : 99 / 100 < b := shift_lower
  have hb6 : b < 6 := by
    have hp : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
    dsimp [b]
    linarith
  have hsq : (Real.log x - b) ^ 2 < (Real.log x - 99 / 100) ^ 2 := by
    have hp := mul_pos (sub_pos.mpr hb)
      (show 0 < 2 * Real.log x - b - 99 / 100 by linarith)
    nlinarith
  have hlogratio := Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)
  have heq : eta (x / 2) = (5 / (4 * Real.log 6)) * (Real.log x - b) ^ 2 + 9 := by
    dsimp [eta, b]
    rw [Real.log_div hx.ne' (by norm_num : (2 : ℝ) ≠ 0), log_six_eq, hlogratio]
    ring
  rw [heq]
  have hmul := mul_le_mul_of_nonneg_right reciprocal_log_six_upper.le
    (sq_nonneg (Real.log x - b))
  nlinarith

theorem freshG_log_lower_of_rlog (rlog : FreshLogLowerBound) {n : ℕ} (hn : 1024 ≤ n) :
    freshG (Real.log (n : ℝ)) * n < (freshCount n : ℝ) * Real.log n := by
  have hnreal : (1024 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hL : 6 ≤ Real.log (n : ℝ) := log_1024_bounds.1.le.trans
    (Real.log_le_log (by norm_num) hnreal)
  have he := eta_half_lt_freshW hnpos hL
  have hg := freshG_log_mul hnpos
  have hr := rlog n (by omega)
  have hm : (46 / 125 : ℝ) * n < (2 / 5) * mu1 * n := by
    have h := mul_pos (sub_pos.mpr mu1_lower) hnpos
    nlinarith
  dsimp [freshW] at hg
  linarith

theorem freshCount_gt_div_thirty_of_rlog (rlog : FreshLogLowerBound) {n : ℕ}
    (hlo : 1024 ≤ n) (hhi : n ≤ 32768) : (n : ℝ) / 30 < freshCount n := by
  have hnlo : (1024 : ℝ) ≤ n := by exact_mod_cast hlo
  have hnhi : (n : ℝ) ≤ 32768 := by exact_mod_cast hhi
  have hnpos : (0 : ℝ) < n := by linarith
  have hloglo := Real.log_le_log (by norm_num : (0 : ℝ) < 1024) hnlo
  have hloghi := Real.log_le_log hnpos hnhi
  have hg := freshG_gt_linear hloglo hloghi
  have hb := freshG_log_lower_of_rlog rlog hlo
  have hmul := mul_lt_mul_of_pos_right hg hnpos
  have hLpos : 0 < Real.log (n : ℝ) := by linarith [log_1024_bounds.1]
  apply (mul_lt_mul_iff_left₀ hLpos).mp
  nlinarith

theorem freshCount_gt_log_of_rlog (rlog : FreshLogLowerBound) {n : ℕ}
    (hn : 32768 ≤ n) : 7 * (n : ℝ) / (20 * Real.log n) < freshCount n := by
  have hnreal : (32768 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hloglo := Real.log_le_log (by norm_num : (0 : ℝ) < 32768) hnreal
  have hg := freshG_gt_seven_twentieths hloglo
  have hb := freshG_log_lower_of_rlog rlog (by omega : 1024 ≤ n)
  have hmul := mul_lt_mul_of_pos_right hg hnpos
  have hLpos : 0 < Real.log (n : ℝ) := by linarith [log_32768_bounds.1]
  apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 20) hLpos)).mpr
  nlinarith

/-- The elementary tangent bound also proves the final comparison with the square root. -/
theorem log_lt_seven_twentieths_sqrt {x : ℝ} (hx : 32768 ≤ x) :
    Real.log x < (7 / 20) * Real.sqrt x := by
  have hxpos : 0 < x := by linarith
  have hL := Real.log_le_log (by norm_num : (0 : ℝ) < 32768) hx
  have hs : (180 : ℝ) < Real.sqrt 32768 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hpos : 0 < 1 + (Real.log x - Real.log 32768) / 2 := by linarith
  have hexp := Real.add_one_le_exp ((Real.log x - Real.log 32768) / 2)
  have hid : Real.sqrt x = Real.sqrt 32768 * Real.exp ((Real.log x - Real.log 32768) / 2) := by
    rw [sqrt_eq_exp_half_log hxpos, sqrt_eq_exp_half_log (by norm_num : (0 : ℝ) < 32768),
      ← Real.exp_add]
    congr 1
    ring
  have hprod := mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg (32768 : ℝ))
  have hstrict := mul_lt_mul_of_pos_right hs hpos
  rw [← hid] at hprod
  have hgrowth := hstrict.trans_le (by simpa only [add_comm] using hprod)
  nlinarith [log_32768_bounds.2]

theorem freshCount_gt_sqrt_of_rlog (rlog : FreshLogLowerBound) {n : ℕ}
    (hn : 1024 ≤ n) : Real.sqrt (n : ℝ) < freshCount n := by
  have hnreal : (1024 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hsq := Real.sq_sqrt hnpos.le
  by_cases hsmall : n ≤ 32768
  · have h := freshCount_gt_div_thirty_of_rlog rlog hn hsmall
    have hs : (32 : ℝ) ≤ Real.sqrt n := by
      have h := Real.sqrt_le_sqrt hnreal
      have hs1024 : Real.sqrt (1024 : ℝ) = 32 :=
        (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num)
      simpa [hs1024] using h
    have hcomp : Real.sqrt (n : ℝ) < (n : ℝ) / 30 := by nlinarith
    exact hcomp.trans h
  · have hlarge : 32768 ≤ n := by omega
    have hnlarge : (32768 : ℝ) ≤ n := by exact_mod_cast hlarge
    have hlog := log_lt_seven_twentieths_sqrt hnlarge
    have hLpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hm := mul_pos (Real.sqrt_pos.mpr hnpos) (sub_pos.mpr hlog)
    have hcomp : Real.sqrt (n : ℝ) < 7 * (n : ℝ) / (20 * Real.log n) := by
      apply (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 20) hLpos)).mpr
      nlinarith
    exact hcomp.trans (freshCount_gt_log_of_rlog rlog hlarge)

theorem nat_sqrt_lt_freshCount_of_rlog (rlog : FreshLogLowerBound) {n : ℕ}
    (hn : 1024 ≤ n) : Nat.sqrt n < freshCount n := by
  have h : (Nat.sqrt n : ℝ) < (freshCount n : ℝ) :=
    Real.nat_sqrt_le_real_sqrt.trans_lt (freshCount_gt_sqrt_of_rlog rlog hn)
  exact_mod_cast h

end Pilz.Chebyshev


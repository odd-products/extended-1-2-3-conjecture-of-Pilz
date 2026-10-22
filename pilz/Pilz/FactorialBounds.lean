import Pilz.ChebyshevKernel
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp

/-!
# The paper's elementary log-factorial estimates

The upper estimate uses the trapezoidal lower bound for the integral of
the concave logarithm. The lower estimate uses its tangent line on a
unit interval centred at each positive integer. These are exactly the
two concavity arguments in the factorial paragraph of Section 5.
-/

noncomputable section

namespace Pilz.Chebyshev

open MeasureTheory

def entropy (x : ℝ) : ℝ := x * Real.log x - x

theorem integral_log_entropy (a b : ℝ) :
    (∫ x in a..b, Real.log x) = entropy b - entropy a := by
  rw [integral_log]
  unfold entropy
  ring

private theorem integral_affine (a b c d : ℝ) :
    (∫ x in a..b, c * x + d) = c * (b ^ 2 - a ^ 2) / 2 + d * (b - a) := by
  have hf : IntervalIntegrable (fun x : ℝ => c * x) volume a b :=
    (show Continuous (fun x : ℝ => c * x) by fun_prop).intervalIntegrable a b
  have hg : IntervalIntegrable (fun _ : ℝ => d) volume a b :=
    continuous_const.intervalIntegrable a b
  rw [intervalIntegral.integral_add hf hg,
    intervalIntegral.integral_const_mul, integral_id,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem entropy_mono_one {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    entropy a ≤ entropy b := by
  have hnonneg : 0 ≤ ∫ x in a..b, Real.log x := by
    apply intervalIntegral.integral_nonneg hab
    intro x hx
    exact Real.log_nonneg (ha.trans hx.1)
  rw [integral_log_entropy] at hnonneg
  linarith

theorem entropy_diff_le_log_right {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    entropy b - entropy a ≤ (b - a) * Real.log b := by
  have hi := intervalIntegral.integral_mono_on hab intervalIntegral.intervalIntegrable_log'
    (continuous_const.intervalIntegrable a b) (fun x hx =>
      Real.log_le_log (by linarith [hx.1]) hx.2)
  rw [integral_log_entropy, intervalIntegral.integral_const] at hi
  simpa only [smul_eq_mul] using hi

/-- Integrating the tangent line to log at the centre of a unit interval
gives the midpoint lower bound for the factorial sum. -/
theorem entropy_center_le_log {c : ℝ} (hc : 1 ≤ c) :
    entropy (c + 1 / 2) - entropy (c - 1 / 2) ≤ Real.log c := by
  have hcpos : 0 < c := by linarith
  have hpoint : ∀ x ∈ Set.Icc (c - 1 / 2) (c + 1 / 2),
      Real.log x ≤ (1 / c) * x + (Real.log c - 1) := by
    intro x hx
    have hxpos : 0 < x := by linarith [hx.1]
    have hl := Real.log_le_sub_one_of_pos (div_pos hxpos hcpos)
    rw [Real.log_div hxpos.ne' hcpos.ne'] at hl
    have heq : (1 / c) * x = x / c := by ring
    rw [heq]
    linarith
  have hint := intervalIntegral.integral_mono_on
    (show c - 1 / 2 ≤ c + 1 / 2 by linarith) intervalIntegral.intervalIntegrable_log'
    (((continuous_const.mul continuous_id).add continuous_const).intervalIntegrable
      (c - 1 / 2) (c + 1 / 2)) hpoint
  simp only [id_eq] at hint
  rw [integral_log_entropy, integral_affine] at hint
  have heval : (1 / c) * ((c + 1 / 2) ^ 2 - (c - 1 / 2) ^ 2) / 2 +
      (Real.log c - 1) * (c + 1 / 2 - (c - 1 / 2)) = Real.log c := by
    field_simp [hcpos.ne']
    ring
  rwa [heval] at hint

/-- The chord of the concave logarithm gives the trapezoidal integral
bound on a unit interval. -/
theorem log_trapezoid_le_entropy {c : ℝ} (hc : 1 ≤ c) :
    (Real.log c + Real.log (c + 1)) / 2 ≤ entropy (c + 1) - entropy c := by
  have hcpos : 0 < c := by linarith
  have hpoint : ∀ x ∈ Set.Icc c (c + 1),
      (Real.log (c + 1) - Real.log c) * x +
        ((c + 1) * Real.log c - c * Real.log (c + 1)) ≤ Real.log x := by
    intro x hx
    have h := strictConcaveOn_log_Ioi.concaveOn.2
      (show c ∈ Set.Ioi 0 from hcpos)
      (show c + 1 ∈ Set.Ioi 0 from by change 0 < c + 1; linarith)
      (show 0 ≤ c + 1 - x by linarith [hx.2])
      (show 0 ≤ x - c by linarith [hx.1])
      (show c + 1 - x + (x - c) = 1 by ring)
    have hxid : (c + 1 - x) * c + (x - c) * (c + 1) = x := by ring
    simp only [smul_eq_mul, hxid] at h
    have heq : (Real.log (c + 1) - Real.log c) * x +
        ((c + 1) * Real.log c - c * Real.log (c + 1)) =
        (c + 1 - x) * Real.log c + (x - c) * Real.log (c + 1) := by ring
    rwa [heq]
  have hint := intervalIntegral.integral_mono_on
    (show c ≤ c + 1 by linarith)
    (((continuous_const.mul continuous_id).add continuous_const).intervalIntegrable c (c + 1))
    intervalIntegral.intervalIntegrable_log' hpoint
  simp only [id_eq] at hint
  rw [integral_affine, integral_log_entropy] at hint
  have heval : (Real.log (c + 1) - Real.log c) * ((c + 1) ^ 2 - c ^ 2) / 2 +
      ((c + 1) * Real.log c - c * Real.log (c + 1)) * (c + 1 - c) =
      (Real.log c + Real.log (c + 1)) / 2 := by ring
  rwa [heval] at hint

theorem lambdaNat_upper {n : ℕ} (hn : 1 ≤ n) :
    lambdaNat n ≤ entropy n + Real.log n / 2 + 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp [lambdaNat, entropy]
  | @succ n hn ih =>
    have hreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have htrap := log_trapezoid_le_entropy hreal
    rw [lambdaNat_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith

theorem lambdaNat_lower_center (n : ℕ) :
    entropy ((n : ℝ) + 1 / 2) - entropy (1 / 2) ≤ lambdaNat n := by
  induction n with
  | zero => simp [lambdaNat]
  | succ n ih =>
    have hc := entropy_center_le_log (c := (n : ℝ) + 1)
      (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have heq : (n : ℝ) + 1 - 1 / 2 = (n : ℝ) + 1 / 2 := by ring
    rw [heq] at hc
    rw [lambdaNat_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith

theorem entropy_half : entropy (1 / 2) = -(1 + Real.log 2) / 2 := by
  unfold entropy
  rw [Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
  ring

theorem lambdaNat_lower (n : ℕ) :
    entropy ((n : ℝ) + 1 / 2) + (1 + Real.log 2) / 2 ≤ lambdaNat n := by
  have h := lambdaNat_lower_center n
  rw [entropy_half] at h
  linarith

/-- The exact lower factorial estimate stated in the paper. -/
theorem lambda_lower {t : ℝ} (ht : 1 ≤ t) :
    entropy t - Real.log t / 2 + (1 + Real.log 2) / 2 ≤ lambda t := by
  let k := ⌊t⌋₊
  have hk : 1 ≤ k := by
    exact (Nat.one_le_floor_iff t).mpr ht
  have hkle : (k : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hkt : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have hdiff : entropy t - entropy ((k : ℝ) + 1 / 2) ≤ Real.log t / 2 := by
    by_cases htc : t ≤ (k : ℝ) + 1 / 2
    · have hm := entropy_mono_one ht htc
      linarith
    · have hct : (k : ℝ) + 1 / 2 ≤ t := by linarith
      have hd := entropy_diff_le_log_right (a := (k : ℝ) + 1 / 2)
        (b := t) (by linarith) hct
      have hmul := mul_le_mul_of_nonneg_right
        (show t - ((k : ℝ) + 1 / 2) ≤ 1 / 2 by linarith) hlog
      nlinarith
  have hl := lambdaNat_lower k
  change _ ≤ lambdaNat k
  linarith

/-- The exact upper factorial estimate stated in the paper. -/
theorem lambda_upper {t : ℝ} (ht : 1 ≤ t) :
    lambda t ≤ entropy t + Real.log t / 2 + 1 := by
  let k := ⌊t⌋₊
  have hk : 1 ≤ k := (Nat.one_le_floor_iff t).mpr ht
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkle : (k : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hm := entropy_mono_one hkreal hkle
  have hlog := Real.log_le_log (by linarith : (0 : ℝ) < k) hkle
  have hu := lambdaNat_upper hk
  change lambdaNat k ≤ _
  linarith

end Pilz.Chebyshev


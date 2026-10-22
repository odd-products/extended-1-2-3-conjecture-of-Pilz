import Pilz.FactorialBounds
import Pilz.LogConstants

/-!
# Explicit estimates for Chebyshev's factorial combination

These are the two inequalities labelled Xi in the paper, with
the same constants and the same five factorials.
-/

noncomputable section

namespace Pilz.Chebyshev

theorem entropy_combination {x : ℝ} (hx : 0 < x) :
    entropy x - entropy (x / 2) - entropy (x / 3) - entropy (x / 5) +
      entropy (x / 30) = mu1 * x := by
  unfold entropy mu1
  rw [Real.log_div hx.ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div hx.ne' (by norm_num : (3 : ℝ) ≠ 0),
    Real.log_div hx.ne' (by norm_num : (5 : ℝ) ≠ 0),
    Real.log_div hx.ne' (by norm_num : (30 : ℝ) ≠ 0), log_thirty_eq]
  ring

theorem log_combination {x : ℝ} (hx : 0 < x) :
    Real.log x + Real.log (x / 2) + Real.log (x / 3) +
      Real.log (x / 5) + Real.log (x / 30) =
      5 * Real.log x - 2 * Real.log 30 := by
  rw [Real.log_div hx.ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div hx.ne' (by norm_num : (3 : ℝ) ≠ 0),
    Real.log_div hx.ne' (by norm_num : (5 : ℝ) ≠ 0),
    Real.log_div hx.ne' (by norm_num : (30 : ℝ) ≠ 0), log_thirty_eq]
  ring

theorem xi_lower {x : ℝ} (hx : 30 ≤ x) :
    mu1 * x - 5 / 2 * Real.log x + Real.log 60 - 2 ≤ xi x := by
  have hxpos : 0 < x := by linarith
  have h1 := lambda_lower (t := x) (by linarith)
  have h2 := lambda_upper (t := x / 2) (by linarith)
  have h3 := lambda_upper (t := x / 3) (by linarith)
  have h5 := lambda_upper (t := x / 5) (by linarith)
  have h30 := lambda_lower (t := x / 30) (by linarith)
  have he := entropy_combination hxpos
  have hl := log_combination hxpos
  have hc : Real.log 60 = Real.log 30 + Real.log 2 := by
    rw [log_sixty_eq, log_thirty_eq]
    ring
  unfold xi
  linarith

theorem xi_upper {x : ℝ} (hx : 30 ≤ x) :
    xi x ≤ mu1 * x + 5 / 2 * Real.log x - Real.log 30 +
      (1 - 3 * Real.log 2) / 2 := by
  have hxpos : 0 < x := by linarith
  have h1 := lambda_upper (t := x) (by linarith)
  have h2 := lambda_lower (t := x / 2) (by linarith)
  have h3 := lambda_lower (t := x / 3) (by linarith)
  have h5 := lambda_lower (t := x / 5) (by linarith)
  have h30 := lambda_upper (t := x / 30) (by linarith)
  have he := entropy_combination hxpos
  have hl := log_combination hxpos
  unfold xi
  linarith

theorem mu1_lower : (23 : ℝ) / 25 < mu1 := by
  simpa only [mu1] using mu1_numeric

theorem mu1_pos : 0 < mu1 := lt_trans (by norm_num) mu1_lower

theorem psi_lower {x : ℝ} (hx : 30 ≤ x) :
    mu1 * x - 5 / 2 * Real.log x + 2 < psi x := by
  have h := xi_lower hx
  have hp := xi_le_psi x
  linarith [log_sixty_constant]

theorem xi_upper_simplified {x : ℝ} (hx : 30 ≤ x) :
    xi x < mu1 * x + 5 / 2 * Real.log x - 3 := by
  have h := xi_upper hx
  linarith [log_thirty_constant]

end Pilz.Chebyshev

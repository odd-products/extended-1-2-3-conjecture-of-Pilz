import Pilz.ChebyshevXi
import Pilz.ChebyshevLcm
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Iterating the Chebyshev combination

The finite scale-six iteration and the completed square are kept explicit,
as in the proof's upper-bound paragraph.
-/

noncomputable section

namespace Pilz.Chebyshev

theorem log_scale_six {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Real.log ((6 : ℝ) ^ k * t) = (k : ℝ) * Real.log 6 + Real.log t := by
  rw [Real.log_mul (pow_ne_zero _ (by norm_num)) ht.ne', Real.log_pow]

theorem psi_scale_six (t : ℝ) (ht : 5 ≤ t) (k : ℕ) :
    psi ((6 : ℝ) ^ k * t) ≤ psi t + mu2 * ((6 : ℝ) ^ k * t - t) +
      (5 / 2 * (k : ℝ) * Real.log t +
        5 / 4 * Real.log 6 * (k : ℝ) * ((k : ℝ) + 1) - 3 * (k : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkpow : 1 ≤ (6 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have hx : 30 ≤ (6 : ℝ) ^ (k + 1) * t := by
      rw [pow_succ]
      nlinarith
    have hrec := psi_sub_sixth_le_xi ((6 : ℝ) ^ (k + 1) * t)
    have hup := xi_upper_simplified hx
    have hdiv : (6 : ℝ) ^ (k + 1) * t / 6 = (6 : ℝ) ^ k * t := by
      rw [pow_succ]
      ring
    rw [hdiv] at hrec
    rw [log_scale_six (by linarith : 0 < t)] at hup
    simp only [Nat.cast_add, Nat.cast_one] at hup ⊢
    simp only [pow_succ, mu2] at ih hrec hup ⊢
    nlinarith

theorem exists_scale_six {x : ℝ} (hx : 5 ≤ x) :
    ∃ k : ℕ, ∃ t : ℝ, 5 ≤ t ∧ t < 30 ∧ x = (6 : ℝ) ^ k * t := by
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near
    (x := x / 5) (y := (6 : ℝ)) (by linarith) (by norm_num)
  refine ⟨k, x / (6 : ℝ) ^ k, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 6) k)).mpr
    linarith
  · apply (div_lt_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 6) k)).mpr
    rw [pow_succ] at hk'
    linarith
  · field_simp

theorem iteration_completed_square (x : ℝ) (k : ℕ) :
    -(5 / 4 : ℝ) * Real.log 6 * (k : ℝ) ^ 2 +
      (5 / 2 * Real.log x + 5 / 4 * Real.log 6 - 3) * (k : ℝ) ≤
      5 / (4 * Real.log 6) * (Real.log x + Real.log 6 / 2 - 6 / 5) ^ 2 := by
  have hL : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
  have hid :
      5 / (4 * Real.log 6) * (Real.log x + Real.log 6 / 2 - 6 / 5) ^ 2 -
        (-(5 / 4 : ℝ) * Real.log 6 * (k : ℝ) ^ 2 +
          (5 / 2 * Real.log x + 5 / 4 * Real.log 6 - 3) * (k : ℝ)) =
      5 / (4 * Real.log 6) *
        (Real.log x + Real.log 6 / 2 - 6 / 5 - Real.log 6 * (k : ℝ)) ^ 2 := by
    field_simp
    ring
  have hn : 0 ≤ 5 / (4 * Real.log 6) *
      (Real.log x + Real.log 6 / 2 - 6 / 5 - Real.log 6 * (k : ℝ)) ^ 2 := by
    positivity
  linarith

theorem psi_upper_from_small_bound
    (hsmall : ∀ t : ℝ, 5 ≤ t → t < 30 → psi t < t * Real.log 4)
    {x : ℝ} (hx : 5 ≤ x) : psi x < mu2 * x + eta x := by
  obtain ⟨k, t, ht, ht', hxt⟩ := exists_scale_six hx
  have hi := psi_scale_six t ht k
  have hl := log_scale_six (by linarith : 0 < t) k
  rw [← hxt] at hi hl
  have hc := iteration_completed_square x k
  have hlogfour : Real.log (4 : ℝ) < 7 / 5 := by
    have hid : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      calc
        Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
        _ = _ := Real.log_pow _ _
    rw [hid]
    linarith [log_two_upper_seven_tenths]
  have htail : psi t - mu2 * t < 9 := by
    have hb := hsmall t ht ht'
    have hm := mu1_lower
    unfold mu2
    nlinarith
  unfold eta
  nlinarith

theorem psi_upper {x : ℝ} (hx : 5 ≤ x) : psi x < mu2 * x + eta x := by
  apply psi_upper_from_small_bound ?_ hx
  intro t ht _
  exact psi_lt_mul_log_four (by linarith)

end Pilz.Chebyshev


import Pilz.PrimePowerBounds
import Pilz.FreshLargeReal

/-!
# The Chebyshev lower bound for fresh prime counts

This joins the independently checked factorial, prime-power, and calculus
parts of the manuscript's argument.
-/

noncomputable section

namespace Pilz.Chebyshev

theorem freshLogLowerBound : FreshLogLowerBound := by
  intro n hn
  have hnreal : (256 : ℝ) ≤ n := by exact_mod_cast hn
  have hlo := psi_lower (x := (n : ℝ)) (by linarith)
  have hup := psi_upper (x := (n : ℝ) / 2) (by linarith)
  have herr := psiNat_sub_thetaNat_lt hn
  have hhalf := thetaNat_le_psiNat (n / 2)
  have hcount := thetaNat_sub_le_freshCount_mul_log (n := n) (by omega)
  simp only [psi, Nat.floor_natCast] at hlo
  simp only [psi, Nat.floor_div_ofNat, Nat.floor_natCast] at hup
  unfold mu2 at hup
  nlinarith

theorem freshCount_gt_div_thirty {n : ℕ} (hlo : 1024 ≤ n) (hhi : n ≤ 32768) :
    (n : ℝ) / 30 < freshCount n :=
  freshCount_gt_div_thirty_of_rlog freshLogLowerBound hlo hhi

theorem freshCount_gt_log {n : ℕ} (hn : 32768 ≤ n) :
    7 * (n : ℝ) / (20 * Real.log n) < freshCount n :=
  freshCount_gt_log_of_rlog freshLogLowerBound hn

theorem freshCount_gt_sqrt {n : ℕ} (hn : 1024 ≤ n) :
    Real.sqrt n < freshCount n :=
  freshCount_gt_sqrt_of_rlog freshLogLowerBound hn

theorem nat_sqrt_lt_freshCount {n : ℕ} (hn : 1024 ≤ n) :
    Nat.sqrt n < freshCount n :=
  nat_sqrt_lt_freshCount_of_rlog freshLogLowerBound hn

end Pilz.Chebyshev

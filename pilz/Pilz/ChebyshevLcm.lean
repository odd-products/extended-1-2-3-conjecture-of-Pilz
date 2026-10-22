import Pilz.ChebyshevKernel
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.ModEq

/-!
# The elementary bound `psi(t) < t log 4`

The manuscript expresses this as a bound on `lcm(1,...,n)` and proves it
by central binomial coefficients. We use the equivalent logarithmic
argument directly: the binomial factorial combination covers every
prime-power contribution above the midpoint. This uses the same
Legendre/binomial mechanism and avoids introducing a second encoding of
the prime-power sum.
-/

noncomputable section

namespace Pilz.Chebyshev

open scoped BigOperators ArithmeticFunction.vonMangoldt
open Finset

theorem log_choose_eq_lambda (n k : ℕ) (hk : k ≤ n) :
    Real.log (n.choose k : ℝ) = lambdaNat n - lambdaNat k - lambdaNat (n - k) := by
  have hc : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have hkf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hrf : ((n - k).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - k)
  have heq : (n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ) =
      (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hlog := congrArg Real.log heq
  rw [Real.log_mul (mul_ne_zero hc hkf) hrf, Real.log_mul hc hkf] at hlog
  unfold lambdaNat
  linarith

private theorem psiNat_padded {k n : ℕ} (hkn : k ≤ n) :
    psiNat k = ∑ d ∈ Icc 1 n, if d ≤ k then Λ d else 0 := by
  have heq : (Icc 1 n).filter (fun d => d ≤ k) = Icc 1 k := by
    ext d
    simp only [mem_filter, mem_Icc]
    omega
  rw [← sum_filter, heq]
  rfl

/-- The factorial/binomial contribution covers every prime power above `n-k`. -/
theorem psiNat_sub_le_log_choose (n k : ℕ) (hk : k ≤ n) (hhalf : k ≤ n - k) :
    psiNat n - psiNat (n - k) ≤ Real.log (n.choose k : ℝ) := by
  rw [log_choose_eq_lambda n k hk, psiNat_padded (Nat.sub_le n k)]
  unfold psiNat
  rw [lambdaNat_legendre n, lambdaNat_legendre_padded hk,
    lambdaNat_legendre_padded (Nat.sub_le n k), ← sum_sub_distrib,
    ← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_le_sum
  intro d hd
  by_cases hsmall : d ≤ n - k
  · rw [if_pos hsmall, sub_self]
    have hnat := Nat.add_div_le_add_div k (n - k) d
    rw [Nat.add_sub_of_le hk] at hnat
    have hreal : ((k / d : ℕ) : ℝ) + (((n - k) / d : ℕ) : ℝ) ≤ ((n / d : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hnonneg := mul_nonneg (sub_nonneg.mpr hreal)
      (ArithmeticFunction.vonMangoldt_nonneg (n := d))
    nlinarith
  · rw [if_neg hsmall, sub_zero]
    have hrlt : n - k < d := by omega
    have hklt : k < d := hhalf.trans_lt hrlt
    rw [Nat.div_eq_of_lt hklt, Nat.div_eq_of_lt hrlt]
    simp only [Nat.cast_zero, zero_mul, sub_zero]
    have hdiv : 1 ≤ n / d := Nat.div_pos (mem_Icc.mp hd).2 (mem_Icc.mp hd).1
    have hreal : (1 : ℝ) ≤ ((n / d : ℕ) : ℝ) := by exact_mod_cast hdiv
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hreal ArithmeticFunction.vonMangoldt_nonneg

theorem log_choose_le_pred_mul_log_two (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    Real.log (n.choose k : ℝ) ≤ ((n - 1 : ℕ) : ℝ) * Real.log 2 := by
  have hnat : n.choose k ≤ 2 ^ (n - 1) := by
    have h := Nat.choose_succ_le_two_pow (n - 1) k
    simpa [Nat.sub_add_cancel hn] using h
  have hreal : (n.choose k : ℝ) ≤ (2 : ℝ) ^ (n - 1) := by exact_mod_cast hnat
  have hpos : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  have hlog := Real.log_le_log hpos hreal
  simpa only [Real.log_pow] using hlog

/-- The natural-number form of the manuscript's elementary lcm bound. -/
theorem psiNat_lt_mul_log_four (n : ℕ) (hn : 0 < n) :
    psiNat n < (n : ℝ) * Real.log 4 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n = 1
    · subst n
      simpa [psiNat] using Real.log_pos (show (1 : ℝ) < 4 by norm_num)
    have hn2 : 2 ≤ n := by omega
    let k := n / 2
    let r := n - k
    have hk : k ≤ n := Nat.div_le_self n 2
    have hhalf : k ≤ n - k := by dsimp [k]; omega
    have hrpos : 0 < r := by dsimp [r, k]; omega
    have hrlt : r < n := by dsimp [r, k]; omega
    have hrec := psiNat_sub_le_log_choose n k hk hhalf
    have hchoose := log_choose_le_pred_mul_log_two n k hn hk
    have hsmaller := ih r hrlt hrpos
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      have h := Real.log_pow (2 : ℝ) 2
      norm_num at h
      exact h
    have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hcoeff : 2 * r + (n - 1) ≤ 2 * n := by dsimp [r, k]; omega
    have hcoeffreal : 2 * (r : ℝ) + ((n - 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
      exact_mod_cast hcoeff
    have hmul := mul_le_mul_of_nonneg_right hcoeffreal hlog2pos.le
    rw [hlog4] at hsmaller ⊢
    change psiNat n - psiNat r ≤ _ at hrec
    nlinarith

/-- The uniform real-variable form used twice in the Chebyshev argument. -/
theorem psi_lt_mul_log_four {t : ℝ} (ht : 1 ≤ t) : psi t < t * Real.log 4 := by
  have hfloor : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr ht
  have hnat := psiNat_lt_mul_log_four ⌊t⌋₊ (by omega)
  have hfloorle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hlog : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  exact hnat.trans_le (mul_le_mul_of_nonneg_right hfloorle hlog.le)

end Pilz.Chebyshev

import Pilz.PrimeCounts
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Chebyshev's factorial combination and its periodic floor kernel

This file follows the elementary Chebyshev argument in the journal paper.
The von Mangoldt function is simply a convenient encoding of the finite
sum over prime powers, and its divisor-sum identity supplies Legendre's
log-factorial formula.
-/

noncomputable section

namespace Pilz.Chebyshev

open scoped BigOperators ArithmeticFunction.vonMangoldt
open Finset

def lambdaNat (n : ℕ) : ℝ := Real.log (n.factorial : ℝ)
def lambda (x : ℝ) : ℝ := lambdaNat ⌊x⌋₊
def psiNat (n : ℕ) : ℝ := ∑ d ∈ Icc 1 n, Λ d
def thetaNat (n : ℕ) : ℝ := ∑ p ∈ Icc 1 n, if p.Prime then Real.log (p : ℝ) else 0
def psi (x : ℝ) : ℝ := psiNat ⌊x⌋₊
def theta (x : ℝ) : ℝ := thetaNat ⌊x⌋₊

def mu1 : ℝ := (14 * Real.log 2 + 9 * Real.log 3 + 5 * Real.log 5) / 30
def mu2 : ℝ := 6 / 5 * mu1
def eta (x : ℝ) : ℝ :=
  5 / (4 * Real.log 6) * (Real.log x + Real.log 6 / 2 - 6 / 5) ^ 2 + 9

def xiNat (n : ℕ) : ℝ :=
  lambdaNat n - lambdaNat (n / 2) - lambdaNat (n / 3) - lambdaNat (n / 5) + lambdaNat (n / 30)

def xi (x : ℝ) : ℝ :=
  lambda x - lambda (x / 2) - lambda (x / 3) - lambda (x / 5) + lambda (x / 30)

/-- The paper's floor kernel, evaluated on an integer. Integer subtraction
avoids the truncation that natural-number subtraction would introduce. -/
def floorKernel (n : ℕ) : ℤ :=
  (n : ℤ) - (n / 2 : ℕ) - (n / 3 : ℕ) - (n / 5 : ℕ) + (n / 30 : ℕ)

theorem floorKernel_mod (n : ℕ) : floorKernel n = floorKernel (n % 30) := by
  unfold floorKernel
  omega

theorem floorKernel_periodic (n : ℕ) : floorKernel (n + 30) = floorKernel n := by
  rw [floorKernel_mod (n + 30), floorKernel_mod n]
  congr 1
  omega

private theorem floorKernel_table :
    ∀ n : Fin 30, 0 ≤ floorKernel n.val ∧ floorKernel n.val ≤ 1 := by decide

theorem floorKernel_bounds (n : ℕ) : 0 ≤ floorKernel n ∧ floorKernel n ≤ 1 := by
  rw [floorKernel_mod]
  exact floorKernel_table ⟨n % 30, Nat.mod_lt n (by decide)⟩

theorem floorKernel_eq_one {n : ℕ} (hn : 1 ≤ n) (hn' : n < 6) : floorKernel n = 1 := by
  unfold floorKernel
  omega

theorem psiNat_nonneg (n : ℕ) : 0 ≤ psiNat n := by
  exact Finset.sum_nonneg (fun d _ => ArithmeticFunction.vonMangoldt_nonneg)

theorem thetaNat_le_psiNat (n : ℕ) : thetaNat n ≤ psiNat n := by
  apply Finset.sum_le_sum
  intro p hp
  by_cases hprime : p.Prime
  · rw [if_pos hprime, ArithmeticFunction.vonMangoldt_apply_prime hprime]
  · rw [if_neg hprime]
    exact ArithmeticFunction.vonMangoldt_nonneg

theorem lambdaNat_succ (n : ℕ) :
    lambdaNat (n + 1) = lambdaNat n + Real.log (n + 1 : ℝ) := by
  rw [lambdaNat, Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast Nat.succ_ne_zero n)
      (by exact_mod_cast Nat.factorial_ne_zero n)]
  simp only [lambdaNat, Nat.cast_add, Nat.cast_one]
  ring

/-- Legendre's formula, with the prime powers grouped by their value. -/
theorem lambdaNat_legendre (n : ℕ) :
    lambdaNat n = ∑ d ∈ Icc 1 n, ((n / d : ℕ) : ℝ) * Λ d := by
  induction n with
  | zero => simp [lambdaNat]
  | succ n ih =>
    have hold : (∑ d ∈ Icc 1 (n + 1), ((n / d : ℕ) : ℝ) * Λ d) =
        ∑ d ∈ Icc 1 n, ((n / d : ℕ) : ℝ) * Λ d := by
      rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n))]
      simp [Nat.div_eq_of_lt (Nat.lt_succ_self n)]
    have hdiv : (∑ d ∈ (n + 1).divisors, Λ d) =
        ∑ d ∈ Icc 1 (n + 1), if d ∣ n + 1 then Λ d else 0 := by
      rw [Nat.divisors, Finset.Ico_add_one_right_eq_Icc, Finset.sum_filter]
    have hlog : Real.log (n + 1 : ℝ) = ∑ d ∈ (n + 1).divisors, Λ d := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (ArithmeticFunction.vonMangoldt_sum (n := n + 1)).symm
    rw [lambdaNat_succ, ih, hlog, hdiv, ← hold,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.succ_div]
    split_ifs <;> push_cast <;> ring

theorem lambdaNat_legendre_padded {k n : ℕ} (hkn : k ≤ n) :
    lambdaNat k = ∑ d ∈ Icc 1 n, ((k / d : ℕ) : ℝ) * Λ d := by
  rw [lambdaNat_legendre]
  apply Finset.sum_subset
  · intro d hd
    obtain ⟨hd1, hdk⟩ := Finset.mem_Icc.mp hd
    exact Finset.mem_Icc.mpr ⟨hd1, hdk.trans hkn⟩
  · intro d hdn hdk
    have hkd : k < d := by
      have hd1 := (Finset.mem_Icc.mp hdn).1
      simp only [Finset.mem_Icc] at hdk
      omega
    simp [Nat.div_eq_of_lt hkd]

/-- The factorial combination is the convolution with the periodic kernel. -/
theorem xiNat_eq_sum_floorKernel (n : ℕ) :
    xiNat n = ∑ d ∈ Icc 1 n, (floorKernel (n / d) : ℝ) * Λ d := by
  unfold xiNat
  rw [lambdaNat_legendre n,
    lambdaNat_legendre_padded (Nat.div_le_self n 2),
    lambdaNat_legendre_padded (Nat.div_le_self n 3),
    lambdaNat_legendre_padded (Nat.div_le_self n 5),
    lambdaNat_legendre_padded (Nat.div_le_self n 30),
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have h2 : n / 2 / d = n / d / 2 := by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have h3 : n / 3 / d = n / d / 3 := by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have h5 : n / 5 / d = n / d / 5 := by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have h30 : n / 30 / d = n / d / 30 := by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [h2, h3, h5, h30]
  unfold floorKernel
  simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast]
  ring

theorem xiNat_nonneg (n : ℕ) : 0 ≤ xiNat n := by
  rw [xiNat_eq_sum_floorKernel]
  apply Finset.sum_nonneg
  intro d hd
  exact mul_nonneg (by exact_mod_cast (floorKernel_bounds (n / d)).1)
    ArithmeticFunction.vonMangoldt_nonneg

theorem xiNat_le_psiNat (n : ℕ) : xiNat n ≤ psiNat n := by
  rw [xiNat_eq_sum_floorKernel]
  apply Finset.sum_le_sum
  intro d hd
  have hk : (floorKernel (n / d) : ℝ) ≤ 1 := by
    exact_mod_cast (floorKernel_bounds (n / d)).2
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hk
    ArithmeticFunction.vonMangoldt_nonneg

private theorem psiNat_eq_sum_indicator {k n : ℕ} (hkn : k ≤ n) :
    psiNat k = ∑ d ∈ Icc 1 n, if d ≤ k then Λ d else 0 := by
  have heq : (Icc 1 n).filter (fun d => d ≤ k) = Icc 1 k := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [← Finset.sum_filter, heq]
  rfl

theorem psiNat_sub_sixth_le_xiNat (n : ℕ) :
    psiNat n - psiNat (n / 6) ≤ xiNat n := by
  rw [psiNat_eq_sum_indicator (Nat.div_le_self n 6), xiNat_eq_sum_floorKernel]
  unfold psiNat
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro d hd
  by_cases hsmall : d ≤ n / 6
  · rw [if_pos hsmall, sub_self]
    exact mul_nonneg (by exact_mod_cast (floorKernel_bounds (n / d)).1)
      ArithmeticFunction.vonMangoldt_nonneg
  · rw [if_neg hsmall, sub_zero]
    obtain ⟨hdpos, hdn⟩ := Finset.mem_Icc.mp hd
    have hlow : 1 ≤ n / d := Nat.div_pos hdn hdpos
    have hupper : n / d < 6 := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < d)).mpr
      omega
    rw [floorKernel_eq_one hlow hupper]
    simp

theorem xi_eq_xiNat_floor (x : ℝ) : xi x = xiNat ⌊x⌋₊ := by
  simp only [xi, xiNat, lambda, Nat.floor_div_ofNat]

theorem xi_le_psi (x : ℝ) : xi x ≤ psi x := by
  rw [xi_eq_xiNat_floor]
  exact xiNat_le_psiNat _

theorem psi_sub_sixth_le_xi (x : ℝ) : psi x - psi (x / 6) ≤ xi x := by
  rw [xi_eq_xiNat_floor]
  simp only [psi, Nat.floor_div_ofNat]
  exact psiNat_sub_sixth_le_xiNat _

end Pilz.Chebyshev

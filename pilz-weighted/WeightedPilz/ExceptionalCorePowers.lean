import WeightedPilz.Arithmetic.ExceptionalPowerProducts
import WeightedPilz.UniqueProductCoefficients
import Mathlib.Tactic.NormNum

/-! The weighted cubic and quartic core bounds in the higher-degree exceptions.
Unique multiplicative power products give an independent proof of the frozen
bounds, without assumptions on the nonzero coefficients beyond their weights. -/

namespace WeightedPilz
variable {K : Type*} [Field K]

private theorem factorial_three_ne_zero (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    (Nat.factorial 3 : K) ≠ 0 := by
  have h : (Nat.factorial 3 : K) = (2 : K) * 3 := by norm_num [Nat.factorial]
  rw [h]
  exact mul_ne_zero h2 h3

private theorem factorial_four_ne_zero (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    (Nat.factorial 4 : K) ≠ 0 := by
  have h : (Nat.factorial 4 : K) = (2 : K) * 2 * 2 * 3 := by norm_num [Nat.factorial]
  rw [h]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h3

/-- Equation (fin-cubic-bound), for every choice of nonzero core weights. -/
theorem exceptional_core_cube_weight (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 26 ≤ n) (hn' : n ≤ 28)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    44 ≤ weight (intervalCore n c ^ 3) := by
  obtain ⟨T, hTcard, hT⟩ := Arithmetic.exceptional_cube_products hn hn'
  rw [intervalCore_eq_arithmetic_core, ← hTcard]
  exact weight_pow_ge_unique_products (Arithmetic.core n) T c 3
    (fun a ha => (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1)
    (fun a ha => hc a (Finset.mem_filter.mp ha).1)
    (factorial_three_ne_zero h2 h3) (fun m hm => (hT m hm).1)
    (fun m hm => (hT m hm).2)

/-- The fifteen-term quartic contribution in the two quartic exceptions. -/
theorem exceptional_core_quartic_weight (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 27 ≤ n) (hn' : n ≤ 28)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    15 ≤ weight (intervalCore n c ^ 4) := by
  obtain ⟨T, hTcard, hT⟩ := Arithmetic.exceptional_quartic_products hn hn'
  rw [intervalCore_eq_arithmetic_core, ← hTcard]
  exact weight_pow_ge_unique_products (Arithmetic.core n) T c 4
    (fun a ha => (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1)
    (fun a ha => hc a (Finset.mem_filter.mp ha).1)
    (factorial_four_ne_zero h2 h3) (fun m hm => (hT m hm).1)
    (fun m hm => (hT m hm).2)

/-- The fifty-six-term cubic contribution at forty. -/
theorem exceptional_core_cube_weight_forty (c : ℕ → K)
    (hc : NonzeroWeights 40 c) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    56 ≤ weight (intervalCore 40 c ^ 3) := by
  obtain ⟨T, hTcard, hT⟩ := Arithmetic.exceptional_cube_products_forty
  rw [intervalCore_eq_arithmetic_core, ← hTcard]
  exact weight_pow_ge_unique_products (Arithmetic.core 40) T c 3
    (fun a ha => (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1)
    (fun a ha => hc a (Finset.mem_filter.mp ha).1)
    (factorial_three_ne_zero h2 h3) (fun m hm => (hT m hm).1)
    (fun m hm => (hT m hm).2)

end WeightedPilz

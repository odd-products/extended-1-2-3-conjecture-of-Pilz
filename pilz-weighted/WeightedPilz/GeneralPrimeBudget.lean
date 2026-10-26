import WeightedPilz.LocalizedSupport

/-! The full integer-parameter prime budget, including every threshold U ≥ 4. -/

namespace WeightedPilz.Arithmetic
open Pilz (primeCount)

theorem primeCount_odd_threshold_growth (U u : ℕ) (hU : 4 ≤ U) (hUu : U ≤ u) :
    primeCount (2 * u - 3) ≤ primeCount (2 * U - 3) + (u - U) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hUu
  induction k with
  | zero => simp
  | succ k ih =>
    have hnot : ¬ Nat.Prime ((2 * (U + k) - 3) + 1) := by
      have heq : (2 * (U + k) - 3) + 1 = 2 * (U + k - 1) := by omega
      rw [heq]
      intro hp
      rcases hp.eq_two_or_odd with heq | hodd <;> omega
    have hstep := Pilz.primeCount_succ_le ((2 * (U + k) - 3) + 1)
    rw [Pilz.primeCount_succ_eq_of_not_prime _ hnot] at hstep
    have heq : 2 * (U + (k + 1)) - 3 = ((2 * (U + k) - 3) + 1) + 1 := by omega
    rw [heq]
    omega

theorem prime_budget_arithmetic_general
    (U w u r p p₀ a b c i f₂ f₃ f₅ : ℕ)
    (hu : U ≤ u) (hr : 8 ≤ r) (hp : p ≤ p₀ + (u - U)) (hi : r ≤ i)
    (h₂ : 1 + a ≤ f₂ + p) (h₃ : 1 + b ≤ f₃ + p) (h₅ : 1 + c ≤ f₅ + p)
    (hbudget : u * i + 4 * f₂ + 2 * f₃ + 2 * f₅ ≤ w) :
    U * r + 4 * a + 2 * b + 2 * c + 8 + (u - U) * (r - 8) ≤ w + 8 * p₀ := by
  have huri : u * r ≤ u * i := Nat.mul_le_mul_left u hi
  have hsum : u * r + 4 * a + 2 * b + 2 * c + 8 ≤ w + 8 * p := by
    nlinarith
  have hpu : p + U ≤ p₀ + u := by omega
  have hproduct : U * r + 8 * u + (u - U) * (r - 8) = u * r + 8 * U := by
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hu
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
    simp only [Nat.add_sub_cancel_left]
    ring
  nlinarith

end WeightedPilz.Arithmetic

noncomputable section
namespace WeightedPilz
open Pilz (primesUpTo primeCount freshCount roughCount roughIntervalCount)
variable {K : Type*} [Field K]

/-- `arith:lem:eight-endpoint-prime-budget`, retaining the exact nonnegative surplus. -/
theorem localized_prime_budget_general_surplus (U n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hU : 4 ≤ U) (hUu : U ≤ weight D)
    (hq : 17 ≤ q) (hqn : q ≤ n / 2) (hcut : q < 2 * (weight D - 1))
    (hr : 8 ≤ freshCount n) (hD : D ≠ 0) (hnorm : Normalized D)
    (hlargest : LargestPrime D q) :
    U * freshCount n + 4 * primeCount (n / 2) + 2 * primeCount (n / 3) +
      2 * primeCount (n / 5) + 8 + (weight D - U) * (freshCount n - 8) ≤
        weight (interval n c * D) + 8 * primeCount (2 * U - 3) := by
  have hqbound : q ≤ 2 * weight D - 3 := by omega
  have hpi := (Pilz.primeCount_mono hqbound).trans
    (Arithmetic.primeCount_odd_threshold_growth U (weight D) hU hUu)
  exact Arithmetic.prime_budget_arithmetic_general U (weight (interval n c * D))
    (weight D) (freshCount n) (primeCount q) (primeCount (2 * U - 3))
    (primeCount (n / 2)) (primeCount (n / 3)) (primeCount (n / 5))
    (roughIntervalCount (primesUpTo q) n) (roughCount (primesUpTo q) (n / 2))
    (roughCount (primesUpTo q) (n / 3)) (roughCount (primesUpTo q) (n / 5))
    hUu hr hpi (Pilz.freshCount_le_roughIntervalCount n q hqn)
    (Pilz.roughCount_add_primeCount_ge q (n / 2) hlargest.1)
    (Pilz.roughCount_add_primeCount_ge q (n / 3) hlargest.1)
    (Pilz.roughCount_add_primeCount_ge q (n / 5) hlargest.1)
    (component_budget_eight q n c D hc hq hD hnorm hlargest)

theorem localized_prime_budget_general (U n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hU : 4 ≤ U) (hUu : U ≤ weight D)
    (hq : 17 ≤ q) (hqn : q ≤ n / 2) (hcut : q < 2 * (weight D - 1))
    (hr : 8 ≤ freshCount n) (hD : D ≠ 0) (hnorm : Normalized D)
    (hlargest : LargestPrime D q) :
    U * freshCount n + 4 * primeCount (n / 2) + 2 * primeCount (n / 3) +
      2 * primeCount (n / 5) + 8 ≤
        weight (interval n c * D) + 8 * primeCount (2 * U - 3) := by
  have h := localized_prime_budget_general_surplus U n q c D hc hU hUu hq hqn
    hcut hr hD hnorm hlargest
  omega

end WeightedPilz

import Pilz.PrimeCounts
import Mathlib.Data.Nat.Prime.Basic

/-!
# An elementary linear prime-count budget

Starting at `pi(17)=7`, increasing `u` by one adds the two consecutive
integers `2u-2, 2u-1` to the counting range. The first is an even composite,
so the count can increase by at most one. This is the prime-count estimate
in the paper's finite localized-support argument.
-/

namespace Pilz

/-- The exact change in prime count at one new integer. -/
theorem primeCount_succ (n : ℕ) :
    primeCount (n + 1) = primeCount n + (if Nat.Prime (n + 1) then 1 else 0) := by
  unfold primeCount
  rw [Finset.range_add_one]
  by_cases hp : Nat.Prime (n + 1)
  · simp [Finset.filter_insert, hp, Finset.mem_filter]
  · simp [Finset.filter_insert, hp]

theorem primeCount_succ_le (n : ℕ) : primeCount (n + 1) ≤ primeCount n + 1 := by
  rw [primeCount_succ]
  split_ifs <;> omega

theorem primeCount_succ_eq_of_not_prime (n : ℕ) (hn : ¬Nat.Prime (n + 1)) :
    primeCount (n + 1) = primeCount n := by
  rw [primeCount_succ, if_neg hn, Nat.add_zero]

private theorem not_prime_even {k : ℕ} (hk : 2 ≤ k) : ¬Nat.Prime (2 * k) := by
  intro hp
  rcases hp.eq_two_or_odd with heq | hodd <;> omega

/-- The paper's `pi(2u-3) <= u-3` for every `u >= 10`. -/
theorem primeCount_two_mul_sub_three (u : ℕ) (hu : 10 ≤ u) :
    primeCount (2 * u - 3) ≤ u - 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hu
  induction k with
  | zero => decide
  | succ k ih =>
    have hnot : ¬Nat.Prime ((2 * (10 + k) - 3) + 1) := by
      have heq : (2 * (10 + k) - 3) + 1 = 2 * (k + 9) := by omega
      rw [heq]
      exact not_prime_even (by omega)
    have hstep := primeCount_succ_le ((2 * (10 + k) - 3) + 1)
    rw [primeCount_succ_eq_of_not_prime _ hnot] at hstep
    have heq : 2 * (10 + (k + 1)) - 3 = ((2 * (10 + k) - 3) + 1) + 1 := by omega
    rw [heq]
    omega

/-- The directed cut confines the number of support primes relative to
the number of multiplier terms. No primality hypothesis on `q` is needed. -/
theorem primeCount_le_terms_sub_three {q u : ℕ} (hq : 17 ≤ q)
    (hcut : q < 2 * (u - 1)) : primeCount q ≤ u - 3 := by
  have hu : 10 ≤ u := by omega
  have hqbound : q ≤ 2 * u - 3 := by omega
  exact (primeCount_mono hqbound).trans (primeCount_two_mul_sub_three u hu)

end Pilz

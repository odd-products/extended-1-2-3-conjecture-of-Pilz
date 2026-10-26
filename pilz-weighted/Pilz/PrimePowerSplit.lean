import Pilz.PrimePowerSums
import Mathlib.Data.Real.Sqrt

/-!
# Grouping the even prime-power exponents

The first term of the split is the prime sum, all even exponents give
the von Mangoldt sum at the square root, and the remaining exponents
are exactly 3, 5, 7, and so on.
-/

noncomputable section

namespace Pilz.Chebyshev

open Finset
open scoped BigOperators

def oddPowerPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((primeSet n) ×ˢ range (Nat.log 2 n)).filter (fun z => z.1 ^ (2 * z.2 + 3) ≤ n)

theorem mem_oddPowerPairs {n p a : ℕ} :
    (p, a) ∈ oddPowerPairs n ↔ p.Prime ∧ p ^ (2 * a + 3) ≤ n := by
  simp only [oddPowerPairs, mem_filter, mem_product, mem_range, mem_primeSet]
  constructor
  · rintro ⟨⟨⟨hp, _⟩, _⟩, hpow⟩
    exact ⟨hp, hpow⟩
  · rintro ⟨hp, hpow⟩
    have hp_le : p ≤ n := (le_self_pow₀ hp.one_le (by omega : 2 * a + 3 ≠ 0)).trans hpow
    have htwo : 2 ^ (2 * a + 3) ≤ n :=
      (Nat.pow_le_pow_left hp.two_le (2 * a + 3)).trans hpow
    have ha := Nat.le_log_of_pow_le (by decide : 1 < 2) htwo
    exact ⟨⟨⟨hp, hp_le⟩, by omega⟩, hpow⟩

private theorem pow_even_sqrt {n p a : ℕ} :
    p ^ (2 * a + 1 + 1) ≤ n ↔ p ^ (a + 1) ≤ n.sqrt := by
  have heq : p ^ (2 * a + 1 + 1) = (p ^ (a + 1)) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [heq, Nat.le_sqrt']

private theorem sum_zero_exponent (n : ℕ) :
    (∑ z ∈ (primePowerPairs n).filter (fun z => z.2 = 0), Real.log (z.1 : ℝ)) =
      thetaNat n := by
  rw [thetaNat_eq_sum_primes]
  symm
  apply sum_bij (fun p _ => (p, 0))
  · intro p hp
    exact mem_filter.mpr ⟨mem_primePowerPairs.mpr
      ⟨(mem_primeSet.mp hp).1, by simpa using (mem_primeSet.mp hp).2⟩, rfl⟩
  · intro p hp q hq heq
    exact congrArg Prod.fst heq
  · intro z hz
    obtain ⟨hz, ha⟩ := mem_filter.mp hz
    obtain ⟨hp, hpow⟩ := mem_primePowerPairs.mp hz
    refine ⟨z.1, mem_primeSet.mpr ⟨hp, ?_⟩, ?_⟩
    · simpa only [ha, zero_add, pow_one] using hpow
    · exact Prod.ext rfl ha.symm
  · intro p hp
    rfl

private theorem sum_even_exponent (n : ℕ) :
    (∑ z ∈ (primePowerPairs n).filter (fun z => z.2 % 2 = 1), Real.log (z.1 : ℝ)) =
      psiNat n.sqrt := by
  rw [psiNat_eq_primePowerPairs]
  symm
  apply sum_bij (fun z _ => (z.1, 2 * z.2 + 1))
  · intro z hz
    obtain ⟨hp, hpow⟩ := mem_primePowerPairs.mp hz
    exact mem_filter.mpr ⟨mem_primePowerPairs.mpr ⟨hp, pow_even_sqrt.mpr hpow⟩, by omega⟩
  · intro z hz w hw heq
    apply Prod.ext
    · simpa only [Prod.fst] using congrArg (fun u : ℕ × ℕ => u.1) heq
    · have hh := congrArg Prod.snd heq
      dsimp only at hh
      omega
  · intro z hz
    obtain ⟨hz, ha⟩ := mem_filter.mp hz
    obtain ⟨hp, hpow⟩ := mem_primePowerPairs.mp hz
    have hid : 2 * (z.2 / 2) + 1 = z.2 := by omega
    refine ⟨(z.1, z.2 / 2), mem_primePowerPairs.mpr ⟨hp, ?_⟩,
      Prod.ext rfl hid⟩
    apply pow_even_sqrt.mp
    simpa only [hid] using hpow
  · intro z hz
    rfl

private theorem sum_odd_exponent (n : ℕ) :
    (∑ z ∈ (primePowerPairs n).filter (fun z => z.2 ≠ 0 ∧ z.2 % 2 ≠ 1),
      Real.log (z.1 : ℝ)) =
      ∑ z ∈ oddPowerPairs n, Real.log (z.1 : ℝ) := by
  symm
  apply sum_bij (fun z _ => (z.1, 2 * z.2 + 2))
  · intro z hz
    obtain ⟨hp, hpow⟩ := mem_oddPowerPairs.mp hz
    exact mem_filter.mpr ⟨mem_primePowerPairs.mpr
      ⟨hp, by simpa only [show 2 * z.2 + 2 + 1 = 2 * z.2 + 3 by omega] using hpow⟩,
      by omega⟩
  · intro z hz w hw heq
    apply Prod.ext
    · simpa only [Prod.fst] using congrArg (fun u : ℕ × ℕ => u.1) heq
    · have hh := congrArg Prod.snd heq
      dsimp only at hh
      omega
  · intro z hz
    obtain ⟨hz, ha0, ha1⟩ := mem_filter.mp hz
    obtain ⟨hp, hpow⟩ := mem_primePowerPairs.mp hz
    have hid : 2 * ((z.2 - 2) / 2) + 2 = z.2 := by omega
    refine ⟨(z.1, (z.2 - 2) / 2), mem_oddPowerPairs.mpr ⟨hp, ?_⟩,
      Prod.ext rfl hid⟩
    convert hpow using 1
    congr 1
    omega
  · intro z hz
    rfl

theorem psiNat_sub_thetaNat (n : ℕ) :
    psiNat n - thetaNat n = psiNat n.sqrt +
      ∑ z ∈ oddPowerPairs n, Real.log (z.1 : ℝ) := by
  have hsplit :
      (∑ z ∈ primePowerPairs n, Real.log (z.1 : ℝ)) =
      (∑ z ∈ (primePowerPairs n).filter (fun z => z.2 = 0), Real.log (z.1 : ℝ)) +
      (∑ z ∈ (primePowerPairs n).filter (fun z => z.2 % 2 = 1), Real.log (z.1 : ℝ)) +
      (∑ z ∈ (primePowerPairs n).filter (fun z => z.2 ≠ 0 ∧ z.2 % 2 ≠ 1),
        Real.log (z.1 : ℝ)) := by
    simp only [sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro z hz
    by_cases h0 : z.2 = 0
    · simp [h0]
    · by_cases h1 : z.2 % 2 = 1
      · simp [h0, h1]
      · simp [h0, h1]
  rw [sum_zero_exponent, sum_even_exponent, sum_odd_exponent] at hsplit
  rw [psiNat_eq_primePowerPairs]
  linarith

end Pilz.Chebyshev

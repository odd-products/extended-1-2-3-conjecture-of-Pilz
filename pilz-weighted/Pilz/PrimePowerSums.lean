import Pilz.ChebyshevKernel
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite prime-power sums

The von Mangoldt sum is identified with the sum over prime powers with
their unique prime base and positive exponent. This finite version is
used to separate the even exponents in the paper's prime-power estimate.
-/

noncomputable section

namespace Pilz.Chebyshev

open Finset
open scoped BigOperators ArithmeticFunction.vonMangoldt

def primeSet (n : ℕ) : Finset ℕ := (Icc 1 n).filter Nat.Prime

theorem mem_primeSet {n p : ℕ} : p ∈ primeSet n ↔ p.Prime ∧ p ≤ n := by
  simp only [primeSet, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨_, hpn⟩, hp⟩
    exact ⟨hp, hpn⟩
  · rintro ⟨hp, hpn⟩
    exact ⟨⟨hp.pos, hpn⟩, hp⟩

theorem primeSet_card (n : ℕ) : (primeSet n).card = primeCount n := by
  unfold primeCount
  congr 1
  ext p
  simp only [mem_primeSet, mem_filter, mem_range]
  constructor
  · rintro ⟨hp, hpn⟩
    exact ⟨by omega, hp⟩
  · rintro ⟨hpn, hp⟩
    exact ⟨hp, by omega⟩

theorem primeSet_mono {a b : ℕ} (hab : a ≤ b) : primeSet a ⊆ primeSet b := by
  intro p hp
  obtain ⟨hprime, hpa⟩ := mem_primeSet.mp hp
  exact mem_primeSet.mpr ⟨hprime, hpa.trans hab⟩

theorem thetaNat_eq_sum_primes (n : ℕ) : thetaNat n = ∑ p ∈ primeSet n, Real.log p := by
  simp only [thetaNat, primeSet, sum_filter]

theorem thetaNat_sub_le_freshCount_mul_log {n : ℕ} (hn : 1 ≤ n) :
    thetaNat n - thetaNat (n / 2) ≤ (freshCount n : ℝ) * Real.log n := by
  have hsub : primeSet (n / 2) ⊆ primeSet n := primeSet_mono (Nat.div_le_self n 2)
  have hsum : thetaNat n - thetaNat (n / 2) =
      ∑ p ∈ primeSet n \ primeSet (n / 2), Real.log p := by
    rw [thetaNat_eq_sum_primes, thetaNat_eq_sum_primes]
    exact (sum_sdiff_eq_sub hsub).symm
  have hcard : (primeSet n \ primeSet (n / 2)).card = freshCount n := by
    rw [card_sdiff_of_subset hsub, primeSet_card, primeSet_card]
    rfl
  rw [hsum]
  calc
    _ ≤ ∑ _p ∈ primeSet n \ primeSet (n / 2), Real.log (n : ℝ) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hprime, hpn⟩ := mem_primeSet.mp (mem_sdiff.mp hp).1
      exact Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hpn)
    _ = _ := by simp only [sum_const, nsmul_eq_mul, hcard]

def primePowerPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((primeSet n) ×ˢ range (Nat.log 2 n)).filter (fun z => z.1 ^ (z.2 + 1) ≤ n)

theorem mem_primePowerPairs {n p a : ℕ} :
    (p, a) ∈ primePowerPairs n ↔ p.Prime ∧ p ^ (a + 1) ≤ n := by
  simp only [primePowerPairs, mem_filter, mem_product, mem_range, mem_primeSet]
  constructor
  · rintro ⟨⟨⟨hp, _⟩, _⟩, hpow⟩
    exact ⟨hp, hpow⟩
  · rintro ⟨hp, hpow⟩
    have hp_le : p ≤ n := (le_self_pow₀ hp.one_le (by omega : a + 1 ≠ 0)).trans hpow
    have htwo : 2 ^ (a + 1) ≤ n :=
      (Nat.pow_le_pow_left hp.two_le (a + 1)).trans hpow
    have ha := Nat.le_log_of_pow_le (by decide : 1 < 2) htwo
    exact ⟨⟨⟨hp, hp_le⟩, by omega⟩, hpow⟩

theorem psiNat_eq_primePowerPairs (n : ℕ) :
    psiNat n = ∑ z ∈ primePowerPairs n, Real.log (z.1 : ℝ) := by
  have hfilter : psiNat n = ∑ d ∈ (Icc 1 n).filter IsPrimePow, Λ d := by
    unfold psiNat
    symm
    apply sum_subset (filter_subset _ _)
    intro d hd hnot
    exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
      (by simpa only [mem_filter, hd, true_and] using hnot)
  rw [hfilter]
  symm
  apply sum_bij (fun z _ => z.1 ^ (z.2 + 1))
  · intro z hz
    obtain ⟨hp, hpow⟩ := mem_primePowerPairs.mp hz
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨one_le_pow₀ hp.one_le, hpow⟩,
      (isPrimePow_nat_iff _).mpr ⟨z.1, z.2 + 1, hp, by omega, rfl⟩⟩
  · intro z hz w hw heq
    obtain ⟨hzprime, _⟩ := mem_primePowerPairs.mp hz
    obtain ⟨hwprime, _⟩ := mem_primePowerPairs.mp hw
    exact Prod.ext (hzprime.pow_inj hwprime heq).1 (hzprime.pow_inj hwprime heq).2
  · intro d hd
    obtain ⟨hdi, hprimepow⟩ := mem_filter.mp hd
    obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff _).mp hprimepow
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    exact ⟨(p, a), mem_primePowerPairs.mpr ⟨hp, (mem_Icc.mp hdi).2⟩, rfl⟩
  · intro z hz
    obtain ⟨hp, _⟩ := mem_primePowerPairs.mp hz
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp]

end Pilz.Chebyshev


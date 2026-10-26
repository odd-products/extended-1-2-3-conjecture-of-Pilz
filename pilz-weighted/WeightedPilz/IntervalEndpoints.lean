import WeightedPilz.Basic
import WeightedPilz.Endpoints
import Mathlib.Tactic.IntervalCases

/-! Prime-coordinate endpoint bounds, valid uniformly for all interval weights. -/

namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem coeff_interval_zero (n : ℕ) (c : ℕ → K) (hn : 1 ≤ n) :
    coeff 0 (interval n c) = c 1 := by
  have h := coeff_interval n c (a := 1) (by decide)
  simpa [Nat.factorization_one, Finset.mem_Icc, hn] using h

theorem coeff_interval_prime (n : ℕ) (c : ℕ → K) {p : ℕ}
    (hp : p.Prime) (hpn : p ≤ n) :
    coeff (Finsupp.single p 1) (interval n c) = c p := by
  have h := coeff_interval n c (a := p) hp.pos
  simpa [hp.factorization, Finset.mem_Icc, hp.one_le, hpn] using h

/-- Constant and prime vertices provide the uniform endpoint lower bound. -/
theorem interval_prime_endpoints (n : ℕ) (c : ℕ → K)
    (hn : 1 ≤ n) (hc : NonzeroWeights n c) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ n) :
    S.card + 1 ≤ distance (interval n c) := by
  apply pure_endpoints_distance S (interval n c)
  · rw [coeff_interval_zero n c hn]
    exact hc 1 (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)
  · intro p hp
    obtain ⟨hpprime, hpn⟩ := hS p hp
    refine ⟨1, by decide, ?_⟩
    rw [coeff_interval_prime n c hpprime hpn]
    exact hc p (Finset.mem_Icc.mpr ⟨hpprime.one_le, hpn⟩)

theorem interval_prime_count_lower (n : ℕ) (c : ℕ → K)
    (hn : 1 ≤ n) (hc : NonzeroWeights n c) :
    ((Finset.range (n + 1)).filter Nat.Prime).card + 1 ≤ distance (interval n c) := by
  apply interval_prime_endpoints n c hn hc
  intro p hp
  obtain ⟨hpbound, hprime⟩ := Finset.mem_filter.mp hp
  exact ⟨hprime, Nat.lt_succ_iff.mp (Finset.mem_range.mp hpbound)⟩

theorem intervalBound_two (c : ℕ → K) (hc : NonzeroWeights 2 c) :
    IntervalBound 2 c := by
  intro H hH
  apply nonmonomial_weight_mul_two (interval 2 c) H _ hH
  rw [weight_interval 2 c hc]

theorem intervalBound_three (c : ℕ → K) (hc : NonzeroWeights 3 c) :
    IntervalBound 3 c := by
  have hd := interval_prime_count_lower 3 c (by decide) hc
  have hcount : ((Finset.range (3 + 1)).filter Nat.Prime).card = 2 := by decide
  rw [hcount] at hd
  exact (le_distance_iff _ 3).mp hd

theorem intervalBound_le_three (n : ℕ) (hn : n ≤ 3) (c : ℕ → K)
    (hc : NonzeroWeights n c) : IntervalBound n c := by
  interval_cases n
  · exact intervalBound_zero c
  · exact intervalBound_one c hc
  · exact intervalBound_two c hc
  · exact intervalBound_three c hc

end WeightedPilz

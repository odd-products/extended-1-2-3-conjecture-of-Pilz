import WeightedPilz.MiddleSix
import WeightedPilz.MiddleCore
import WeightedPilz.Arithmetic.MiddleBudgets

/-! The full base-variable bound throughout the middle interval. -/
noncomputable section
namespace WeightedPilz
variable {K : Type*} [Field K]

theorem middle_base (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c)
    (hn : 25 ≤ n) (hn' : n ≤ 66) (D : Poly K) (hD : D ≠ 0)
    (hbase : ∀ p ∈ intervalFreshPrimes n, ∀ d ∈ D.support, d p = 0) :
    n ≤ weight (intervalCore n c * D) + Arithmetic.freshCount n * weight D := by
  have hbudget := Arithmetic.middleBasicBudgets hn hn'
  by_cases hsmall : weight D ≤ 6
  · have h := middle_six_term_bound n c D hc hn hn' hD hsmall
    have hrpos : 0 < Arithmetic.freshCount n := by
      by_contra hnot
      have hz : Arithmetic.freshCount n = 0 := by omega
      have hstrict := hbudget.2.1
      rw [hz, zero_mul] at hstrict
      omega
    have hr : (intervalFreshPrimes n).Nonempty := by
      apply Finset.card_pos.mp
      rwa [Pilz.card_freshPrimes]
    rwa [weight_interval_mul_base_freshCount n c (by omega) hc hr D hbase] at h
  · have hseven : 7 ≤ weight D := by omega
    have hcore := middle_core_mul_endpoint n c hc hn hn' D hD
    have hmul := Nat.mul_le_mul_left (Arithmetic.freshCount n) hseven
    nlinarith [hbudget.1]

theorem middle_interval_mul_base_lower (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (D : Poly K) (hD : D ≠ 0)
    (hbase : ∀ p ∈ intervalFreshPrimes n, ∀ d ∈ D.support, d p = 0) :
    n ≤ weight (interval n c * D) := by
  have hbudget := Arithmetic.middleBasicBudgets hn hn'
  have hrpos : 0 < Arithmetic.freshCount n := by
    by_contra hnot
    have hz : Arithmetic.freshCount n = 0 := by omega
    have hstrict := hbudget.2.1
    rw [hz, zero_mul] at hstrict
    omega
  have hr : (intervalFreshPrimes n).Nonempty := by
    apply Finset.card_pos.mp
    rwa [Pilz.card_freshPrimes]
  rw [weight_interval_mul_base_freshCount n c (by omega) hc hr D hbase]
  exact middle_base n c hc hn hn' D hD hbase

end WeightedPilz

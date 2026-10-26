import WeightedPilz.InitialCore
import WeightedPilz.WeightedCompletion

/-! The initial weighted interval theorem through eight, over arbitrary fields.
The later cases in `thm:initial` require the additional short-multiple analysis.
-/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

/-- Adjoining the next prime term preserves exact weighted interval distance. -/
theorem intervalBound_prime_successor (n : ℕ) (c : ℕ → K)
    (hp : (n + 1).Prime) (hc : NonzeroWeights (n + 1) c)
    (hb : IntervalBound n c) : IntervalBound (n + 1) c := by
  have hn : 0 < n := by have := hp.two_le; omega
  have hcprev : NonzeroWeights n c := by
    intro a ha
    exact hc a (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1, by
      have := (Finset.mem_Icc.mp ha).2
      omega⟩)
  have hind : ∀ d ∈ (interval n c).support, d (n + 1) = 0 := by
    intro d hd
    rw [support_interval n c hcprev] at hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdiv
    have haI := Finset.mem_Icc.mp ha
    have hle := Nat.le_of_dvd (by omega : 0 < a) hdiv
    omega
  have h := weighted_sharp_completion_coordinate (interval n c) (n + 1)
    (interval_ne_zero c hn hcprev) hind (c (n + 1))
    (hc (n + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩))
  have hdist : n ≤ distance (interval n c) := (le_distance_iff _ n).mpr hb
  rw [weight_interval n c hcprev, min_eq_left (by omega)] at h
  have heq : interval (n + 1) c = interval n c + C (c (n + 1)) * X (n + 1) := by
    rw [interval_succ, hp.factorization]
    simp [X, C_mul_monomial]
  rw [← heq] at h
  exact (le_distance_iff _ (n + 1)).mp h

/-- The precise threshold at which sharp completion proves the interval bound. -/
theorem intervalBound_of_core_distance (n : ℕ) (c : ℕ → K) (hn : 0 < n)
    (hc : NonzeroWeights n c) (hr : (intervalFreshPrimes n).Nonempty)
    (hcore : n ≤ distance (intervalCore n c) + 2 * (intervalFreshPrimes n).card) :
    IntervalBound n c := by
  have h := (intervalFreshData n c hn hc hr).sharp_completion
  have hweight := weight_intervalCore_add_freshCount n c hc
  rw [← Pilz.card_freshPrimes n] at hweight
  change min (weight (intervalCore n c) + (intervalFreshPrimes n).card)
    (distance (intervalCore n c) + 2 * (intervalFreshPrimes n).card) ≤
    distance (intervalFreshData n c hn hc hr).F at h
  rw [hweight, min_eq_left hcore, ← distance_interval_eq_freshData] at h
  exact (le_distance_iff _ n).mp h

theorem intervalBound_four_to_five (n : ℕ) (hn : 4 ≤ n) (hn5 : n ≤ 5)
    (c : ℕ → K) (hc : NonzeroWeights n c) : IntervalBound n c := by
  have hmem : n ∈ Finset.Icc 4 5 := Finset.mem_Icc.mpr ⟨hn, hn5⟩
  have hrall : ∀ m ∈ Finset.Icc 4 5, (intervalFreshPrimes m).Nonempty := by decide
  have hwall : ∀ m ∈ Finset.Icc 4 5, 2 ≤ m - (intervalFreshPrimes m).card := by decide
  have hball : ∀ m ∈ Finset.Icc 4 5, m ≤ 2 + 2 * (intervalFreshPrimes m).card := by decide
  have hw : 2 ≤ weight (intervalCore n c) := by
    rw [weight_intervalCore n c hc]
    exact hwall n hmem
  apply intervalBound_of_core_distance n c (by omega) hc (hrall n hmem)
  exact (hball n hmem).trans (Nat.add_le_add_right (nonmonomial_distance_two _ hw) _)

theorem intervalBound_six_to_eight (n : ℕ) (hn : 6 ≤ n) (hn8 : n ≤ 8)
    (c : ℕ → K) (hc : NonzeroWeights n c) : IntervalBound n c := by
  have hmem : n ∈ Finset.Icc 6 8 := Finset.mem_Icc.mpr ⟨hn, hn8⟩
  have hrall : ∀ m ∈ Finset.Icc 6 8, (intervalFreshPrimes m).Nonempty := by decide
  have hball : ∀ m ∈ Finset.Icc 6 8, m ≤ 4 + 2 * (intervalFreshPrimes m).card := by decide
  apply intervalBound_of_core_distance n c (by omega) hc (hrall n hmem)
  exact (hball n hmem).trans (Nat.add_le_add_right (intervalCore_distance_four n hn hn8 c hc) _)

theorem intervalBound_le_eight (n : ℕ) (hn : n ≤ 8) (c : ℕ → K)
    (hc : NonzeroWeights n c) : IntervalBound n c := by
  by_cases h3 : n ≤ 3
  · exact intervalBound_le_three n h3 c hc
  by_cases h5 : n ≤ 5
  · exact intervalBound_four_to_five n (by omega) h5 c hc
  · exact intervalBound_six_to_eight n (by omega) hn c hc

theorem distance_interval_eq_of_le_eight (n : ℕ) (hn : n ≤ 8) (c : ℕ → K)
    (hc : NonzeroWeights n c) : distance (interval n c) = n := by
  apply Nat.le_antisymm
  · simpa only [weight_interval n c hc] using distance_le_weight (interval n c)
  · exact (le_distance_iff _ n).mpr (intervalBound_le_eight n hn c hc)

end WeightedPilz

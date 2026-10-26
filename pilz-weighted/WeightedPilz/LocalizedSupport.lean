import WeightedPilz.LocalizedSmallSupport
import WeightedPilz.Arithmetic.LocalizedNumerics

/-!
# The localized multiplier theorem over every field

All analytic/counting inputs are field-independent. The polynomial estimates
come from the weighted disjoint components and weighted endpoint profiles.
-/

noncomputable section

namespace WeightedPilz

open Pilz (primesUpTo primeCount freshCount roughCount roughIntervalCount
  roughRealCount roughRealIntervalCount roughRealCount_natCast
  roughRealIntervalCount_natCast sieveAlpha sieveNu middleAlpha middleDelta)

variable {K : Type*} [Field K]

theorem localized_prime_budget (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hq : 17 ≤ q) (hqn : q ≤ n / 2)
    (hcut : q < 2 * (weight D - 1)) (hr : 8 ≤ freshCount n)
    (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    10 * freshCount n + 4 * primeCount (n / 2) + 2 * primeCount (n / 3) +
      2 * primeCount (n / 5) ≤ weight (interval n c * D) + 48 := by
  have hu : 10 ≤ weight D := by omega
  exact Pilz.prime_budget_arithmetic (weight (interval n c * D)) (weight D) (freshCount n)
    (primeCount q) (primeCount (n / 2)) (primeCount (n / 3)) (primeCount (n / 5))
    (roughIntervalCount (primesUpTo q) n)
    (roughCount (primesUpTo q) (n / 2)) (roughCount (primesUpTo q) (n / 3))
    (roughCount (primesUpTo q) (n / 5)) hu hr
    (Pilz.primeCount_le_terms_sub_three hq hcut)
    (Pilz.freshCount_le_roughIntervalCount n q hqn)
    (Pilz.roughCount_add_primeCount_ge q (n / 2) hlargest.1)
    (Pilz.roughCount_add_primeCount_ge q (n / 3) hlargest.1)
    (Pilz.roughCount_add_primeCount_ge q (n / 5) hlargest.1)
    (component_budget_eight q n c D hc hq hD hnorm hlargest)

theorem localized_finite (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 67 ≤ n) (hn' : n ≤ 1023)
    (hq : 17 ≤ q) (hqn : q ≤ n / 2) (hcut : q < 2 * (weight D - 1))
    (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    n ≤ weight (interval n c * D) := by
  have hp := localized_prime_budget n q c D hc hq hqn hcut
    (Arithmetic.fresh_count_eight n hn) hD hnorm hlargest
  have hnumerical := (Arithmetic.finite_prime_budgets hn hn').2
  omega

theorem weight_mul_freshCount_le (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hqn : q ≤ n / 2) (hlargest : LargestPrime D q) :
    weight D * freshCount n ≤ weight (interval n c * D) := by
  exact (Nat.mul_le_mul_left (weight D)
    (Pilz.freshCount_le_roughIntervalCount n q hqn)).trans
    (weight_interval_mul_ge_index_one (primesUpTo q) n c D hc (Pilz.primesUpTo_prime q)
      (largestPrime_vars_subset D q hlargest))

theorem weight_lt_thirty_of_short (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hqn : q ≤ n / 2) (hlargest : LargestPrime D q)
    (hshort : weight (interval n c * D) < n)
    (hr : (n : ℝ) / 30 < freshCount n) : weight D < 30 := by
  have hbudget : (weight D : ℝ) * freshCount n < n := by
    exact_mod_cast (weight_mul_freshCount_le n q c D hc hqn hlargest).trans_lt hshort
  by_contra hnot
  have hu : (30 : ℝ) ≤ weight D := by exact_mod_cast (show 30 ≤ weight D by omega)
  have hmul := mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg (freshCount n) : (0 : ℝ) ≤ _)
  linarith

theorem weight_lt_log_of_short (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 2 ≤ n) (hqn : q ≤ n / 2) (hlargest : LargestPrime D q)
    (hshort : weight (interval n c * D) < n)
    (hr : 7 * (n : ℝ) / (20 * Real.log n) < freshCount n) :
    (weight D : ℝ) < (20 / 7) * Real.log n := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hr' := (div_lt_iff₀ (show (0 : ℝ) < 20 * Real.log n by positivity)).mp hr
  have hbudget : (weight D : ℝ) * freshCount n < n := by
    exact_mod_cast (weight_mul_freshCount_le n q c D hc hqn hlargest).trans_lt hshort
  by_contra hnot
  have hu : (20 / 7) * Real.log n ≤ (weight D : ℝ) := le_of_not_gt hnot
  have hmul := mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg (freshCount n) : (0 : ℝ) ≤ _)
  nlinarith

theorem localized_five_band_budget (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hq : 17 ≤ q) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D q) (hu : 4 ≤ weight D) :
    sieveAlpha q * ((weight D : ℝ) / 2 + 46 / 15) * n -
      ((22 * (weight D : ℝ) + 24) / 15) * (sieveNu q : ℝ) ≤
        (weight (interval n c * D) : ℝ) := by
  have hq5 : 5 ≤ q := by omega
  have hbudget : (weight D : ℝ) * roughIntervalCount (primesUpTo q) n +
      4 * roughCount (primesUpTo q) (n / 2) +
      2 * roughCount (primesUpTo q) (n / 3) +
      2 * roughCount (primesUpTo q) (n / 5) ≤ (weight (interval n c * D) : ℝ) := by
    exact_mod_cast component_budget_eight q n c D hc hq hD hnorm hlargest
  have hsplitNat : roughIntervalCount (primesUpTo q) n + roughCount (primesUpTo q) (n / 2) =
      roughCount (primesUpTo q) n :=
    Nat.sub_add_cancel (Pilz.roughCount_mono _ (Nat.div_le_self n 2))
  have hsplit : (roughIntervalCount (primesUpTo q) n : ℝ) +
      roughCount (primesUpTo q) (n / 2) = roughCount (primesUpTo q) n := by
    exact_mod_cast hsplitNat
  have h1 := Pilz.roughRealCount_primesUpTo_alpha_lower hq5 (n : ℝ) (by positivity)
  have hI := Pilz.roughRealIntervalCount_primesUpTo_alpha_lower hq5 (n : ℝ) (by positivity)
  have h3 := Pilz.roughRealCount_primesUpTo_alpha_lower hq5 ((n : ℝ) / 3) (by positivity)
  have h5 := Pilz.roughRealCount_primesUpTo_alpha_lower hq5 ((n : ℝ) / 5) (by positivity)
  simp only [roughRealCount_natCast] at h1
  simp only [roughRealIntervalCount_natCast] at hI
  simp only [roughRealCount, Nat.floor_div_ofNat, Nat.floor_natCast] at h3 h5
  have huR : (4 : ℝ) ≤ weight D := by exact_mod_cast hu
  have hIprod := mul_le_mul_of_nonneg_left hI (sub_nonneg.mpr huR)
  nlinarith

theorem localized_expansion_five_bands (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 1024 ≤ n) (hq17 : 17 ≤ q) (hq53 : q ≤ 53)
    (hcut : q < 2 * (weight D - 1)) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    (n : ℝ) < weight (interval n c * D) := by
  have hnum := Arithmetic.small_support_prime_numeric n q (weight D) hn hq17 hq53 hlargest.1 hcut
  exact hnum.trans_le (localized_five_band_budget n q c D hc hq17 hD hnorm hlargest (by omega))

theorem localized_middle_budget (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hq : 7 ≤ q) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D q) (hu : 4 ≤ weight D) :
    ((weight D : ℝ) + 4) / 2 * middleAlpha q * n -
      2 * ((weight D : ℝ) - 2) * middleDelta q ≤ (weight (interval n c * D) : ℝ) := by
  have hbudget : 4 * (roughCount (primesUpTo q) n : ℝ) +
      ((weight D - 4 : ℕ) : ℝ) * roughIntervalCount (primesUpTo q) n ≤
        (weight (interval n c * D) : ℝ) := by
    exact_mod_cast component_budget_four_paper q n c D hc (by omega) hD hnorm hlargest hu
  have hcast : ((weight D - 4 : ℕ) : ℝ) = (weight D : ℝ) - 4 := by
    rw [Nat.cast_sub hu]
    norm_num
  rw [hcast] at hbudget
  have h1 := Pilz.roughRealCount_primesUpTo_middle_lower hq (n : ℝ) (by positivity)
  have hI := Pilz.roughRealIntervalCount_primesUpTo_middle_lower hq (n : ℝ) (by positivity)
  simp only [roughRealCount_natCast] at h1
  simp only [roughRealIntervalCount_natCast] at hI
  have huR : (4 : ℝ) ≤ weight D := by exact_mod_cast hu
  have hIprod := mul_le_mul_of_nonneg_left hI (sub_nonneg.mpr huR)
  nlinarith

theorem localized_expansion_middle (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 32768 ≤ n) (hq59 : 59 ≤ q) (hq271 : q ≤ 271)
    (hcut : q < 2 * (weight D - 1)) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    (n : ℝ) < weight (interval n c * D) := by
  have hnum := Arithmetic.middle_support_prime_numeric n q (weight D) hn hq59 hq271 hlargest.1 hcut
  exact hnum.trans_le (localized_middle_budget n q c D hc (by omega) hD hnorm hlargest (by omega))

theorem localized_expansion_large_support (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 32768 ≤ n) (hq : 277 ≤ q)
    (huL : (weight D : ℝ) < (20 / 7) * Real.log n)
    (hcut : q < 2 * (weight D - 1)) (hlargest : LargestPrime D q) :
    (5 / 4 : ℝ) * n < weight (interval n c * D) := by
  have hnum := Arithmetic.large_support_prime_count n q (weight D) hn hq hlargest.1 huL hcut
  have hbudget : (weight D : ℝ) * roughIntervalCount (primesUpTo q) n ≤
      weight (interval n c * D) := by
    exact_mod_cast weight_interval_mul_ge_index_one (primesUpTo q) n c D hc
      (Pilz.primesUpTo_prime q) (largestPrime_vars_subset D q hlargest)
  exact hnum.trans_le hbudget

private theorem prime_ge_seventeen {q : ℕ} (hp : Nat.Prime q) (hq : ¬q ≤ 13) : 17 ≤ q := by
  by_contra hn
  have hlo : 14 ≤ q := by omega
  have hhi : q ≤ 16 := by omega
  interval_cases q <;> norm_num at hp

private theorem prime_ge_fiftynine {q : ℕ} (hp : Nat.Prime q) (hq : ¬q ≤ 53) : 59 ≤ q := by
  by_contra hn
  have hlo : 54 ≤ q := by omega
  have hhi : q ≤ 58 := by omega
  interval_cases q <;> norm_num at hp

private theorem prime_ge_twoseventyseven {q : ℕ} (hp : Nat.Prime q)
    (hq : ¬q ≤ 271) : 277 ≤ q := by
  by_contra hn
  have hlo : 272 ≤ q := by omega
  have hhi : q ≤ 276 := by omega
  interval_cases q <;> norm_num at hp

/-- `arith:thm:localized-expansion`, with no restriction on the characteristic
or on the nonzero interval weights. -/
theorem localized_expansion (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 67 ≤ n) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D q)
    (hqn : q ≤ n / 2) (hcut : q < 2 * (weight D - 1)) :
    n ≤ weight (interval n c * D) := by
  by_cases hsmall : q ≤ 13
  · exact localized_small_support n q c D hc hn hsmall hD hnorm hlargest hcut
  have hq17 := prime_ge_seventeen hlargest.1 hsmall
  by_cases hfinite : n ≤ 1023
  · exact localized_finite n q c D hc hn hfinite hq17 hqn hcut hD hnorm hlargest
  have hn1024 : 1024 ≤ n := by omega
  by_contra hnot
  have hshort : weight (interval n c * D) < n := by omega
  have hshortR : (weight (interval n c * D) : ℝ) < n := by exact_mod_cast hshort
  by_cases hq53 : q ≤ 53
  · have hh := localized_expansion_five_bands n q c D hc hn1024 hq17 hq53 hcut hD hnorm hlargest
    linarith
  by_cases hmedium : n ≤ 32768
  · have hr := Arithmetic.fresh_count_div_thirty hn1024 hmedium
    have hu := weight_lt_thirty_of_short n q c D hc hqn hlargest hshort hr
    have hq59 := prime_ge_fiftynine hlargest.1 hq53
    omega
  have hnlarge : 32768 ≤ n := by omega
  have hr := Arithmetic.fresh_count_log hnlarge
  have huL := weight_lt_log_of_short n q c D hc (by omega) hqn hlargest hshort hr
  by_cases hq271 : q ≤ 271
  · have hq59 := prime_ge_fiftynine hlargest.1 hq53
    have hh := localized_expansion_middle n q c D hc hnlarge hq59 hq271 hcut hD hnorm hlargest
    linarith
  · have hq277 := prime_ge_twoseventyseven hlargest.1 hq271
    have hh := localized_expansion_large_support n q c D hc hnlarge hq277 huL hcut hlargest
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith

end WeightedPilz

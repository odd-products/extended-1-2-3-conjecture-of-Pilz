import Pilz.SievePrimes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Data.Rat.BigOperators

/-!
# Exact reciprocal certificates and the five localized support bands

The finite sums below are evaluated over actual finite sets of primes.
The expansion estimate combines the proved component profile with the
proved ordinary and half-interval alpha-sieve bounds.
-/

noncomputable section

set_option maxRecDepth 65536
set_option maxHeartbeats 200000

namespace Pilz

open scoped BigOperators

def primeReciprocalSum (a b : ℕ) : ℝ :=
  ∑ p ∈ (primesUpTo b).filter (fun p => a ≤ p), 1 / (p : ℝ)

theorem reciprocal_sum_7_53 : primeReciprocalSum 7 53 < (259 : ℝ) / 400 := by
  have hs : (primesUpTo 53).filter (fun p => 7 ≤ p) =
      ({7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53} : Finset ℕ) := by decide
  rw [primeReciprocalSum, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton, not_false_eq_true, or_false, false_or]

theorem reciprocal_sum_11_149 : primeReciprocalSum 11 149 < (229 : ℝ) / 320 := by
  have hs : (primesUpTo 149).filter (fun p => 11 ≤ p) =
      ({11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59,
        61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149} : Finset ℕ) := by decide
  rw [primeReciprocalSum, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton, not_false_eq_true, or_false, false_or]

theorem reciprocal_sum_11_271 : primeReciprocalSum 11 271 < (33 : ℝ) / 40 := by
  have hs : (primesUpTo 271).filter (fun p => 11 ≤ p) =
      ({11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59,
        61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
        181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239,
        241, 251, 257, 263, 269, 271} : Finset ℕ) := by decide
  rw [primeReciprocalSum, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton, not_false_eq_true, or_false, false_or]

theorem sieveAlpha_antitone {a b : ℕ} (hab : a ≤ b) : sieveAlpha b ≤ sieveAlpha a := by
  have hsub : sieveExtraPrimes a ⊆ sieveExtraPrimes b := by
    intro p hp
    exact Finset.mem_sdiff.mpr
      ⟨primesUpTo_mono hab (Finset.mem_sdiff.mp hp).1, (Finset.mem_sdiff.mp hp).2⟩
  have hs : (∑ p ∈ sieveExtraPrimes a, 1 / (p : ℝ)) ≤
      ∑ p ∈ sieveExtraPrimes b, 1 / (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _hp _hnot => by positivity)
  unfold sieveAlpha
  linarith

theorem sieveNu_mono {a b : ℕ} (hab : a ≤ b) : sieveNu a ≤ sieveNu b :=
  Nat.sub_le_sub_right (primeCount_mono hab) 2

private theorem alpha_23 : (7 : ℝ) / 50 < sieveAlpha 23 := by
  have hs : sieveExtraPrimes 23 = ({7, 11, 13, 17, 19, 23} : Finset ℕ) := by decide
  rw [sieveAlpha, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton, not_false_eq_true, or_false, false_or]

private theorem alpha_37 : (7 : ℝ) / 60 < sieveAlpha 37 := by
  have hs : sieveExtraPrimes 37 = ({7, 11, 13, 17, 19, 23, 29, 31, 37} : Finset ℕ) := by decide
  rw [sieveAlpha, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton, not_false_eq_true, or_false, false_or]

private theorem alpha_43 : (13 : ℝ) / 125 < sieveAlpha 43 := by
  have hs : sieveExtraPrimes 43 = ({7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43} : Finset ℕ) := by decide
  rw [sieveAlpha, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton, not_false_eq_true, or_false, false_or]

private theorem alpha_47 : (99 : ℝ) / 1000 < sieveAlpha 47 := by
  have hs : sieveExtraPrimes 47 = ({7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ) := by decide
  rw [sieveAlpha, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton, not_false_eq_true, or_false, false_or]

private theorem alpha_53 : (47 : ℝ) / 500 < sieveAlpha 53 := by
  have hs : sieveExtraPrimes 53 = ({7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53} : Finset ℕ) := by decide
  rw [sieveAlpha, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton, not_false_eq_true, or_false, false_or]

/-- The paper's five-band lower bound, before evaluating its constants. -/
theorem localized_five_band_budget (n q : ℕ) (D : Poly)
    (hq : 17 ≤ q) (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q)
    (hu : 4 ≤ weight D) :
    sieveAlpha q * ((weight D : ℝ) / 2 + 46 / 15) * n -
      ((22 * (weight D : ℝ) + 24) / 15) * (sieveNu q : ℝ) ≤
        (weight (interval n * D) : ℝ) := by
  have hq5 : 5 ≤ q := by omega
  have hbudget : (weight D : ℝ) * roughIntervalCount (primesUpTo q) n +
      4 * roughCount (primesUpTo q) (n / 2) +
      2 * roughCount (primesUpTo q) (n / 3) +
      2 * roughCount (primesUpTo q) (n / 5) ≤ (weight (interval n * D) : ℝ) := by
    exact_mod_cast component_budget_eight q n D hq hD hnorm hlargest
  have hsplitNat : roughIntervalCount (primesUpTo q) n + roughCount (primesUpTo q) (n / 2) =
      roughCount (primesUpTo q) n :=
    Nat.sub_add_cancel (roughCount_mono _ (Nat.div_le_self n 2))
  have hsplit : (roughIntervalCount (primesUpTo q) n : ℝ) +
      roughCount (primesUpTo q) (n / 2) = roughCount (primesUpTo q) n := by
    exact_mod_cast hsplitNat
  have h1 := roughRealCount_primesUpTo_alpha_lower hq5 (n : ℝ) (by positivity)
  have hI := roughRealIntervalCount_primesUpTo_alpha_lower hq5 (n : ℝ) (by positivity)
  have h3 := roughRealCount_primesUpTo_alpha_lower hq5 ((n : ℝ) / 3) (by positivity)
  have h5 := roughRealCount_primesUpTo_alpha_lower hq5 ((n : ℝ) / 5) (by positivity)
  simp only [roughRealCount_natCast] at h1
  simp only [roughRealIntervalCount_natCast] at hI
  simp only [roughRealCount, Nat.floor_div_ofNat, Nat.floor_natCast] at h3 h5
  have huR : (4 : ℝ) ≤ weight D := by exact_mod_cast hu
  have hIprod := mul_le_mul_of_nonneg_left hI (sub_nonneg.mpr huR)
  nlinarith

private theorem five_band_numeric (n u ν α a u₀ ν₀ : ℝ)
    (hn : 1024 ≤ n) (hu : u₀ ≤ u) (hu₀ : 4 ≤ u₀) (hν : ν ≤ ν₀)
    (ha : a ≤ α) (ha0 : 0 ≤ a)
    (hcorner : 1024 < a * (u₀ / 2 + 46 / 15) * 1024 - ((22 * u₀ + 24) / 15) * ν₀)
    (hslopeu : 0 ≤ a * 512 - 22 * ν₀ / 15)
    (hslopen : 0 ≤ a * (u₀ / 2 + 46 / 15) - 1) :
    n < α * (u / 2 + 46 / 15) * n - ((22 * u + 24) / 15) * ν := by
  have hu4 : 4 ≤ u := hu₀.trans hu
  have hslopeN : 0 ≤ a * (u / 2 + 46 / 15) - 1 := by nlinarith
  have hdu := mul_nonneg (sub_nonneg.mpr hu) hslopeu
  have hdn := mul_nonneg (sub_nonneg.mpr hn) hslopeN
  have hbase : n < a * (u / 2 + 46 / 15) * n - ((22 * u + 24) / 15) * ν₀ := by
    nlinarith
  have hαgain := mul_nonneg (sub_nonneg.mpr ha)
    (show 0 ≤ (u / 2 + 46 / 15) * n by positivity)
  have hνgain := mul_nonneg (sub_nonneg.mpr hν)
    (show 0 ≤ (22 * u + 24) / 15 by positivity)
  nlinarith

private theorem prime_five_bands (q : ℕ) (hq17 : 17 ≤ q) (hq53 : q ≤ 53)
    (hp : Nat.Prime q) : q ≤ 23 ∨ (29 ≤ q ∧ q ≤ 37) ∨ (41 ≤ q ∧ q ≤ 43) ∨ q = 47 ∨ q = 53 := by
  interval_cases q <;> first | omega | (exfalso; norm_num at hp)

private theorem localized_five_band_from_corner (n q u₀ ν₀ : ℕ) (D : Poly) (a : ℝ)
    (hn : 1024 ≤ n) (hq : 17 ≤ q) (hu : u₀ ≤ weight D) (hu₀ : 4 ≤ u₀)
    (hν : sieveNu q ≤ ν₀) (ha : a ≤ sieveAlpha q) (ha0 : 0 ≤ a)
    (hcorner : 1024 < a * ((u₀ : ℝ) / 2 + 46 / 15) * 1024 -
      ((22 * (u₀ : ℝ) + 24) / 15) * ν₀)
    (hslopeu : 0 ≤ a * 512 - 22 * (ν₀ : ℝ) / 15)
    (hslopen : 0 ≤ a * ((u₀ : ℝ) / 2 + 46 / 15) - 1)
    (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    (n : ℝ) < weight (interval n * D) := by
  have hnum := five_band_numeric (n : ℝ) (weight D : ℝ) (sieveNu q : ℝ) (sieveAlpha q)
    a u₀ ν₀ (by exact_mod_cast hn) (by exact_mod_cast hu) (by exact_mod_cast hu₀)
    (by exact_mod_cast hν) ha ha0 hcorner hslopeu hslopen
  exact hnum.trans_le (localized_five_band_budget n q D hq hD hnorm hlargest (hu₀.trans hu))

/-- The five support-prime bands `[17,53]`, uniformly for every `n≥1024`. -/
theorem localized_expansion_five_bands (n q : ℕ) (D : Poly)
    (hn : 1024 ≤ n) (hq17 : 17 ≤ q) (hq53 : q ≤ 53)
    (hcut : q < 2 * (weight D - 1)) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    (n : ℝ) < weight (interval n * D) := by
  rcases prime_five_bands q hq17 hq53 hlargest.1 with hq | hq | hq | rfl | rfl
  · have hν : sieveNu 23 = 7 := by decide
    apply localized_five_band_from_corner n q 10 7 D (7 / 50) hn hq17 (by omega) (by decide)
      (by simpa [hν] using sieveNu_mono hq) (alpha_23.le.trans (sieveAlpha_antitone hq))
    all_goals first | assumption | norm_num
  · have hν : sieveNu 37 = 10 := by decide
    apply localized_five_band_from_corner n q 16 10 D (7 / 60) hn hq17 (by omega) (by decide)
      (by simpa [hν] using sieveNu_mono hq.2) (alpha_37.le.trans (sieveAlpha_antitone hq.2))
    all_goals first | assumption | norm_num
  · have hν : sieveNu 43 = 12 := by decide
    apply localized_five_band_from_corner n q 22 12 D (13 / 125) hn hq17 (by omega) (by decide)
      (by simpa [hν] using sieveNu_mono hq.2) (alpha_43.le.trans (sieveAlpha_antitone hq.2))
    all_goals first | assumption | norm_num
  · have hν : sieveNu 47 = 13 := by decide
    apply localized_five_band_from_corner n 47 25 13 D (99 / 1000) hn (by decide) (by omega) (by decide)
      hν.le alpha_47.le
    all_goals first | assumption | norm_num
  · have hν : sieveNu 53 = 14 := by decide
    apply localized_five_band_from_corner n 53 28 14 D (47 / 500) hn (by decide) (by omega) (by decide)
      hν.le alpha_53.le
    all_goals first | assumption | norm_num

end Pilz



import WeightedPilz.Arithmetic.Imported
import Pilz.LocalizedMiddle

/-!
# Pure numerical localized-prime estimates

The proofs below separate the numerical content of the old localized argument
from its coefficient-specific polynomial statements. The variable `u` is a
natural number, and no polynomial, field, or support lower bound is assumed.
-/

noncomputable section

namespace WeightedPilz.Arithmetic

open Pilz

private theorem alpha_23 : (7 : ℝ) / 50 < sieveAlpha 23 := by
  have hs : sieveExtraPrimes 23 = ({7, 11, 13, 17, 19, 23} : Finset ℕ) := by decide
  rw [sieveAlpha, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton, not_false_eq_true, or_false, false_or]

private theorem alpha_37 : (7 : ℝ) / 60 < sieveAlpha 37 := by
  have hs : sieveExtraPrimes 37 =
      ({7, 11, 13, 17, 19, 23, 29, 31, 37} : Finset ℕ) := by decide
  rw [sieveAlpha, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton, not_false_eq_true, or_false, false_or]

private theorem alpha_43 : (13 : ℝ) / 125 < sieveAlpha 43 := by
  have hs : sieveExtraPrimes 43 =
      ({7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43} : Finset ℕ) := by decide
  rw [sieveAlpha, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton, not_false_eq_true, or_false, false_or]

private theorem alpha_47 : (99 : ℝ) / 1000 < sieveAlpha 47 := by
  have hs : sieveExtraPrimes 47 =
      ({7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ) := by decide
  rw [sieveAlpha, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton, not_false_eq_true, or_false, false_or]

private theorem alpha_53 : (47 : ℝ) / 500 < sieveAlpha 53 := by
  have hs : sieveExtraPrimes 53 =
      ({7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53} : Finset ℕ) := by decide
  rw [sieveAlpha, hs]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton, not_false_eq_true, or_false, false_or]

private theorem five_band_numeric (n u ν α a u₀ ν₀ : ℝ)
    (hn : 1024 ≤ n) (hu : u₀ ≤ u) (hu₀ : 4 ≤ u₀) (hν : ν ≤ ν₀)
    (ha : a ≤ α) (ha0 : 0 ≤ a)
    (hcorner : 1024 < a * (u₀ / 2 + 46 / 15) * 1024 -
      ((22 * u₀ + 24) / 15) * ν₀)
    (hslopeu : 0 ≤ a * 512 - 22 * ν₀ / 15)
    (hslopen : 0 ≤ a * (u₀ / 2 + 46 / 15) - 1) :
    n < α * (u / 2 + 46 / 15) * n - ((22 * u + 24) / 15) * ν := by
  have hu4 : 4 ≤ u := hu₀.trans hu
  have hslopeN : 0 ≤ a * (u / 2 + 46 / 15) - 1 := by nlinarith
  have hdu := mul_nonneg (sub_nonneg.mpr hu) hslopeu
  have hdn := mul_nonneg (sub_nonneg.mpr hn) hslopeN
  have hbase : n < a * (u / 2 + 46 / 15) * n -
      ((22 * u + 24) / 15) * ν₀ := by nlinarith
  have hαgain := mul_nonneg (sub_nonneg.mpr ha)
    (show 0 ≤ (u / 2 + 46 / 15) * n by positivity)
  have hνgain := mul_nonneg (sub_nonneg.mpr hν)
    (show 0 ≤ (22 * u + 24) / 15 by positivity)
  nlinarith

private theorem five_band_from_corner (n q u u₀ ν₀ : ℕ) (a : ℝ)
    (hn : 1024 ≤ n) (hu : u₀ ≤ u) (hu₀ : 4 ≤ u₀)
    (hν : sieveNu q ≤ ν₀) (ha : a ≤ sieveAlpha q) (ha0 : 0 ≤ a)
    (hcorner : 1024 < a * ((u₀ : ℝ) / 2 + 46 / 15) * 1024 -
      ((22 * (u₀ : ℝ) + 24) / 15) * ν₀)
    (hslopeu : 0 ≤ a * 512 - 22 * (ν₀ : ℝ) / 15)
    (hslopen : 0 ≤ a * ((u₀ : ℝ) / 2 + 46 / 15) - 1) :
    (n : ℝ) < sieveAlpha q * ((u : ℝ) / 2 + 46 / 15) * n -
      ((22 * (u : ℝ) + 24) / 15) * (sieveNu q : ℝ) :=
  five_band_numeric n u (sieveNu q) (sieveAlpha q) a u₀ ν₀
    (by exact_mod_cast hn) (by exact_mod_cast hu) (by exact_mod_cast hu₀)
    (by exact_mod_cast hν) ha ha0 hcorner hslopeu hslopen

/-- `arith:lem:no-core-small-primes`: the five numerical bands, for all `n≥1024`. -/
theorem small_support_prime_numeric (n q u : ℕ)
    (hn : 1024 ≤ n) (hq17 : 17 ≤ q) (hq53 : q ≤ 53) (hp : Nat.Prime q)
    (hcut : q < 2 * (u - 1)) :
    (n : ℝ) < sieveAlpha q * ((u : ℝ) / 2 + 46 / 15) * n -
      ((22 * (u : ℝ) + 24) / 15) * (sieveNu q : ℝ) := by
  have hbands : q ≤ 23 ∨ (29 ≤ q ∧ q ≤ 37) ∨
      (41 ≤ q ∧ q ≤ 43) ∨ q = 47 ∨ q = 53 := by
    interval_cases q <;> first | omega | (exfalso; norm_num at hp)
  rcases hbands with hq | hq | hq | rfl | rfl
  · have hν : sieveNu 23 = 7 := by decide
    apply five_band_from_corner n q u 10 7 (7 / 50) hn (by omega) (by decide)
      (by simpa [hν] using sieveNu_mono hq) (alpha_23.le.trans (sieveAlpha_antitone hq))
    all_goals norm_num
  · have hν : sieveNu 37 = 10 := by decide
    apply five_band_from_corner n q u 16 10 (7 / 60) hn (by omega) (by decide)
      (by simpa [hν] using sieveNu_mono hq.2)
      (alpha_37.le.trans (sieveAlpha_antitone hq.2))
    all_goals norm_num
  · have hν : sieveNu 43 = 12 := by decide
    apply five_band_from_corner n q u 22 12 (13 / 125) hn (by omega) (by decide)
      (by simpa [hν] using sieveNu_mono hq.2)
      (alpha_43.le.trans (sieveAlpha_antitone hq.2))
    all_goals norm_num
  · have hν : sieveNu 47 = 13 := by decide
    apply five_band_from_corner n 47 u 25 13 (99 / 1000) hn (by omega) (by decide)
      hν.le alpha_47.le
    all_goals norm_num
  · have hν : sieveNu 53 = 14 := by decide
    apply five_band_from_corner n 53 u 28 14 (47 / 500) hn (by omega) (by decide)
      hν.le alpha_53.le
    all_goals norm_num

private theorem middle_numeric (n u δ α a u₀ δ₀ : ℝ)
    (hn : 32768 ≤ n) (hu : u₀ ≤ u) (hu₀ : 4 ≤ u₀) (hδ : δ ≤ δ₀)
    (ha : a ≤ α) (ha0 : 0 ≤ a)
    (hcorner : 32768 < (u₀ + 4) / 2 * a * 32768 - 2 * (u₀ - 2) * δ₀)
    (hslopeu : 0 ≤ a * 16384 - 2 * δ₀)
    (hslopen : 0 ≤ a * (u₀ + 4) / 2 - 1) :
    n < (u + 4) / 2 * α * n - 2 * (u - 2) * δ := by
  have hu4 : 4 ≤ u := hu₀.trans hu
  have hslopeN : 0 ≤ a * (u + 4) / 2 - 1 := by nlinarith
  have hdu := mul_nonneg (sub_nonneg.mpr hu) hslopeu
  have hdn := mul_nonneg (sub_nonneg.mpr hn) hslopeN
  have hbase : n < (u + 4) / 2 * a * n - 2 * (u - 2) * δ₀ := by nlinarith
  have hαgain := mul_nonneg (sub_nonneg.mpr ha)
    (show 0 ≤ (u + 4) / 2 * n by positivity)
  have hδgain := mul_nonneg (sub_nonneg.mpr hδ)
    (show 0 ≤ 2 * (u - 2) by linarith)
  nlinarith

private theorem middle_from_corner (n q u u₀ : ℕ) (a δ₀ : ℝ)
    (hn : 32768 ≤ n) (hu : u₀ ≤ u) (hu₀ : 4 ≤ u₀)
    (hδ : middleDelta q ≤ δ₀) (ha : a ≤ middleAlpha q) (ha0 : 0 ≤ a)
    (hcorner : 32768 < ((u₀ : ℝ) + 4) / 2 * a * 32768 -
      2 * ((u₀ : ℝ) - 2) * δ₀)
    (hslopeu : 0 ≤ a * 16384 - 2 * δ₀)
    (hslopen : 0 ≤ a * ((u₀ : ℝ) + 4) / 2 - 1) :
    (n : ℝ) < ((u : ℝ) + 4) / 2 * middleAlpha q * n -
      2 * ((u : ℝ) - 2) * middleDelta q :=
  middle_numeric n u (middleDelta q) (middleAlpha q) a u₀ δ₀
    (by exact_mod_cast hn) (by exact_mod_cast hu) (by exact_mod_cast hu₀)
    hδ ha ha0 hcorner hslopeu hslopen

/-- `arith:lem:no-core-middle-primes`: both numerical bands, for all `n≥32768`. -/
theorem middle_support_prime_numeric (n q u : ℕ)
    (hn : 32768 ≤ n) (hq59 : 59 ≤ q) (hq271 : q ≤ 271) (hp : Nat.Prime q)
    (hcut : q < 2 * (u - 1)) :
    (n : ℝ) < ((u : ℝ) + 4) / 2 * middleAlpha q * n -
      2 * ((u : ℝ) - 2) * middleDelta q := by
  by_cases hq149 : q ≤ 149
  · apply middle_from_corner n q u 31 (13 / 200) 75 hn (by omega) (by decide)
      (middleDelta_upper_149 hq149) (middleAlpha_lower_149 hq149).le
    all_goals norm_num
  · have hq151 : 151 ≤ q := by
      by_contra h
      have hq150 : q = 150 := by omega
      have hp150 : Nat.Prime 150 := by simpa [hq150] using hp
      norm_num at hp150
    apply middle_from_corner n q u 77 (1 / 25) 135 hn (by omega) (by decide)
      (middleDelta_upper_271 hq271) (middleAlpha_lower_271 hq271).le
    all_goals norm_num

end WeightedPilz.Arithmetic

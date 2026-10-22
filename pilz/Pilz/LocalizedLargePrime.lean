import Pilz.LocalizedTail
import Pilz.LocalizedPrimeCount
import Pilz.SieveDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Assembly of the manuscript's large support-prime estimate, using the
independently checked elementary odd-cutoff bound in `SieveDensity`. -/

noncomputable section

namespace Pilz

theorem large_sieve_main_coefficient (q u ρ : ℝ) (hq : 277 ≤ q)
    (hu : q / 2 < u) (hρ : 1 / (2 * Real.sqrt q) < ρ) :
    2 < u * ρ / 2 := by
  have hqpos : 0 < q := by linarith
  have hspos := Real.sqrt_pos.mpr hqpos
  have hsq := Real.sq_sqrt hqpos.le
  have hs : 16 < Real.sqrt q := by nlinarith
  have hρpos : 0 < ρ := lt_trans (by positivity) hρ
  have hρs : (1 / 2 : ℝ) < ρ * Real.sqrt q := by
    have hh := (div_lt_iff₀ (show 0 < 2 * Real.sqrt q by positivity)).mp hρ
    nlinarith
  have hρq : Real.sqrt q / 2 < ρ * q := by
    have hh := mul_lt_mul_of_pos_right hρs hspos
    have heq := congrArg (fun x : ℝ => ρ * x) hsq
    nlinarith
  have huρ := mul_lt_mul_of_pos_right hu hρpos
  nlinarith

theorem localized_expansion_large_support_of_density (n q : ℕ) (D : Poly)
    (hn : 32768 ≤ n) (hq : 277 ≤ q)
    (huL : (weight D : ℝ) < (20 / 7) * Real.log n)
    (hcut : q < 2 * (weight D - 1)) (hlargest : LargestPrime D q)
    (hρ : 1 / (2 * Real.sqrt (q : ℝ)) < sieveDensity q) :
    (5 / 4 : ℝ) * n < weight (interval n * D) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hu2 : 2 ≤ weight D := by omega
  have hcutR : (q : ℝ) < 2 * ((weight D : ℝ) - 1) := by
    have hh : (q : ℝ) < 2 * ((weight D - 1 : ℕ) : ℝ) := by exact_mod_cast hcut
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at hh
  have hqR : (277 : ℝ) ≤ q := by exact_mod_cast hq
  have hqL : (q : ℝ) < (40 / 7) * Real.log n := by linarith
  have hL : (48 : ℝ) ≤ Real.log n := by linarith
  have hπ := primeCount_large_linear_bound q (by omega)
  have hδ := large_sieve_delta_bound q (Real.log n) (by omega) hπ hqL
  have herror := large_sieve_error (Real.log n) (weight D) (sieveDelta q)
    hL (Nat.cast_nonneg _) huL hδ.le
  rw [Real.exp_log hnpos] at herror
  have hcoef := large_sieve_main_coefficient (q : ℝ) (weight D) (sieveDensity q)
    hqR (by linarith) hρ
  have hI := roughRealIntervalCount_primesUpTo_lower (q := q) (by omega)
    (n : ℝ) hnpos.le
  rw [roughRealIntervalCount_natCast] at hI
  have hbudgetNat := weight_interval_mul_ge_index_one (primesUpTo q) n D
    (primesUpTo_prime q) (largestPrime_vars_subset D q hlargest)
  have hbudget : (weight D : ℝ) * roughIntervalCount (primesUpTo q) n ≤
      weight (interval n * D) := by exact_mod_cast hbudgetNat
  have hmul := mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg (weight D) : (0 : ℝ) ≤ _)
  have hmain := mul_lt_mul_of_pos_right hcoef hnpos
  nlinarith

theorem localized_expansion_large_support (n q : ℕ) (D : Poly)
    (hn : 32768 ≤ n) (hq : 277 ≤ q)
    (huL : (weight D : ℝ) < (20 / 7) * Real.log n)
    (hcut : q < 2 * (weight D - 1)) (hlargest : LargestPrime D q) :
    (5 / 4 : ℝ) * n < weight (interval n * D) :=
  localized_expansion_large_support_of_density n q D hn hq huL hcut hlargest
    (sieveDensity_sqrt_lower hlargest.1 (by omega))

end Pilz

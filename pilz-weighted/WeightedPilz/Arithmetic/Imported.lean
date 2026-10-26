import Pilz.FreshCount
import Pilz.LocalizedSmallQ
import Pilz.LocalizedBands
import Pilz.LocalizedTail
import Pilz.LocalizedPrimeCount
import Pilz.SieveDensity

/-!
# Field-independent arithmetic from the frozen weighted manuscript

These declarations reuse proved statements about actual prime and rough-number
counts. None assumes an interval support theorem. The polynomial estimates in
the earlier `Pilz` development are not used here. Analytic estimates have their
full unbounded domains; the finite estimates use kernel-checked integer counts.
-/

noncomputable section

namespace WeightedPilz.Arithmetic

/-- `arith:prop:written-low-range`, with the negative constant moved left. -/
theorem finite_prime_budgets {n : ℕ} (hn : 67 ≤ n) (hn' : n ≤ 1023) :
    Nat.sqrt n ≤ Pilz.freshCount n ∧
      n + 48 ≤ 10 * Pilz.freshCount n + 4 * Pilz.primeCount (n / 2) +
        2 * Pilz.primeCount (n / 3) + 2 * Pilz.primeCount (n / 5) := by
  have h := Pilz.finitePrimeBounds_67_1023 hn hn'
  exact ⟨h.1, h.2.2⟩

/-- `arith:lem:no-core-fresh-budget`, valid without an upper bound on `n`. -/
theorem fresh_count_sqrt (n : ℕ) (hn : 67 ≤ n) :
    Nat.sqrt n ≤ Pilz.freshCount n := Pilz.freshPrimeCountBound n hn

theorem fresh_count_eight (n : ℕ) (hn : 67 ≤ n) :
    8 ≤ Pilz.freshCount n := Pilz.eight_le_freshCount n hn

/-- The middle range is proved analytically, rather than by a finite table. -/
theorem fresh_count_div_thirty {n : ℕ} (hn : 1024 ≤ n) (hn' : n ≤ 32768) :
    (n : ℝ) / 30 < Pilz.freshCount n :=
  Pilz.Chebyshev.freshCount_gt_div_thirty hn hn'

/-- The logarithmic fresh-prime lower bound on the unbounded range. -/
theorem fresh_count_log {n : ℕ} (hn : 32768 ≤ n) :
    7 * (n : ℝ) / (20 * Real.log n) < Pilz.freshCount n :=
  Pilz.Chebyshev.freshCount_gt_log hn

/-- The stronger square-root comparison required in the frozen manuscript. -/
theorem log_lt_seven_over_120_sqrt {x : ℝ} (hx : 32768 ≤ x) :
    Real.log x < (7 / 120) * Real.sqrt x := by
  have hxpos : 0 < x := by linarith
  have hL := Real.log_le_log (by norm_num : (0 : ℝ) < 32768) hx
  have hs : (180 : ℝ) < Real.sqrt 32768 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hpos : 0 < 1 + (Real.log x - Real.log 32768) / 2 := by linarith
  have hexp := Real.add_one_le_exp ((Real.log x - Real.log 32768) / 2)
  have hid : Real.sqrt x = Real.sqrt 32768 *
      Real.exp ((Real.log x - Real.log 32768) / 2) := by
    rw [Pilz.Chebyshev.sqrt_eq_exp_half_log hxpos,
      Pilz.Chebyshev.sqrt_eq_exp_half_log (by norm_num : (0 : ℝ) < 32768),
      ← Real.exp_add]
    congr 1
    ring
  have hprod := mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg (32768 : ℝ))
  have hstrict := mul_lt_mul_of_pos_right hs hpos
  rw [← hid] at hprod
  have hgrowth := hstrict.trans_le (by simpa only [add_comm] using hprod)
  nlinarith [Pilz.Chebyshev.log_32768_bounds.2]

theorem six_sqrt_lt_fresh_log {n : ℕ} (hn : 32768 ≤ n) :
    6 * Real.sqrt (n : ℝ) < 7 * (n : ℝ) / (20 * Real.log n) := by
  have hnreal : (32768 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hspos := Real.sqrt_pos.mpr hnpos
  have hsquare := Real.sq_sqrt hnpos.le
  have hmul := mul_lt_mul_of_pos_right (log_lt_seven_over_120_sqrt hnreal) hspos
  apply (lt_div_iff₀ (show 0 < 20 * Real.log (n : ℝ) by positivity)).mpr
  nlinarith

theorem fresh_count_six_sqrt {n : ℕ} (hn : 32768 ≤ n) :
    6 * Real.sqrt (n : ℝ) < Pilz.freshCount n :=
  (six_sqrt_lt_fresh_log hn).trans (fresh_count_log hn)

/-- The complete Chebyshev inequalities used in the analytic argument. -/
theorem elementary_chebyshev {x : ℝ} (hx : 30 ≤ x) :
    Pilz.Chebyshev.mu1 * x - 5 / 2 * Real.log x + 2 < Pilz.Chebyshev.psi x ∧
      Pilz.Chebyshev.psi x < Pilz.Chebyshev.mu2 * x + Pilz.Chebyshev.eta x :=
  ⟨Pilz.Chebyshev.psi_lower hx, Pilz.Chebyshev.psi_upper (by linarith)⟩

theorem prime_power_error {x : ℝ} (hx : 256 ≤ x) :
    0 ≤ Pilz.Chebyshev.psi x - Pilz.Chebyshev.theta x ∧
      Pilz.Chebyshev.psi x - Pilz.Chebyshev.theta x < 8 / 3 * Real.sqrt x :=
  ⟨Pilz.Chebyshev.psi_sub_theta_nonneg x, Pilz.Chebyshev.psi_sub_theta_lt hx⟩

/-- Exact finite reciprocal sums; the summation sets consist of actual primes. -/
theorem reciprocal_sum_7_53 : Pilz.primeReciprocalSum 7 53 < (259 : ℝ) / 400 :=
  Pilz.reciprocal_sum_7_53

theorem reciprocal_sum_11_149 : Pilz.primeReciprocalSum 11 149 < (229 : ℝ) / 320 :=
  Pilz.reciprocal_sum_11_149

theorem reciprocal_sum_11_271 : Pilz.primeReciprocalSum 11 271 < (33 : ℝ) / 40 :=
  Pilz.reciprocal_sum_11_271

/-- `arith:prop:small-prime-profile-replacement`: pure count conclusions. -/
theorem small_prime_profiles (n : ℕ) (hn : 67 ≤ n) :
    n ≤ Pilz.smallQBudget 7 1 1 0 n ∧
      n ≤ Pilz.smallQBudget 11 3 2 0 n ∧
      n ≤ Pilz.smallQBudget 13 4 2 1 n :=
  ⟨Pilz.smallQBudget_seven_ge n hn, Pilz.smallQBudget_eleven_ge n hn,
    Pilz.smallQBudget_thirteen_ge n hn⟩

theorem small_prime_profiles_linear (n : ℕ) :
    ((116 : ℝ) * n - 1372) / 105 ≤ (Pilz.smallQBudget 7 1 1 0 n : ℝ) ∧
      ((4366 : ℝ) * n - 116424) / 3465 ≤ (Pilz.smallQBudget 11 3 2 0 n : ℝ) ∧
      ((18952 : ℝ) * n - 840840) / 15015 ≤
        (Pilz.smallQBudget 13 4 2 1 n : ℝ) :=
  ⟨Pilz.smallQBudget_seven_linear n, Pilz.smallQBudget_eleven_linear n,
    Pilz.smallQBudget_thirteen_linear n⟩

/-- `arith:lem:no-core-odd-product`: no finite cutoff on the prime. -/
theorem prime_product_sqrt {q : ℕ} (hq : Nat.Prime q) (hq3 : 3 ≤ q) :
    1 / (2 * Real.sqrt (q : ℝ)) < Pilz.sieveDensity q :=
  Pilz.sieveDensity_sqrt_lower hq hq3

theorem large_prime_count (q : ℕ) (hq : 221 ≤ q) :
    (Pilz.primeCount q : ℝ) < (16 / 77) * q + 6 :=
  Pilz.primeCount_large_linear_bound q hq

theorem large_sieve_error (L u δ : ℝ) (hL : 48 ≤ L) (hu : 0 ≤ u)
    (huL : u < (20 / 7) * L)
    (hδ : δ ≤ (112 / 15) * Real.exp ((64 / 77) * L)) :
    2 * u * δ < (3 / 4) * Real.exp L :=
  Pilz.large_sieve_error L u δ hL hu huL hδ

/-- Numerical main term in the unbounded support-prime estimate. -/
theorem large_sieve_main (q u ρ : ℝ) (hq : 277 ≤ q)
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

/-- The unbounded counting estimate underlying `arith:lem:no-core-large-primes`.
An algebraic component bound can use this theorem over any coefficient field. -/
theorem large_support_prime_count (n q u : ℕ)
    (hn : 32768 ≤ n) (hq : 277 ≤ q) (hp : Nat.Prime q)
    (huL : (u : ℝ) < (20 / 7) * Real.log n)
    (hcut : q < 2 * (u - 1)) :
    (5 / 4 : ℝ) * n < (u : ℝ) * Pilz.roughIntervalCount (Pilz.primesUpTo q) n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hu2 : 2 ≤ u := by omega
  have hcutR : (q : ℝ) < 2 * ((u : ℝ) - 1) := by
    have hh : (q : ℝ) < 2 * ((u - 1 : ℕ) : ℝ) := by exact_mod_cast hcut
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at hh
  have hqR : (277 : ℝ) ≤ q := by exact_mod_cast hq
  have hqL : (q : ℝ) < (40 / 7) * Real.log n := by linarith
  have hL : (48 : ℝ) ≤ Real.log n := by linarith
  have hπ := large_prime_count q (by omega)
  have hδ := Pilz.large_sieve_delta_bound q (Real.log n) (by omega) hπ hqL
  have herror := large_sieve_error (Real.log n) u (Pilz.sieveDelta q)
    hL (Nat.cast_nonneg _) huL hδ.le
  rw [Real.exp_log hnpos] at herror
  have hcoef := large_sieve_main (q : ℝ) u (Pilz.sieveDensity q)
    hqR (by linarith) (prime_product_sqrt hp (by omega))
  have hI := Pilz.roughRealIntervalCount_primesUpTo_lower (q := q) (by omega)
    (n : ℝ) hnpos.le
  rw [Pilz.roughRealIntervalCount_natCast] at hI
  have hmul := mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg u : (0 : ℝ) ≤ _)
  have hmain := mul_lt_mul_of_pos_right hcoef hnpos
  nlinarith

end WeightedPilz.Arithmetic

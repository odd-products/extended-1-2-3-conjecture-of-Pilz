import WeightedPilz.Arithmetic.Counts
import Pilz.Sieve30
import Pilz.SieveEstimates
import Pilz.PrimeLinearBound

/-! The exact eleven-rough semiprime sieve below 1800, including real inputs.
The finite certificate checks the increment identity; induction then identifies
the expression with the actual prime count, without assuming a prime table. -/

namespace WeightedPilz.Arithmetic
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def semiprimePrime (i : ℕ) : ℕ := [13, 17, 19, 23, 29, 31, 37, 41].getD (i - 1) 0

def sieveElevenFormula (n : ℕ) : ℕ :=
  (Pilz.sieve30Formula n - Pilz.sieve30Formula (n / 7)) -
    (Pilz.sieve30Formula (n / 11) - Pilz.sieve30Formula (n / 11 / 7))

private theorem seven_set :
    ({2, 3, 5, 7} : Finset ℕ) = insert 7 {2, 3, 5} := by decide
private theorem eleven_set :
    ({2, 3, 5, 7, 11} : Finset ℕ) = insert 11 {2, 3, 5, 7} := by decide
private theorem five_primes : ∀ p ∈ ({2, 3, 5} : Finset ℕ), p.Prime := by decide
private theorem seven_primes : ∀ p ∈ ({2, 3, 5, 7} : Finset ℕ), p.Prime := by decide

theorem roughCount_eleven_formula (n : ℕ) :
    Pilz.roughCount {2, 3, 5, 7, 11} n = sieveElevenFormula n := by
  have hseven (m : ℕ) : Pilz.roughCount {2, 3, 5, 7} m =
      Pilz.sieve30Formula m - Pilz.sieve30Formula (m / 7) := by
    rw [seven_set, Pilz.roughCount_insert {2, 3, 5} 7 m five_primes (by decide) (by decide),
      Pilz.roughCount_two_three_five_formula, Pilz.roughCount_two_three_five_formula]
  rw [eleven_set, Pilz.roughCount_insert {2, 3, 5, 7} 11 n seven_primes (by decide) (by decide),
    hseven, hseven]
  rfl

def semiprimeCorrection (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 8, (Pilz.roughCount {2, 3, 5, 7, 11} (n / semiprimePrime i) - i)

private def fastSemiprimeCorrection (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 8, (sieveElevenFormula (n / semiprimePrime i) - i)

private theorem semiprimeCorrection_eq (n : ℕ) :
    semiprimeCorrection n = fastSemiprimeCorrection n := by
  simp only [semiprimeCorrection, fastSemiprimeCorrection, roughCount_eleven_formula]

private def SemiprimeIncrement (n : ℕ) : Prop :=
  sieveElevenFormula (n + 1) + fastSemiprimeCorrection n =
    sieveElevenFormula n + fastSemiprimeCorrection (n + 1) +
      (if kernelPrime (n + 1) then 1 else 0)

private instance (n : ℕ) : Decidable (SemiprimeIncrement n) := inferInstanceAs (Decidable (_ = _))

private theorem semiprime_increment_11_138 :
    ∀ n ∈ Finset.Icc 11 138, SemiprimeIncrement n := by decide +kernel

private theorem semiprime_increment_139_266 :
    ∀ n ∈ Finset.Icc 139 266, SemiprimeIncrement n := by decide +kernel

private theorem semiprime_increment_267_394 :
    ∀ n ∈ Finset.Icc 267 394, SemiprimeIncrement n := by decide +kernel

private theorem semiprime_increment_395_522 :
    ∀ n ∈ Finset.Icc 395 522, SemiprimeIncrement n := by decide +kernel

private theorem semiprime_increment_523_650 :
    ∀ n ∈ Finset.Icc 523 650, SemiprimeIncrement n := by decide +kernel

private theorem semiprime_increment_651_778 :
    ∀ n ∈ Finset.Icc 651 778, SemiprimeIncrement n := by decide +kernel

private theorem semiprime_increment_779_906 :
    ∀ n ∈ Finset.Icc 779 906, SemiprimeIncrement n := by decide +kernel

private theorem semiprime_increment_907_1034 :
    ∀ n ∈ Finset.Icc 907 1034, SemiprimeIncrement n := by decide +kernel

private theorem semiprime_increment_1035_1162 :
    ∀ n ∈ Finset.Icc 1035 1162, SemiprimeIncrement n := by decide +kernel

private theorem semiprime_increment_1163_1290 :
    ∀ n ∈ Finset.Icc 1163 1290, SemiprimeIncrement n := by decide +kernel

private theorem semiprime_increment_1291_1418 :
    ∀ n ∈ Finset.Icc 1291 1418, SemiprimeIncrement n := by decide +kernel

private theorem semiprime_increment_1419_1546 :
    ∀ n ∈ Finset.Icc 1419 1546, SemiprimeIncrement n := by decide +kernel

private theorem semiprime_increment_1547_1674 :
    ∀ n ∈ Finset.Icc 1547 1674, SemiprimeIncrement n := by decide +kernel

private theorem semiprime_increment_1675_1798 :
    ∀ n ∈ Finset.Icc 1675 1798, SemiprimeIncrement n := by decide +kernel

private theorem semiprime_increment {n : ℕ} (hn : 11 ≤ n) (hn' : n ≤ 1798) :
    SemiprimeIncrement n := by
  by_cases h0 : n ≤ 138
  · exact semiprime_increment_11_138 n (Finset.mem_Icc.mpr ⟨by omega, h0⟩)
  by_cases h1 : n ≤ 266
  · exact semiprime_increment_139_266 n (Finset.mem_Icc.mpr ⟨by omega, h1⟩)
  by_cases h2 : n ≤ 394
  · exact semiprime_increment_267_394 n (Finset.mem_Icc.mpr ⟨by omega, h2⟩)
  by_cases h3 : n ≤ 522
  · exact semiprime_increment_395_522 n (Finset.mem_Icc.mpr ⟨by omega, h3⟩)
  by_cases h4 : n ≤ 650
  · exact semiprime_increment_523_650 n (Finset.mem_Icc.mpr ⟨by omega, h4⟩)
  by_cases h5 : n ≤ 778
  · exact semiprime_increment_651_778 n (Finset.mem_Icc.mpr ⟨by omega, h5⟩)
  by_cases h6 : n ≤ 906
  · exact semiprime_increment_779_906 n (Finset.mem_Icc.mpr ⟨by omega, h6⟩)
  by_cases h7 : n ≤ 1034
  · exact semiprime_increment_907_1034 n (Finset.mem_Icc.mpr ⟨by omega, h7⟩)
  by_cases h8 : n ≤ 1162
  · exact semiprime_increment_1035_1162 n (Finset.mem_Icc.mpr ⟨by omega, h8⟩)
  by_cases h9 : n ≤ 1290
  · exact semiprime_increment_1163_1290 n (Finset.mem_Icc.mpr ⟨by omega, h9⟩)
  by_cases h10 : n ≤ 1418
  · exact semiprime_increment_1291_1418 n (Finset.mem_Icc.mpr ⟨by omega, h10⟩)
  by_cases h11 : n ≤ 1546
  · exact semiprime_increment_1419_1546 n (Finset.mem_Icc.mpr ⟨by omega, h11⟩)
  by_cases h12 : n ≤ 1674
  · exact semiprime_increment_1547_1674 n (Finset.mem_Icc.mpr ⟨by omega, h12⟩)
  exact semiprime_increment_1675_1798 n (Finset.mem_Icc.mpr ⟨by omega, hn'⟩)

/-- The natural-number form of the exact displayed semiprime sieve. -/
theorem small_prime_sieve_nat {n : ℕ} (hn : 11 ≤ n) (hn' : n ≤ 1799) :
    Pilz.primeCount n + semiprimeCorrection n =
      4 + Pilz.roughCount {2, 3, 5, 7, 11} n := by
  have aux : ∀ n : ℕ, 11 ≤ n → n ≤ 1799 →
      Pilz.primeCount n + fastSemiprimeCorrection n = 4 + sieveElevenFormula n := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro _
      unfold Pilz.primeCount
      simp only [primePredicate_eq]
      decide +kernel
    | succ m hm ih =>
      intro hm'
      have hprev := ih (by omega)
      have hstep := semiprime_increment hm (by omega)
      unfold SemiprimeIncrement at hstep
      rw [Pilz.primeCount_succ]
      have hprime : (if m.succ.Prime then 1 else 0) =
          (if kernelPrime (m + 1) then 1 else 0) := by
        simp only [kernelPrime_iff, Nat.succ_eq_add_one]
      rw [hprime]
      omega
  simpa only [semiprimeCorrection_eq, roughCount_eleven_formula] using aux n hn hn'

/-- Inclusion-exclusion for the actual eleven-rough count, for every real input. -/
theorem roughRealCount_eleven_eq_five (x : ℝ) :
    Pilz.roughRealCount {2, 3, 5, 7, 11} x =
      Pilz.roughRealCount {2, 3, 5} x -
      Pilz.roughRealCount {2, 3, 5} (x / 7) -
      Pilz.roughRealCount {2, 3, 5} (x / 11) +
      Pilz.roughRealCount {2, 3, 5} (x / 77) := by
  have hseven (y : ℝ) : Pilz.roughRealCount {2, 3, 5, 7} y =
      Pilz.roughRealCount {2, 3, 5} y - Pilz.roughRealCount {2, 3, 5} (y / 7) := by
    rw [seven_set]
    exact Pilz.roughRealCount_insert {2, 3, 5} 7 y five_primes (by decide) (by decide)
  rw [eleven_set, Pilz.roughRealCount_insert {2, 3, 5, 7} 11 x seven_primes (by decide) (by decide),
    hseven, hseven]
  have hx : x / 11 / 7 = x / 77 := by ring
  norm_num only [Nat.cast_ofNat]
  rw [hx]
  ring

noncomputable def primeRealCount (x : ℝ) : ℝ := (Pilz.primeCount ⌊x⌋₊ : ℝ)

private theorem nat_sub_cast_eq_max (a b : ℕ) :
    ((a - b : ℕ) : ℝ) = max ((a : ℝ) - b) 0 := by
  by_cases h : b ≤ a
  · rw [Nat.cast_sub h, max_eq_left]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · have h' : a ≤ b := by omega
    rw [Nat.sub_eq_zero_of_le h', Nat.cast_zero, max_eq_right]
    exact sub_nonpos.mpr (by exact_mod_cast h')

/-- The manuscript's exact formula for every real eleven through 1799. -/
theorem small_prime_sieve (x : ℝ) (hx : 11 ≤ x) (hx' : x ≤ 1799) :
    primeRealCount x = 4 + Pilz.roughRealCount {2, 3, 5, 7, 11} x -
      ∑ i ∈ Finset.Icc 1 8,
        max (Pilz.roughRealCount {2, 3, 5, 7, 11} (x / (semiprimePrime i : ℝ)) - (i : ℝ)) 0 := by
  have hfloor : 11 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hfloor' : ⌊x⌋₊ ≤ 1799 := by
    have h := (Nat.floor_le (by linarith : 0 ≤ x)).trans hx'
    exact_mod_cast h
  have hnat := small_prime_sieve_nat hfloor hfloor'
  have hreal : (Pilz.primeCount ⌊x⌋₊ : ℝ) + (semiprimeCorrection ⌊x⌋₊ : ℝ) =
      4 + (Pilz.roughCount {2, 3, 5, 7, 11} ⌊x⌋₊ : ℝ) := by exact_mod_cast hnat
  have hcorr : (semiprimeCorrection ⌊x⌋₊ : ℝ) =
      ∑ i ∈ Finset.Icc 1 8,
        max (Pilz.roughRealCount {2, 3, 5, 7, 11} (x / (semiprimePrime i : ℝ)) - (i : ℝ)) 0 := by
    simp only [semiprimeCorrection, Nat.cast_sum, nat_sub_cast_eq_max,
      Pilz.roughRealCount, Nat.floor_div_natCast]
  rw [hcorr] at hreal
  change (Pilz.primeCount ⌊x⌋₊ : ℝ) =
    4 + (Pilz.roughCount {2, 3, 5, 7, 11} ⌊x⌋₊ : ℝ) - _
  linarith

end WeightedPilz.Arithmetic


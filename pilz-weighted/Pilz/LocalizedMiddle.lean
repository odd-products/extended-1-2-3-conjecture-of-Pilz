import Pilz.LocalizedBands

/-! The two middle support-prime bands, with the base sieve `2,3,5,7`. -/

noncomputable section

set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Pilz

open scoped BigOperators

def middleBase : Finset ℕ := {2, 3, 5, 7}
def middleExtraPrimes (q : ℕ) : Finset ℕ := primesUpTo q \ middleBase
def middleAlpha (q : ℕ) : ℝ := (8 / 35) * (1 - primeReciprocalSum 11 q)
def middleDelta (q : ℕ) : ℝ := (28 / 15) * ((primeCount q - 3 : ℕ) : ℝ)

private theorem middleBase_eq : middleBase = primesUpTo 7 := by decide

private theorem middleBase_prime (p : ℕ) (hp : p ∈ middleBase) : Nat.Prime p := by
  rw [middleBase_eq] at hp
  exact primesUpTo_prime 7 p hp

private theorem middleBase_subset {q : ℕ} (hq : 7 ≤ q) : middleBase ⊆ primesUpTo q := by
  rw [middleBase_eq]
  exact primesUpTo_mono hq

private theorem middle_union {q : ℕ} (hq : 7 ≤ q) :
    middleBase ∪ middleExtraPrimes q = primesUpTo q :=
  Finset.union_sdiff_of_subset (middleBase_subset hq)

private theorem middle_disjoint (q : ℕ) : Disjoint middleBase (middleExtraPrimes q) := by
  apply Finset.disjoint_left.mpr
  intro p hp hpExtra
  exact (Finset.mem_sdiff.mp hpExtra).2 hp

theorem middleExtraPrimes_eq_filter (q : ℕ) :
    middleExtraPrimes q = (primesUpTo q).filter (fun p => 11 ≤ p) := by
  ext p
  simp only [middleExtraPrimes, Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨hpq, hpnot⟩
    refine ⟨hpq, ?_⟩
    have hp := primesUpTo_prime q p hpq
    by_contra h
    have hp10 : p ≤ 10 := by omega
    interval_cases p <;> norm_num at hp <;> norm_num [middleBase] at hpnot
  · rintro ⟨hpq, hp11⟩
    refine ⟨hpq, ?_⟩
    simp only [middleBase, Finset.mem_insert, Finset.mem_singleton]
    omega

theorem primeReciprocalSum_mono {a b c : ℕ} (hbc : b ≤ c) :
    primeReciprocalSum a b ≤ primeReciprocalSum a c := by
  have hsub : (primesUpTo b).filter (fun p => a ≤ p) ⊆
      (primesUpTo c).filter (fun p => a ≤ p) := by
    intro p hp
    obtain ⟨hp, hpa⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨primesUpTo_mono hbc hp, hpa⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _hp _hnot => by positivity)

theorem middleAlpha_lower_149 {q : ℕ} (hq : q ≤ 149) : (13 : ℝ) / 200 < middleAlpha q := by
  have hs := (primeReciprocalSum_mono (a := 11) hq).trans_lt reciprocal_sum_11_149
  unfold middleAlpha
  linarith

theorem middleAlpha_lower_271 {q : ℕ} (hq : q ≤ 271) : (1 : ℝ) / 25 < middleAlpha q := by
  have hs := (primeReciprocalSum_mono (a := 11) hq).trans_lt reciprocal_sum_11_271
  unfold middleAlpha
  linarith

theorem middleDelta_upper_149 {q : ℕ} (hq : q ≤ 149) : middleDelta q ≤ 75 := by
  have hπ := primeCount_mono hq
  have h149 : primeCount 149 = 35 := by decide
  have hν : primeCount q - 3 ≤ 32 := by omega
  have hνR : ((primeCount q - 3 : ℕ) : ℝ) ≤ 32 := by exact_mod_cast hν
  unfold middleDelta
  linarith

theorem middleDelta_upper_271 {q : ℕ} (hq : q ≤ 271) : middleDelta q ≤ 135 := by
  have hπ := primeCount_mono hq
  have h271 : primeCount 271 = 58 := by decide
  have hν : primeCount q - 3 ≤ 55 := by omega
  have hνR : ((primeCount q - 3 : ℕ) : ℝ) ≤ 55 := by exact_mod_cast hν
  unfold middleDelta
  linarith

private theorem middleBase_discrepancy : RoughDiscrepancy middleBase (8 / 35) (28 / 15) := by
  have hprimes : ∀ p ∈ ({2, 3, 5} : Finset ℕ), Nat.Prime p := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  have h := roughDiscrepancy_insert {2, 3, 5} 7 (4 / 15) (14 / 15)
    hprimes (by decide) (by decide) roughRealCount_five_discrepancy
  have hset : insert 7 ({2, 3, 5} : Finset ℕ) = middleBase := by decide
  rw [hset] at h
  norm_num at h
  exact h

private theorem middle_error_card {q : ℕ} (hq : 7 ≤ q) :
    (1 : ℝ) + (middleExtraPrimes q).card = ((primeCount q - 3 : ℕ) : ℝ) := by
  have hcard : (middleExtraPrimes q).card = primeCount q - 4 := by
    rw [middleExtraPrimes, Finset.card_sdiff_of_subset (middleBase_subset hq), card_primesUpTo]
    rfl
  have hfour : 4 ≤ primeCount q := by
    have h := Finset.card_le_card (middleBase_subset hq)
    simpa [middleBase] using h
  have hnat : 1 + (middleExtraPrimes q).card = primeCount q - 3 := by omega
  exact_mod_cast hnat

theorem roughRealCount_primesUpTo_middle_lower {q : ℕ} (hq : 7 ≤ q)
    (x : ℝ) (hx : 0 ≤ x) :
    middleAlpha q * x - middleDelta q ≤ roughRealCount (primesUpTo q) x := by
  have hU : ∀ p ∈ middleExtraPrimes q, Nat.Prime p :=
    fun p hp => primesUpTo_prime q p (Finset.mem_sdiff.mp hp).1
  have h := roughRealCount_one_step middleBase (middleExtraPrimes q)
    (8 / 35) (28 / 15) x middleBase_prime hU (middle_disjoint q) middleBase_discrepancy hx
  rw [middle_union hq, middle_error_card hq] at h
  simpa [middleAlpha, primeReciprocalSum, middleExtraPrimes_eq_filter, middleDelta, mul_comm] using h

theorem roughRealIntervalCount_primesUpTo_middle_lower {q : ℕ} (hq : 7 ≤ q)
    (x : ℝ) (hx : 0 ≤ x) :
    middleAlpha q * x / 2 - 2 * middleDelta q ≤ roughRealIntervalCount (primesUpTo q) x := by
  have hU : ∀ p ∈ middleExtraPrimes q, Nat.Prime p :=
    fun p hp => primesUpTo_prime q p (Finset.mem_sdiff.mp hp).1
  have h := roughRealIntervalCount_one_step middleBase (middleExtraPrimes q)
    (8 / 35) (28 / 15) x middleBase_prime hU (middle_disjoint q) middleBase_discrepancy hx
  rw [middle_union hq, middle_error_card hq] at h
  simpa [middleAlpha, primeReciprocalSum, middleExtraPrimes_eq_filter, middleDelta,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- The middle-range sieve budget in the paper. -/
theorem localized_middle_budget (n q : ℕ) (D : Poly)
    (hq : 7 ≤ q) (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q)
    (hu : 4 ≤ weight D) :
    ((weight D : ℝ) + 4) / 2 * middleAlpha q * n -
      2 * ((weight D : ℝ) - 2) * middleDelta q ≤ (weight (interval n * D) : ℝ) := by
  have hbudget : 4 * (roughCount (primesUpTo q) n : ℝ) +
      ((weight D - 4 : ℕ) : ℝ) * roughIntervalCount (primesUpTo q) n ≤
        (weight (interval n * D) : ℝ) := by
    exact_mod_cast component_budget_four_paper q n D (by omega) hD hnorm hlargest hu
  have hcast : ((weight D - 4 : ℕ) : ℝ) = (weight D : ℝ) - 4 := by
    rw [Nat.cast_sub hu]
    norm_num
  rw [hcast] at hbudget
  have h1 := roughRealCount_primesUpTo_middle_lower hq (n : ℝ) (by positivity)
  have hI := roughRealIntervalCount_primesUpTo_middle_lower hq (n : ℝ) (by positivity)
  simp only [roughRealCount_natCast] at h1
  simp only [roughRealIntervalCount_natCast] at hI
  have huR : (4 : ℝ) ≤ weight D := by exact_mod_cast hu
  have hIprod := mul_le_mul_of_nonneg_left hI (sub_nonneg.mpr huR)
  nlinarith

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

private theorem localized_middle_from_corner (n q u₀ : ℕ) (D : Poly) (a δ₀ : ℝ)
    (hn : 32768 ≤ n) (hq : 7 ≤ q) (hu : u₀ ≤ weight D) (hu₀ : 4 ≤ u₀)
    (hδ : middleDelta q ≤ δ₀) (ha : a ≤ middleAlpha q) (ha0 : 0 ≤ a)
    (hcorner : 32768 < ((u₀ : ℝ) + 4) / 2 * a * 32768 - 2 * ((u₀ : ℝ) - 2) * δ₀)
    (hslopeu : 0 ≤ a * 16384 - 2 * δ₀)
    (hslopen : 0 ≤ a * ((u₀ : ℝ) + 4) / 2 - 1)
    (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    (n : ℝ) < weight (interval n * D) := by
  have hnum := middle_numeric (n : ℝ) (weight D : ℝ) (middleDelta q) (middleAlpha q)
    a u₀ δ₀ (by exact_mod_cast hn) (by exact_mod_cast hu) (by exact_mod_cast hu₀)
    hδ ha ha0 hcorner hslopeu hslopen
  exact hnum.trans_le (localized_middle_budget n q D hq hD hnorm hlargest (hu₀.trans hu))

/-- The two middle support-prime bands, uniformly beyond `n=32768`. -/
theorem localized_expansion_middle (n q : ℕ) (D : Poly)
    (hn : 32768 ≤ n) (hq59 : 59 ≤ q) (hq271 : q ≤ 271)
    (hcut : q < 2 * (weight D - 1)) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    (n : ℝ) < weight (interval n * D) := by
  by_cases hq149 : q ≤ 149
  · apply localized_middle_from_corner n q 31 D (13 / 200) 75 hn (by omega) (by omega) (by decide)
      (middleDelta_upper_149 hq149) (middleAlpha_lower_149 hq149).le
    all_goals first | assumption | norm_num
  · have hq151 : 151 ≤ q := by
      by_contra h
      have hq150 : q = 150 := by omega
      have hp : Nat.Prime 150 := by simpa [hq150] using hlargest.1
      norm_num at hp
    apply localized_middle_from_corner n q 77 D (1 / 25) 135 hn (by omega) (by omega) (by decide)
      (middleDelta_upper_271 hq271) (middleAlpha_lower_271 hq271).le
    all_goals first | assumption | norm_num

end Pilz

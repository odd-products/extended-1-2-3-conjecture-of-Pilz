import Pilz.ComponentProfile
import Pilz.Sieve30
import Pilz.SievePrimes

/-!
# Localized expansion for the smallest support primes

The cases 2, 3 and 5 use the actual component profile and exact initial
sieve formulas. No numerical component lower bound is assumed.
-/

noncomputable section

namespace Pilz

open scoped BigOperators

private theorem primesUpTo_two : primesUpTo 2 = ({2} : Finset ℕ) := by decide
private theorem primesUpTo_three : primesUpTo 3 = ({2, 3} : Finset ℕ) := by decide
private theorem primesUpTo_five : primesUpTo 5 = ({2, 3, 5} : Finset ℕ) := by decide

/-- A uniform profile can be summed over all rough components. -/
theorem uniform_component_budget (q n c : ℕ) (D : Poly)
    (hlargest : LargestPrime D q)
    (hprofile : ∀ j : ℕ, 1 ≤ j → c ≤ weight (smoothInterval (primesUpTo q) j * D)) :
    c * roughCount (primesUpTo q) n ≤ weight (interval n * D) := by
  classical
  calc
    _ = ∑ _b ∈ roughNumbers (primesUpTo q) n, c := by
      simp [roughCount, Nat.mul_comm]
    _ ≤ ∑ b ∈ roughNumbers (primesUpTo q) n,
        weight (smoothInterval (primesUpTo q) (n / b) * D) := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨hbpos, hbn, _⟩ := (mem_roughNumbers (primesUpTo q) n b).mp hb
      apply hprofile
      apply (Nat.le_div_iff_mul_le hbpos).mpr
      simpa using hbn
    _ = _ := (weight_interval_mul_eq_sum_rough_components _ n D
      (primesUpTo_prime q) (largestPrime_vars_subset D q hlargest)).symm

theorem localized_q_two (n : ℕ) (D : Poly) (hD : D ≠ 0)
    (_hnorm : Normalized D) (hlargest : LargestPrime D 2)
    (hcut : 2 < 2 * (weight D - 1)) : n ≤ weight (interval n * D) := by
  have hu : 2 ≤ weight D := by omega
  have hprofile : ∀ j : ℕ, 1 ≤ j → 2 ≤ weight (smoothInterval (primesUpTo 2) j * D) := by
    intro j hj
    by_cases h1 : j = 1
    · simpa [h1, smoothInterval_one] using hu
    · have hj2 : 2 ≤ j := by omega
      have h := component_profile_after 2 j D (by decide) hj2 hD
      have hπ : primeCount 2 = 1 := by decide
      omega
  have h := uniform_component_budget 2 n 2 D hlargest hprofile
  rw [primesUpTo_two, roughCount_two] at h
  omega

/-- Initial discrepancy for the two residues coprime to 6. -/
theorem roughCount_three_discrepancy (n : ℕ) :
    n ≤ 3 * roughCount {2, 3} n + 1 ∧ 3 * roughCount {2, 3} n ≤ n + 2 := by
  rw [roughCount_two_three_formula]
  omega

theorem roughCount_three_between_third_half (n : ℕ) (hn : 24 ≤ n) :
    roughCount {2, 3} (n / 3) + 1 ≤ roughCount {2, 3} (n / 2) := by
  have hlo := (roughCount_three_discrepancy (n / 2)).1
  have hhi := (roughCount_three_discrepancy (n / 3)).2
  omega

theorem card_roughNumbers_index_two (T : Finset ℕ) (n : ℕ) :
    ((roughNumbers T n).filter (fun b => n / b = 2)).card =
      roughCount T (n / 2) - roughCount T (n / 3) := by
  classical
  have hset : (roughNumbers T n).filter (fun b => n / b = 2) =
      roughNumbers T (n / 2) \ roughNumbers T (n / 3) := by
    rw [← roughNumbers_index_ge T n 2 (by decide), ← roughNumbers_index_ge T n 3 (by decide)]
    ext b
    by_cases hb : b ∈ roughNumbers T n
    · simp only [Finset.mem_filter, Finset.mem_sdiff, hb, true_and]
      omega
    · simp [hb]
  rw [hset, Finset.card_sdiff_of_subset (roughNumbers_mono T (show n / 3 ≤ n / 2 by omega))]
  rfl

private theorem sum_if_two (R : Finset ℕ) (n : ℕ) :
    (∑ b ∈ R, if n / b = 2 then 1 else 0) = (R.filter (fun b => n / b = 2)).card := by
  rw [← Finset.sum_filter]
  simp

/-- The extra index-two term supplements the three-term baseline for q=3. -/
theorem component_budget_three (n : ℕ) (D : Poly) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D 3)
    (hcut : 3 < 2 * (weight D - 1)) :
    3 * roughCount (primesUpTo 3) n +
      (roughCount (primesUpTo 3) (n / 2) - roughCount (primesUpTo 3) (n / 3)) ≤
        weight (interval n * D) := by
  classical
  have hu : 3 ≤ weight D := by omega
  calc
    _ = ∑ b ∈ roughNumbers (primesUpTo 3) n, (3 + if n / b = 2 then 1 else 0) := by
      rw [Finset.sum_add_distrib, sum_if_two, card_roughNumbers_index_two]
      simp [roughCount, Nat.mul_comm]
    _ ≤ ∑ b ∈ roughNumbers (primesUpTo 3) n,
        weight (smoothInterval (primesUpTo 3) (n / b) * D) := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨hbpos, hbn, _⟩ := (mem_roughNumbers (primesUpTo 3) n b).mp hb
      have hidx : 1 ≤ n / b := (Nat.le_div_iff_mul_le hbpos).mpr (by simpa using hbn)
      by_cases h1 : n / b = 1
      · simpa [h1, smoothInterval_one] using hu
      · by_cases h2 : n / b = 2
        · have h := component_profile_before 3 2 D (by decide) (by decide) hnorm hlargest
          have hπ : primeCount 2 = 1 := by decide
          simpa [h2, hπ] using h
        · have hidx3 : 3 ≤ n / b := by omega
          have h := component_profile_after 3 (n / b) D (by decide) hidx3 hD
          have hπ : primeCount 3 = 2 := by decide
          simpa [h2, hπ] using h
    _ = _ := (weight_interval_mul_eq_sum_rough_components _ n D
      (primesUpTo_prime 3) (largestPrime_vars_subset D 3 hlargest)).symm

theorem localized_q_three (n : ℕ) (D : Poly) (hn : 67 ≤ n) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D 3)
    (hcut : 3 < 2 * (weight D - 1)) : n ≤ weight (interval n * D) := by
  have hbudget := component_budget_three n D hD hnorm hlargest hcut
  rw [primesUpTo_three] at hbudget
  have hlo := (roughCount_three_discrepancy n).1
  have hbetween := roughCount_three_between_third_half n (by omega)
  omega

theorem localized_q_five (n : ℕ) (D : Poly) (hn : 56 ≤ n) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D 5)
    (hcut : 5 < 2 * (weight D - 1)) : n ≤ weight (interval n * D) := by
  have hu : 4 ≤ weight D := by omega
  have hbudget := component_budget_four_paper 5 n D (by decide) hD hnorm hlargest hu
  have hfour : 4 * roughCount (primesUpTo 5) n ≤ weight (interval n * D) :=
    (Nat.le_add_right _ _).trans hbudget
  rw [primesUpTo_five] at hfour
  have hdisc := (roughCount_five_discrepancy n).2
  omega

theorem localized_prime_le_five (n q : ℕ) (D : Poly) (hn : 67 ≤ n) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D q)
    (hcut : q < 2 * (weight D - 1)) (hq : q ≤ 5) : n ≤ weight (interval n * D) := by
  have hq2 := hlargest.1.two_le
  have hq4 : q ≠ 4 := by
    intro heq
    have hp := hlargest.1
    rw [heq] at hp
    exact (by decide : ¬Nat.Prime 4) hp
  have hcases : q = 2 ∨ q = 3 ∨ q = 5 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact localized_q_two n D hD hnorm hlargest hcut
  · exact localized_q_three n D hn hD hnorm hlargest hcut
  · exact localized_q_five n D (by omega) hD hnorm hlargest hcut

/-! The remaining three small primes use the same component profile and
the alpha-sieve bound, with the finite rows of the manuscript checked
directly as natural-number statements. -/

/-- The nonnegative form of the three small-prime budgets. -/
def smallQBudget (q a c d n : ℕ) : ℕ :=
  4 * roughCount (primesUpTo q) n + a * roughIntervalCount (primesUpTo q) n +
    c * roughCount (primesUpTo q) (n / 3) + d * roughCount (primesUpTo q) (n / 5)

private theorem sum_small_indicator (R : Finset ℕ) (p : ℕ → Prop) [DecidablePred p]
    (c : ℕ) : (∑ b ∈ R, if p b then c else 0) = c * (R.filter p).card := by
  rw [← Finset.sum_filter]
  simp [Nat.mul_comm]

theorem small_component_budget (q a c d n : ℕ) (D : Poly)
    (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q)
    (hc : c ≤ 2) (hcd : c + d ≤ 4) (hq : 4 + c + d ≤ 1 + primeCount q)
    (hu : 4 + a ≤ weight D) : smallQBudget q a c d n ≤ weight (interval n * D) := by
  classical
  have hsplit : roughIntervalCount (primesUpTo q) n + roughCount (primesUpTo q) (n / 2) =
      roughCount (primesUpTo q) n :=
    Nat.sub_add_cancel (roughCount_mono _ (Nat.div_le_self n 2))
  calc
    _ = (4 + a) * roughIntervalCount (primesUpTo q) n +
        4 * roughCount (primesUpTo q) (n / 2) +
        c * roughCount (primesUpTo q) (n / 3) + d * roughCount (primesUpTo q) (n / 5) := by
      unfold smallQBudget
      rw [← hsplit]
      ring
    _ = ∑ b ∈ roughNumbers (primesUpTo q) n,
        ((if n / b = 1 then 4 + a else 0) + (if 2 ≤ n / b then 4 else 0) +
          (if 3 ≤ n / b then c else 0) + (if 5 ≤ n / b then d else 0)) := by
      simp only [Finset.sum_add_distrib, sum_small_indicator]
      rw [card_roughNumbers_index_one, card_roughNumbers_index_ge _ _ 2 (by decide),
        card_roughNumbers_index_ge _ _ 3 (by decide), card_roughNumbers_index_ge _ _ 5 (by decide)]
    _ ≤ ∑ b ∈ roughNumbers (primesUpTo q) n,
        weight (smoothInterval (primesUpTo q) (n / b) * D) := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨hbpos, hbn, _⟩ := (mem_roughNumbers (primesUpTo q) n b).mp hb
      have hidx : 1 ≤ n / b := (Nat.le_div_iff_mul_le hbpos).mpr (by simpa using hbn)
      by_cases h1 : n / b = 1
      · simpa [h1, smoothInterval_one] using hu
      · have h2 : 2 ≤ n / b := by omega
        simp only [if_neg h1, if_pos h2, zero_add]
        by_cases hbefore : n / b < q
        · have h := component_profile_before q (n / b) D h2 hbefore hnorm hlargest
          by_cases h5 : 5 ≤ n / b
          · have h3 : 3 ≤ n / b := by omega
            have hπ := primeCount_mono h5
            have hπ5 : primeCount 5 = 3 := by decide
            simp only [if_pos h3, if_pos h5]
            omega
          · by_cases h3 : 3 ≤ n / b
            · have hπ := primeCount_mono h3
              have hπ3 : primeCount 3 = 2 := by decide
              simp only [if_pos h3, if_neg h5]
              omega
            · have hπ := primeCount_mono h2
              have hπ2 : primeCount 2 = 1 := by decide
              simp only [if_neg h3, if_neg h5]
              omega
        · have h := component_profile_after q (n / b) D hlargest.1
            (Nat.le_of_not_gt hbefore) hD
          by_cases h3 : 3 ≤ n / b <;> by_cases h5 : 5 ≤ n / b <;>
            simp [h3, h5] <;> omega
    _ = _ := (weight_interval_mul_eq_sum_rough_components _ n D
      (primesUpTo_prime q) (largestPrime_vars_subset D q hlargest)).symm

theorem component_budget_seven (n : ℕ) (D : Poly) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D 7)
    (hcut : 7 < 2 * (weight D - 1)) : smallQBudget 7 1 1 0 n ≤ weight (interval n * D) := by
  apply small_component_budget 7 1 1 0 n D hD hnorm hlargest (by decide) (by decide) (by decide)
  omega

theorem component_budget_eleven (n : ℕ) (D : Poly) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D 11)
    (hcut : 11 < 2 * (weight D - 1)) : smallQBudget 11 3 2 0 n ≤ weight (interval n * D) := by
  apply small_component_budget 11 3 2 0 n D hD hnorm hlargest (by decide) (by decide) (by decide)
  omega

theorem component_budget_thirteen (n : ℕ) (D : Poly) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D 13)
    (hcut : 13 < 2 * (weight D - 1)) : smallQBudget 13 4 2 1 n ≤ weight (interval n * D) := by
  apply small_component_budget 13 4 2 1 n D hD hnorm hlargest (by decide) (by decide) (by decide)
  omega

private theorem alpha_seven : sieveAlpha 7 = (8 / 35 : ℝ) := by
  have h : sieveExtraPrimes 7 = ({7} : Finset ℕ) := by decide
  norm_num [sieveAlpha, h]

private theorem alpha_eleven : sieveAlpha 11 = (236 / 1155 : ℝ) := by
  have h : sieveExtraPrimes 11 = ({7, 11} : Finset ℕ) := by decide
  norm_num [sieveAlpha, h]

private theorem alpha_thirteen : sieveAlpha 13 = (184 / 1001 : ℝ) := by
  have h : sieveExtraPrimes 13 = ({7, 11, 13} : Finset ℕ) := by decide
  norm_num [sieveAlpha, h]

theorem roughRealCount_nat_div (T : Finset ℕ) (n k : ℕ) :
    roughRealCount T ((n : ℝ) / k) = (roughCount T (n / k) : ℝ) := by
  simp only [roughRealCount, Nat.floor_div_natCast, Nat.floor_natCast]

/-- The paper uses the weaker twice-ordinary error in the interval estimate. -/
theorem smallQBudget_alpha_lower (q a c d n : ℕ) (hq : 5 ≤ q) :
    (4 + (a : ℝ) / 2 + (c : ℝ) / 3 + (d : ℝ) / 5) * sieveAlpha q * n -
      (4 + 2 * (a : ℝ) + c + d) * ((14 / 15) * (sieveNu q : ℝ)) ≤
      (smallQBudget q a c d n : ℝ) := by
  have h0 := roughRealCount_primesUpTo_alpha_lower hq (n : ℝ) (Nat.cast_nonneg n)
  have hI := roughRealIntervalCount_primesUpTo_alpha_lower hq (n : ℝ) (Nat.cast_nonneg n)
  have h3 := roughRealCount_primesUpTo_alpha_lower hq ((n : ℝ) / 3) (by positivity)
  have h5 := roughRealCount_primesUpTo_alpha_lower hq ((n : ℝ) / 5) (by positivity)
  simp only [roughRealCount_natCast, roughRealIntervalCount_natCast] at h0 hI
  simp only [roughRealCount, Nat.floor_div_ofNat, Nat.floor_natCast] at h3 h5
  have hν : (0 : ℝ) ≤ sieveNu q := Nat.cast_nonneg _
  have hIweak : sieveAlpha q * n / 2 - 2 * ((14 / 15) * (sieveNu q : ℝ)) ≤
      (roughIntervalCount (primesUpTo q) n : ℝ) := by linarith
  have hfour := mul_le_mul_of_nonneg_left h0 (show (0 : ℝ) ≤ 4 by norm_num)
  have ha := mul_le_mul_of_nonneg_left hIweak (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  have hc := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
  have hd := mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hsum := add_le_add (add_le_add (add_le_add hfour ha) hc) hd
  calc
    _ = 4 * (sieveAlpha q * n - (14 / 15) * (sieveNu q : ℝ)) +
        a * (sieveAlpha q * n / 2 - 2 * ((14 / 15) * (sieveNu q : ℝ))) +
        c * (sieveAlpha q * ((n : ℝ) / 3) - (14 / 15) * (sieveNu q : ℝ)) +
        d * (sieveAlpha q * ((n : ℝ) / 5) - (14 / 15) * (sieveNu q : ℝ)) := by ring
    _ ≤ _ := hsum
    _ = _ := by simp only [smallQBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

theorem smallQBudget_seven_linear (n : ℕ) :
    ((116 : ℝ) * n - 1372) / 105 ≤ (smallQBudget 7 1 1 0 n : ℝ) := by
  have h := smallQBudget_alpha_lower 7 1 1 0 n (by decide)
  have hν : sieveNu 7 = 2 := by decide
  rw [alpha_seven, hν] at h
  norm_num at h ⊢
  linarith

theorem smallQBudget_eleven_linear (n : ℕ) :
    ((4366 : ℝ) * n - 116424) / 3465 ≤ (smallQBudget 11 3 2 0 n : ℝ) := by
  have h := smallQBudget_alpha_lower 11 3 2 0 n (by decide)
  have hν : sieveNu 11 = 3 := by decide
  rw [alpha_eleven, hν] at h
  norm_num at h ⊢
  linarith

theorem smallQBudget_thirteen_linear (n : ℕ) :
    ((18952 : ℝ) * n - 840840) / 15015 ≤ (smallQBudget 13 4 2 1 n : ℝ) := by
  have h := smallQBudget_alpha_lower 13 4 2 1 n (by decide)
  have hν : sieveNu 13 = 4 := by decide
  rw [alpha_thirteen, hν] at h
  norm_num at h ⊢
  linarith

/-- A table row is sufficient throughout its interval, using monotonicity
on all positive arguments and the upper endpoint on the negative one. -/
theorem smallQBudget_row (q a c d L H n : ℕ) (hL : L ≤ n) (hH : n ≤ H)
    (hrow : H + a * roughCount (primesUpTo q) (H / 2) ≤
      (4 + a) * roughCount (primesUpTo q) L +
        c * roughCount (primesUpTo q) (L / 3) + d * roughCount (primesUpTo q) (L / 5)) :
    n ≤ smallQBudget q a c d n := by
  have h0 := Nat.mul_le_mul_left (4 + a) (roughCount_mono (primesUpTo q) hL)
  have h2 := Nat.mul_le_mul_left a (roughCount_mono (primesUpTo q)
    (Nat.div_le_div_right hH : n / 2 ≤ H / 2))
  have h3 := Nat.mul_le_mul_left c (roughCount_mono (primesUpTo q)
    (Nat.div_le_div_right hL : L / 3 ≤ n / 3))
  have h5 := Nat.mul_le_mul_left d (roughCount_mono (primesUpTo q)
    (Nat.div_le_div_right hL : L / 5 ≤ n / 5))
  have hsplit : roughIntervalCount (primesUpTo q) n + roughCount (primesUpTo q) (n / 2) =
      roughCount (primesUpTo q) n :=
    Nat.sub_add_cancel (roughCount_mono _ (Nat.div_le_self n 2))
  have heq : smallQBudget q a c d n + a * roughCount (primesUpTo q) (n / 2) =
      (4 + a) * roughCount (primesUpTo q) n +
        c * roughCount (primesUpTo q) (n / 3) + d * roughCount (primesUpTo q) (n / 5) := by
    unfold smallQBudget
    rw [← hsplit]
    ring
  omega

/-- The six relevant rows of the paper's table for q=7. -/
theorem smallQBudget_seven_finite (n : ℕ) (hn : 67 ≤ n) (hmax : n ≤ 115) :
    n ≤ smallQBudget 7 1 1 0 n := by
  by_cases h76 : n ≤ 76
  · exact smallQBudget_row 7 1 1 0 67 76 n hn h76 (by decide)
  by_cases h85 : n ≤ 85
  · exact smallQBudget_row 7 1 1 0 77 85 n (by omega) h85 (by decide)
  by_cases h94 : n ≤ 94
  · exact smallQBudget_row 7 1 1 0 86 94 n (by omega) h94 (by decide)
  by_cases h101 : n ≤ 101
  · exact smallQBudget_row 7 1 1 0 95 101 n (by omega) h101 (by decide)
  by_cases h110 : n ≤ 110
  · exact smallQBudget_row 7 1 1 0 102 110 n (by omega) h110 (by decide)
  · exact smallQBudget_row 7 1 1 0 111 115 n (by omega) hmax (by decide)

/-- The six relevant rows of the paper's table for q=11. -/
theorem smallQBudget_eleven_finite (n : ℕ) (hn : 67 ≤ n) (hmax : n ≤ 125) :
    n ≤ smallQBudget 11 3 2 0 n := by
  by_cases h76 : n ≤ 76
  · exact smallQBudget_row 11 3 2 0 67 76 n hn h76 (by decide)
  by_cases h85 : n ≤ 85
  · exact smallQBudget_row 11 3 2 0 77 85 n (by omega) h85 (by decide)
  by_cases h94 : n ≤ 94
  · exact smallQBudget_row 11 3 2 0 86 94 n (by omega) h94 (by decide)
  by_cases h101 : n ≤ 101
  · exact smallQBudget_row 11 3 2 0 95 101 n (by omega) h101 (by decide)
  by_cases h110 : n ≤ 110
  · exact smallQBudget_row 11 3 2 0 102 110 n (by omega) h110 (by decide)
  · exact smallQBudget_row 11 3 2 0 111 125 n (by omega) hmax (by decide)

/-- All eight rows of the paper's table for q=13. -/
theorem smallQBudget_thirteen_finite (n : ℕ) (hn : 67 ≤ n) (hmax : n ≤ 209) :
    n ≤ smallQBudget 13 4 2 1 n := by
  by_cases h76 : n ≤ 76
  · exact smallQBudget_row 13 4 2 1 67 76 n hn h76 (by decide)
  by_cases h85 : n ≤ 85
  · exact smallQBudget_row 13 4 2 1 77 85 n (by omega) h85 (by decide)
  by_cases h94 : n ≤ 94
  · exact smallQBudget_row 13 4 2 1 86 94 n (by omega) h94 (by decide)
  by_cases h101 : n ≤ 101
  · exact smallQBudget_row 13 4 2 1 95 101 n (by omega) h101 (by decide)
  by_cases h110 : n ≤ 110
  · exact smallQBudget_row 13 4 2 1 102 110 n (by omega) h110 (by decide)
  by_cases h145 : n ≤ 145
  · exact smallQBudget_row 13 4 2 1 111 145 n (by omega) h145 (by decide)
  by_cases h181 : n ≤ 181
  · exact smallQBudget_row 13 4 2 1 146 181 n (by omega) h181 (by decide)
  · exact smallQBudget_row 13 4 2 1 182 209 n (by omega) hmax (by decide)

theorem smallQBudget_seven_ge (n : ℕ) (hn : 67 ≤ n) : n ≤ smallQBudget 7 1 1 0 n := by
  by_cases hmax : n ≤ 115
  · exact smallQBudget_seven_finite n hn hmax
  · have hn116 : (116 : ℝ) ≤ n := by exact_mod_cast (show 116 ≤ n by omega)
    have hlin := smallQBudget_seven_linear n
    by_contra hnot
    have hlt : ((smallQBudget 7 1 1 0 n : ℕ) : ℝ) + 1 ≤ n := by
      exact_mod_cast (show smallQBudget 7 1 1 0 n + 1 ≤ n by omega)
    linarith

theorem smallQBudget_eleven_ge (n : ℕ) (hn : 67 ≤ n) : n ≤ smallQBudget 11 3 2 0 n := by
  by_cases hmax : n ≤ 125
  · exact smallQBudget_eleven_finite n hn hmax
  · have hn126 : (126 : ℝ) ≤ n := by exact_mod_cast (show 126 ≤ n by omega)
    have hlin := smallQBudget_eleven_linear n
    by_contra hnot
    have hlt : ((smallQBudget 11 3 2 0 n : ℕ) : ℝ) + 1 ≤ n := by
      exact_mod_cast (show smallQBudget 11 3 2 0 n + 1 ≤ n by omega)
    linarith

theorem smallQBudget_thirteen_ge (n : ℕ) (hn : 67 ≤ n) : n ≤ smallQBudget 13 4 2 1 n := by
  by_cases hmax : n ≤ 209
  · exact smallQBudget_thirteen_finite n hn hmax
  · have hn210 : (210 : ℝ) ≤ n := by exact_mod_cast (show 210 ≤ n by omega)
    have hlin := smallQBudget_thirteen_linear n
    by_contra hnot
    have hlt : ((smallQBudget 13 4 2 1 n : ℕ) : ℝ) + 1 ≤ n := by
      exact_mod_cast (show smallQBudget 13 4 2 1 n + 1 ≤ n by omega)
    linarith

theorem localized_q_seven (n : ℕ) (D : Poly) (hn : 67 ≤ n) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D 7)
    (hcut : 7 < 2 * (weight D - 1)) : n ≤ weight (interval n * D) :=
  (smallQBudget_seven_ge n hn).trans (component_budget_seven n D hD hnorm hlargest hcut)

theorem localized_q_eleven (n : ℕ) (D : Poly) (hn : 67 ≤ n) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D 11)
    (hcut : 11 < 2 * (weight D - 1)) : n ≤ weight (interval n * D) :=
  (smallQBudget_eleven_ge n hn).trans (component_budget_eleven n D hD hnorm hlargest hcut)

theorem localized_q_thirteen (n : ℕ) (D : Poly) (hn : 67 ≤ n) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D 13)
    (hcut : 13 < 2 * (weight D - 1)) : n ≤ weight (interval n * D) :=
  (smallQBudget_thirteen_ge n hn).trans (component_budget_thirteen n D hD hnorm hlargest hcut)

theorem localized_prime_le_thirteen (n q : ℕ) (D : Poly) (hn : 67 ≤ n) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D q)
    (hcut : q < 2 * (weight D - 1)) (hq : q ≤ 13) : n ≤ weight (interval n * D) := by
  have hprimes : ∀ k : Fin 14, Nat.Prime k.val →
      k.val = 2 ∨ k.val = 3 ∨ k.val = 5 ∨ k.val = 7 ∨ k.val = 11 ∨ k.val = 13 := by decide
  have hcases := hprimes ⟨q, by omega⟩ hlargest.1
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact localized_q_two n D hD hnorm hlargest hcut
  · exact localized_q_three n D hn hD hnorm hlargest hcut
  · exact localized_q_five n D (by omega) hD hnorm hlargest hcut
  · exact localized_q_seven n D hn hD hnorm hlargest hcut
  · exact localized_q_eleven n D hn hD hnorm hlargest hcut
  · exact localized_q_thirteen n D hn hD hnorm hlargest hcut

end Pilz

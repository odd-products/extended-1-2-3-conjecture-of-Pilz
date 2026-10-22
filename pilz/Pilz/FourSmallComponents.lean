import Pilz.FewMultipliers
import Pilz.Parity
import Pilz.Sieve30

/-! The q = 2, 3, 5 component estimates in the exceptional four-term cases. -/

noncomputable section

namespace Pilz

open MvPolynomial
open scoped BigOperators

private theorem even_round_four {w : ℕ} (h : 3 ≤ w) (he : Even w) : 4 ≤ w := by
  obtain ⟨k, hk⟩ := he
  omega

/-- Every product with a four-term multiplier has even support cardinality. -/
theorem four_term_product_even (P D : Poly) (hw : weight D = 4) :
    Even (weight (P * D)) := by
  have he : Even (weight D) := by rw [hw]; decide
  simpa only [mul_comm P D] using even_weight_mul he P

private theorem sum_index_one_const (R : Finset ℕ) (n c : ℕ) :
    (∑ b ∈ R, if n / b = 1 then c else 0) =
      c * (R.filter (fun b => n / b = 1)).card := by
  rw [← Finset.sum_filter]
  simp [Nat.mul_comm]

/-- For one support prime the index-one copies contribute two extra terms. -/
theorem four_term_one_prime_budget (n p : ℕ) (D : Poly) (hp : Nat.Prime p)
    (hD : D ≠ 0) (hw : weight D = 4) (hvars : D.vars ⊆ {p}) :
    2 * roughCount {p} n + 2 * roughIntervalCount {p} n ≤
      weight (interval n * D) := by
  classical
  have hprime : ∀ r ∈ ({p} : Finset ℕ), Nat.Prime r := by
    intro r hr
    have heq := Finset.mem_singleton.mp hr
    subst r
    exact hp
  calc
    _ = ∑ b ∈ roughNumbers {p} n, (2 + if n / b = 1 then 2 else 0) := by
      rw [Finset.sum_add_distrib, sum_index_one_const, card_roughNumbers_index_one]
      simp [roughCount, Nat.mul_comm]
    _ ≤ ∑ b ∈ roughNumbers {p} n, weight (smoothInterval {p} (n / b) * D) := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨hbpos, hbn, _⟩ := (mem_roughNumbers {p} n b).mp hb
      have hj : 1 ≤ n / b := (Nat.le_div_iff_mul_le hbpos).mpr (by simpa using hbn)
      by_cases h1 : n / b = 1
      · simp [h1, hw]
      · rw [if_neg h1, Nat.add_zero]
        by_cases hjp : n / b < p
        · rw [smoothInterval_eq_one_below {p} (n / b) hj (by
            intro r hr
            simpa only [Finset.mem_singleton.mp hr] using hjp), one_mul, hw]
          decide
        · have h := smooth_component_endpoints {p} {p} (n / b) D hj hD
            (fun _ hr => hr) hprime (by
              intro r hr
              have heq := Finset.mem_singleton.mp hr
              subst r
              exact Nat.le_of_not_gt hjp)
          simpa only [Finset.card_singleton] using h
    _ = _ := (weight_interval_mul_eq_sum_rough_components {p} n D hprime hvars).symm

private theorem primesUpTo_two : primesUpTo 2 = {2} := by decide
private theorem primesUpTo_three : primesUpTo 3 = {2, 3} := by decide
private theorem primesUpTo_five : primesUpTo 5 = {2, 3, 5} := by decide

theorem four_term_largest_two_budget (n : ℕ) (D : Poly) (hD : D ≠ 0)
    (hw : weight D = 4) (hlargest : LargestPrime D 2) :
    2 * roughCount {2} n + 2 * roughIntervalCount {2} n ≤
      weight (interval n * D) := by
  have hvars := largestPrime_vars_subset D 2 hlargest
  rw [primesUpTo_two] at hvars
  exact four_term_one_prime_budget n 2 D (by decide) hD hw hvars

/-- The three-endpoint estimate rounds to four because D has even weight. -/
theorem four_term_largest_three_profile (j : ℕ) (D : Poly) (hj : 1 ≤ j)
    (hD : D ≠ 0) (hw : weight D = 4) (hnorm : Normalized D)
    (hlargest : LargestPrime D 3) :
    4 ≤ weight (smoothInterval (primesUpTo 3) j * D) := by
  rw [primesUpTo_three]
  have h := two_prime_component_profile 2 3 j D (by decide) (by decide)
    (by decide) hD hnorm hlargest.2.1 (by omega) hj
  exact even_round_four h (four_term_product_even _ D hw)

theorem four_term_largest_three_budget (n : ℕ) (D : Poly) (hD : D ≠ 0)
    (hw : weight D = 4) (hnorm : Normalized D) (hlargest : LargestPrime D 3) :
    4 * roughCount (primesUpTo 3) n ≤ weight (interval n * D) :=
  uniform_component_budget_set _ n 4 D (primesUpTo_prime 3)
    (largestPrime_vars_subset D 3 hlargest)
    (fun j hj => four_term_largest_three_profile j D hj hD hw hnorm hlargest)

theorem four_term_largest_five_budget (n : ℕ) (D : Poly) (hD : D ≠ 0)
    (hw : weight D = 4) (hnorm : Normalized D) (hlargest : LargestPrime D 5) :
    4 * roughCount (primesUpTo 5) n ≤ weight (interval n * D) := by
  have h := component_budget_four_paper 5 n D (by decide) hD hnorm hlargest (by omega)
  simpa only [hw, Nat.sub_self, Nat.zero_mul, Nat.add_zero] using h

private def fortyCost (j : ℕ) : ℕ := if 3 ≤ j ∧ j < 5 then 6 else 4

/-- The two index-three/four components at n=40 each pay six, rather than four. -/
theorem four_term_largest_five_at_forty (D : Poly) (hD : D ≠ 0)
    (hw : weight D = 4) (hnorm : Normalized D) (hlargest : LargestPrime D 5) :
    44 ≤ weight (interval 40 * D) := by
  classical
  have hcost : (∑ b ∈ roughNumbers (primesUpTo 5) 40, fortyCost (40 / b)) = 44 := by
    decide
  calc
    _ = ∑ b ∈ roughNumbers (primesUpTo 5) 40, fortyCost (40 / b) := hcost.symm
    _ ≤ ∑ b ∈ roughNumbers (primesUpTo 5) 40,
        weight (smoothInterval (primesUpTo 5) (40 / b) * D) := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨hbpos, hbn, _⟩ := (mem_roughNumbers (primesUpTo 5) 40 b).mp hb
      have hj : 1 ≤ 40 / b := (Nat.le_div_iff_mul_le hbpos).mpr (by simpa using hbn)
      by_cases hband : 3 ≤ 40 / b ∧ 40 / b < 5
      · rw [fortyCost, if_pos hband]
        have h := component_profile_before 5 (40 / b) D (by omega) hband.2 hnorm hlargest
        have hmono := primeCount_mono hband.1
        have hpi : primeCount 3 = 2 := by decide
        omega
      · rw [fortyCost, if_neg hband]
        by_cases h1 : 40 / b = 1
        · simp [h1, hw]
        · exact component_profile_four 5 (40 / b) D (by decide) (by omega) hD hnorm hlargest
    _ = _ := (weight_interval_mul_eq_sum_rough_components _ 40 D
      (primesUpTo_prime 5) (largestPrime_vars_subset D 5 hlargest)).symm

/-- The exceptional bounds for q=2 use the exact one-prime budget. -/
theorem four_term_largest_two_exceptions (D : Poly) (hD : D ≠ 0)
    (hw : weight D = 4) (hlargest : LargestPrime D 2) :
    44 ≤ weight (interval 40 * D) ∧ 36 ≤ weight (interval 27 * D) ∧
      ∀ n : ℕ, 49 ≤ n → 56 ≤ weight (interval n * D) := by
  have h40 := four_term_largest_two_budget 40 D hD hw hlargest
  have h27 := four_term_largest_two_budget 27 D hD hw hlargest
  have hc40 : 2 * roughCount {2} 40 + 2 * roughIntervalCount {2} 40 = 60 := by decide
  have hc27 : 2 * roughCount {2} 27 + 2 * roughIntervalCount {2} 27 = 42 := by decide
  rw [hc40] at h40
  rw [hc27] at h27
  refine ⟨(by omega), (by omega), ?_⟩
  intro n hn
  have hb := four_term_largest_two_budget n D hD hw hlargest
  have hmon := roughCount_mono ({2} : Finset ℕ) hn
  have hc49 : roughCount {2} 49 = 25 := by decide
  have hI : 3 ≤ roughIntervalCount {2} n := by
    rw [roughIntervalCount, roughCount_singleton 2 n (by decide),
      roughCount_singleton 2 (n / 2) (by decide)]
    omega
  rw [hc49] at hmon
  omega

theorem four_term_largest_three_exceptions (D : Poly) (hD : D ≠ 0)
    (hw : weight D = 4) (hnorm : Normalized D) (hlargest : LargestPrime D 3) :
    44 ≤ weight (interval 40 * D) ∧ 36 ≤ weight (interval 27 * D) ∧
      ∀ n : ℕ, 49 ≤ n → 56 ≤ weight (interval n * D) := by
  have h40 := four_term_largest_three_budget 40 D hD hw hnorm hlargest
  have h27 := four_term_largest_three_budget 27 D hD hw hnorm hlargest
  have hc40 : roughCount (primesUpTo 3) 40 = 13 := by decide
  have hc27 : roughCount (primesUpTo 3) 27 = 9 := by decide
  rw [hc40] at h40
  rw [hc27] at h27
  refine ⟨(by omega), (by omega), ?_⟩
  intro n hn
  have hb := four_term_largest_three_budget n D hD hw hnorm hlargest
  have hmon := roughCount_mono (primesUpTo 3) hn
  have hc49 : roughCount (primesUpTo 3) 49 = 17 := by decide
  rw [hc49] at hmon
  omega

theorem four_term_largest_five_ge_forty_nine (n : ℕ) (D : Poly) (hn : 49 ≤ n)
    (hD : D ≠ 0) (hw : weight D = 4) (hnorm : Normalized D)
    (hlargest : LargestPrime D 5) : 56 ≤ weight (interval n * D) := by
  have hb := four_term_largest_five_budget n D hD hw hnorm hlargest
  have hmon := roughCount_mono (primesUpTo 5) hn
  have hc49 : roughCount (primesUpTo 5) 49 = 14 := by decide
  rw [hc49] at hmon
  omega

end Pilz

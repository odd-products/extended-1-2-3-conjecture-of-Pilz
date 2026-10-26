import WeightedPilz.SmallCounterexample
import WeightedPilz.Arithmetic.MiddleRoughCounts

/-! Every multiplier with at most six terms satisfies the middle interval bound. -/
noncomputable section
namespace WeightedPilz
open scoped BigOperators
open Pilz (primesUpTo primeCount primeCount_mono smoothNumbers roughNumbers
  roughCount mem_roughNumbers)
variable {K : Type*} [Field K]

private def sevenCost (j : ℕ) : ℕ :=
  if j = 1 then 5 else if j = 2 then 4 else if j < 5 then 6 else if j < 7 then 8 else 5

private theorem sevenCost_balance (j : ℕ) (hj : 1 ≤ j) :
    sevenCost j + (if 2 ≤ j then 1 else 0) + (if 7 ≤ j then 3 else 0) =
      5 + (if 3 ≤ j then 2 else 0) + (if 5 ≤ j then 2 else 0) := by
  unfold sevenCost
  split_ifs <;> omega

private theorem sum_indicator_middle (R : Finset ℕ) (p : ℕ → Prop) [DecidablePred p]
    (a : ℕ) : (∑ b ∈ R, if p b then a else 0) = a * (R.filter p).card := by
  rw [← Finset.sum_filter]
  simp [Nat.mul_comm]

theorem component_budget_seven_middle (n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hD : D ≠ 0) (hnorm : Normalized D)
    (hlargest : LargestPrime D 7) (hu : 5 ≤ weight D) :
    5 * roughCount (primesUpTo 7) n + 2 * roughCount (primesUpTo 7) (n / 3) +
      2 * roughCount (primesUpTo 7) (n / 5) ≤
      weight (interval n c * D) + roughCount (primesUpTo 7) (n / 2) +
        3 * roughCount (primesUpTo 7) (n / 7) := by
  have hp : ∀ (j : ℕ) (f : ℕ → K), 1 ≤ j →
      (∀ a ∈ smoothNumbers (primesUpTo 7) j, f a ≠ 0) →
      sevenCost j ≤ weight (smoothInterval (primesUpTo 7) j f * D) := by
    intro j f hj hf
    by_cases h1 : j = 1
    · subst j
      rw [component_profile_one 7 f D (hf 1 (one_mem_smoothNumbers _ le_rfl))]
      simpa only [sevenCost, if_pos rfl] using hu
    · by_cases h7 : j < 7
      · have h2 : 2 ≤ j := by omega
        have h := component_profile_before 7 j f D hf h2 h7 hnorm hlargest
        have hπ2 : primeCount 2 = 1 := by decide
        have hπ3 : primeCount 3 = 2 := by decide
        have hπ4 : primeCount 4 = 2 := by decide
        have hπ5 : primeCount 5 = 3 := by decide
        have hπ6 : primeCount 6 = 3 := by decide
        interval_cases j <;> norm_num [sevenCost, hπ2, hπ3, hπ4, hπ5, hπ6] at h ⊢ <;> omega
      · have h := component_profile_after 7 j f D hf (by decide) (by omega) hD
        have hπ : primeCount 7 = 4 := by decide
        have h2 : j ≠ 2 := by omega
        have h5 : ¬j < 5 := by omega
        simpa only [sevenCost, if_neg h1, if_neg h2, if_neg h5, if_neg h7, hπ] using h
  have hbudget := component_budget_of_profile (primesUpTo 7) n c D sevenCost hc
    (Pilz.primesUpTo_prime 7) (largestPrime_vars_subset D 7 hlargest) hp
  have hsum : (∑ b ∈ roughNumbers (primesUpTo 7) n, sevenCost (n / b)) +
      roughCount (primesUpTo 7) (n / 2) + 3 * roughCount (primesUpTo 7) (n / 7) =
      5 * roughCount (primesUpTo 7) n + 2 * roughCount (primesUpTo 7) (n / 3) +
        2 * roughCount (primesUpTo 7) (n / 5) := by
    have heq : (∑ b ∈ roughNumbers (primesUpTo 7) n,
        (sevenCost (n / b) + (if 2 ≤ n / b then 1 else 0) + (if 7 ≤ n / b then 3 else 0))) =
        ∑ b ∈ roughNumbers (primesUpTo 7) n,
          (5 + (if 3 ≤ n / b then 2 else 0) + (if 5 ≤ n / b then 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro b hb
      obtain ⟨hbpos, hbn, _⟩ := (mem_roughNumbers (primesUpTo 7) n b).mp hb
      exact sevenCost_balance (n / b) ((Nat.le_div_iff_mul_le hbpos).mpr (by simpa using hbn))
    simpa only [Finset.sum_add_distrib, sum_indicator_middle,
      Pilz.card_roughNumbers_index_ge _ _ 2 (by decide),
      Pilz.card_roughNumbers_index_ge _ _ 7 (by decide),
      Pilz.card_roughNumbers_index_ge _ _ 3 (by decide),
      Pilz.card_roughNumbers_index_ge _ _ 5 (by decide),
      one_mul, Finset.sum_const, smul_eq_mul, Nat.mul_comm, roughCount] using heq
  omega

/-- This statement allows arbitrary additional variables in the multiplier. -/
theorem middle_six_term_bound (n : ℕ) (c : ℕ → K) (H : Poly K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (hH : H ≠ 0) (hweight : weight H ≤ 6) : n ≤ weight (interval n c * H) := by
  by_contra hnot
  have hshort : weight (interval n c * H) < n := by omega
  obtain ⟨D, q, hD, hDshort, hwD, _, hnorm, hmin, hlargest⟩ :=
    prime_counterexample_preparation n c H hc hH hshort
  have hcut := deletionMinimal_prime_bound n q c hc D hlargest.1
    (hnorm q) hlargest.2.1 hmin hDshort
  have hq : q < 10 := by omega
  have hprime := hlargest.1
  have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by
    interval_cases q <;> first | omega | norm_num at hprime
  obtain ⟨_, h3, h5, h7⟩ := Arithmetic.sixInput_rough_budgets hn hn'
  change n + roughCount (primesUpTo 3) (n / 3) ≤
    3 * roughCount (primesUpTo 3) n + roughCount (primesUpTo 3) (n / 2) at h3
  change n ≤ 4 * roughCount (primesUpTo 5) n at h5
  change n + roughCount (primesUpTo 7) (n / 2) + 3 * roughCount (primesUpTo 7) (n / 7) ≤
    5 * roughCount (primesUpTo 7) n + 2 * roughCount (primesUpTo 7) (n / 3) +
      2 * roughCount (primesUpTo 7) (n / 5) at h7
  rcases hcases with rfl | rfl | rfl | rfl
  · have h := localized_q_two n c D hc hD hlargest hcut
    omega
  · have h := component_budget_three n c D hc hD hnorm hlargest hcut
    have hmono : roughCount (primesUpTo 3) (n / 3) ≤ roughCount (primesUpTo 3) (n / 2) :=
      Pilz.roughCount_mono _ (Nat.div_le_div_left (by decide : 2 ≤ 3) (by decide))
    omega
  · have h := component_budget_four_paper 5 n c D hc (by decide) hD hnorm hlargest (by omega)
    omega
  · have h := component_budget_seven_middle n c D hc hD hnorm hlargest (by omega)
    omega

end WeightedPilz

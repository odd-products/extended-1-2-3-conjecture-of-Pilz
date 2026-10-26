import WeightedPilz.ComponentBounds
import WeightedPilz.Arithmetic.Imported

/-! Weighted localized estimates for the support primes through thirteen. -/

noncomputable section

namespace WeightedPilz

open scoped BigOperators
open Pilz (primesUpTo primeCount primeCount_mono smoothNumbers roughNumbers
  roughCount roughIntervalCount mem_roughNumbers smallQBudget)

variable {K : Type*} [Field K]

/-- Sum a profile which holds for every inherited nonzero weight function. -/
theorem component_budget_of_profile (T : Finset ℕ) (n : ℕ) (c : ℕ → K)
    (D : Poly K) (g : ℕ → ℕ) (hc : NonzeroWeights n c)
    (hT : ∀ p ∈ T, Nat.Prime p) (hD : D.vars ⊆ T)
    (hprofile : ∀ (j : ℕ) (f : ℕ → K), 1 ≤ j →
      (∀ a ∈ smoothNumbers T j, f a ≠ 0) → g j ≤ weight (smoothInterval T j f * D)) :
    (∑ b ∈ roughNumbers T n, g (n / b)) ≤ weight (interval n c * D) := by
  rw [weight_interval_mul_eq_sum_rough_components T n c D hT hD]
  apply Finset.sum_le_sum
  intro b hb
  obtain ⟨hbpos, hbn, _⟩ := (mem_roughNumbers T n b).mp hb
  have hidx : 1 ≤ n / b := (Nat.le_div_iff_mul_le hbpos).mpr (by simpa using hbn)
  exact hprofile (n / b) (fun a => c (b * a)) hidx (component_weights_nonzero T n b c hc hb)

theorem uniform_component_budget (q n t : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hlargest : LargestPrime D q)
    (hprofile : ∀ (j : ℕ) (f : ℕ → K), 1 ≤ j →
      (∀ a ∈ smoothNumbers (primesUpTo q) j, f a ≠ 0) →
      t ≤ weight (smoothInterval (primesUpTo q) j f * D)) :
    t * roughCount (primesUpTo q) n ≤ weight (interval n c * D) := by
  have h := component_budget_of_profile (primesUpTo q) n c D (fun _ => t) hc
    (Pilz.primesUpTo_prime q) (largestPrime_vars_subset D q hlargest) hprofile
  simpa [roughCount, Nat.mul_comm] using h

theorem localized_q_two (n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hD : D ≠ 0) (hlargest : LargestPrime D 2)
    (hcut : 2 < 2 * (weight D - 1)) : n ≤ weight (interval n c * D) := by
  have hu : 2 ≤ weight D := by omega
  have hprofile : ∀ (j : ℕ) (f : ℕ → K), 1 ≤ j →
      (∀ a ∈ smoothNumbers (primesUpTo 2) j, f a ≠ 0) →
      2 ≤ weight (smoothInterval (primesUpTo 2) j f * D) := by
    intro j f hj hf
    by_cases h1 : j = 1
    · subst j
      rw [component_profile_one 2 f D (hf 1 (one_mem_smoothNumbers _ le_rfl))]
      exact hu
    · have h := component_profile_after 2 j f D hf (by decide) (by omega) hD
      have hπ : primeCount 2 = 1 := by decide
      omega
  have h := uniform_component_budget 2 n 2 c D hc hlargest hprofile
  have htwo : primesUpTo 2 = ({2} : Finset ℕ) := by decide
  rw [htwo, Pilz.roughCount_two] at h
  omega

private theorem sum_indicator (R : Finset ℕ) (p : ℕ → Prop) [DecidablePred p]
    (t : ℕ) : (∑ b ∈ R, if p b then t else 0) = t * (R.filter p).card := by
  rw [← Finset.sum_filter]
  simp [Nat.mul_comm]

theorem component_budget_three (n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D 3)
    (hcut : 3 < 2 * (weight D - 1)) :
    3 * roughCount (primesUpTo 3) n +
      (roughCount (primesUpTo 3) (n / 2) - roughCount (primesUpTo 3) (n / 3)) ≤
        weight (interval n c * D) := by
  have hu : 3 ≤ weight D := by omega
  have hp : ∀ (j : ℕ) (f : ℕ → K), 1 ≤ j →
      (∀ a ∈ smoothNumbers (primesUpTo 3) j, f a ≠ 0) →
      (3 + if j = 2 then 1 else 0) ≤ weight (smoothInterval (primesUpTo 3) j f * D) := by
    intro j f hj hf
    by_cases h1 : j = 1
    · subst j
      rw [component_profile_one 3 f D (hf 1 (one_mem_smoothNumbers _ le_rfl))]
      simpa using hu
    · by_cases h2 : j = 2
      · subst j
        have h := component_profile_before 3 2 f D hf (by decide) (by decide) hnorm hlargest
        have hπ : primeCount 2 = 1 := by decide
        simpa [hπ] using h
      · have h := component_profile_after 3 j f D hf (by decide) (by omega) hD
        have hπ : primeCount 3 = 2 := by decide
        simpa [h2, hπ] using h
  have h := component_budget_of_profile (primesUpTo 3) n c D
    (fun j => 3 + if j = 2 then 1 else 0) hc
    (Pilz.primesUpTo_prime 3) (largestPrime_vars_subset D 3 hlargest) hp
  simpa only [Finset.sum_add_distrib, sum_indicator, one_mul,
    Pilz.card_roughNumbers_index_two, Finset.sum_const, smul_eq_mul, Nat.mul_comm,
    roughCount] using h

theorem localized_q_three (n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 67 ≤ n) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D 3)
    (hcut : 3 < 2 * (weight D - 1)) : n ≤ weight (interval n c * D) := by
  have hbudget := component_budget_three n c D hc hD hnorm hlargest hcut
  have hthree : primesUpTo 3 = ({2, 3} : Finset ℕ) := by decide
  rw [hthree] at hbudget
  have hlo := (Pilz.roughCount_three_discrepancy n).1
  have hbetween := Pilz.roughCount_three_between_third_half n (by omega)
  omega

theorem localized_q_five (n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 56 ≤ n) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D 5)
    (hcut : 5 < 2 * (weight D - 1)) : n ≤ weight (interval n c * D) := by
  have hu : 4 ≤ weight D := by omega
  have hbudget := component_budget_four_paper 5 n c D hc (by decide) hD hnorm hlargest hu
  have hfour : 4 * roughCount (primesUpTo 5) n ≤ weight (interval n c * D) :=
    (Nat.le_add_right _ _).trans hbudget
  have hfive : primesUpTo 5 = ({2, 3, 5} : Finset ℕ) := by decide
  rw [hfive] at hfour
  have hdisc := (Pilz.roughCount_five_discrepancy n).2
  omega

theorem small_component_budget (q a t d n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hD : D ≠ 0) (hnorm : Normalized D)
    (hlargest : LargestPrime D q) (ht : t ≤ 2) (htd : t + d ≤ 4)
    (hq : 4 + t + d ≤ 1 + primeCount q) (hu : 4 + a ≤ weight D) :
    smallQBudget q a t d n ≤ weight (interval n c * D) := by
  classical
  let g := fun j => (if j = 1 then 4 + a else 0) + (if 2 ≤ j then 4 else 0) +
    (if 3 ≤ j then t else 0) + (if 5 ≤ j then d else 0)
  have hp : ∀ (j : ℕ) (f : ℕ → K), 1 ≤ j →
      (∀ a ∈ smoothNumbers (primesUpTo q) j, f a ≠ 0) →
      g j ≤ weight (smoothInterval (primesUpTo q) j f * D) := by
    intro j f hj hf
    by_cases h1 : j = 1
    · subst j
      rw [component_profile_one q f D (hf 1 (one_mem_smoothNumbers _ le_rfl))]
      simpa [g] using hu
    · have h2 : 2 ≤ j := by omega
      simp only [g, if_neg h1, if_pos h2, zero_add]
      by_cases hbefore : j < q
      · have h := component_profile_before q j f D hf h2 hbefore hnorm hlargest
        by_cases h5 : 5 ≤ j
        · have h3 : 3 ≤ j := by omega
          have hπ := primeCount_mono h5
          have hπ5 : primeCount 5 = 3 := by decide
          simp only [if_pos h3, if_pos h5]
          omega
        · by_cases h3 : 3 ≤ j
          · have hπ := primeCount_mono h3
            have hπ3 : primeCount 3 = 2 := by decide
            simp only [if_pos h3, if_neg h5]
            omega
          · have hπ := primeCount_mono h2
            have hπ2 : primeCount 2 = 1 := by decide
            simp only [if_neg h3, if_neg h5]
            omega
      · have h := component_profile_after q j f D hf hlargest.1 (Nat.le_of_not_gt hbefore) hD
        by_cases h3 : 3 ≤ j <;> by_cases h5 : 5 ≤ j <;> simp [h3, h5] <;> omega
  have h := component_budget_of_profile (primesUpTo q) n c D g hc
    (Pilz.primesUpTo_prime q) (largestPrime_vars_subset D q hlargest) hp
  simp only [g, Finset.sum_add_distrib, sum_indicator,
    Pilz.card_roughNumbers_index_one, Pilz.card_roughNumbers_index_ge _ _ 2 (by decide),
    Pilz.card_roughNumbers_index_ge _ _ 3 (by decide),
    Pilz.card_roughNumbers_index_ge _ _ 5 (by decide)] at h
  have hsplit : roughIntervalCount (primesUpTo q) n + roughCount (primesUpTo q) (n / 2) =
      roughCount (primesUpTo q) n :=
    Nat.sub_add_cancel (Pilz.roughCount_mono _ (Nat.div_le_self n 2))
  unfold smallQBudget
  nlinarith

/-- All six small support primes, including the finite and unbounded numerical tails. -/
theorem localized_small_support (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 67 ≤ n) (hq : q ≤ 13) (hD : D ≠ 0)
    (hnorm : Normalized D) (hlargest : LargestPrime D q)
    (hcut : q < 2 * (weight D - 1)) : n ≤ weight (interval n c * D) := by
  have hqp := hlargest.1
  have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 := by
    interval_cases q <;> first | omega | (norm_num at hqp)
  obtain ⟨h7, h11, h13⟩ := Arithmetic.small_prime_profiles n hn
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact localized_q_two n c D hc hD hlargest hcut
  · exact localized_q_three n c D hc hn hD hnorm hlargest hcut
  · exact localized_q_five n c D hc (by omega) hD hnorm hlargest hcut
  · exact h7.trans (small_component_budget 7 1 1 0 n c D hc hD hnorm hlargest
      (by decide) (by decide) (by decide) (by omega))
  · exact h11.trans (small_component_budget 11 3 2 0 n c D hc hD hnorm hlargest
      (by decide) (by decide) (by decide) (by omega))
  · exact h13.trans (small_component_budget 13 4 2 1 n c D hc hD hnorm hlargest
      (by decide) (by decide) (by decide) (by omega))

end WeightedPilz

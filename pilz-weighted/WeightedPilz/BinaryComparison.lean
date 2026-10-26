import WeightedPilz.MiddleSix

/-! Signed rough-component profiles and quantitative cuts for the binary middle proof. -/
noncomputable section
namespace WeightedPilz
open scoped BigOperators
open Pilz (primesUpTo primeCount smoothNumbers roughNumbers roughCount mem_roughNumbers)
variable {K : Type*} [Field K]

def comparisonCost (q u j : ℕ) : ℤ :=
  if q = 2 then u + (if 2 ≤ j then 2 - (u : ℤ) else 0)
  else if q = 3 then u + (if 2 ≤ j then 4 - (u : ℤ) else 0) - (if 3 ≤ j then 1 else 0)
  else if q = 5 then u + (if 2 ≤ j then 4 - (u : ℤ) else 0) +
    (if 3 ≤ j then 2 else 0) - (if 5 ≤ j then 2 else 0)
  else u + (if 2 ≤ j then 4 - (u : ℤ) else 0) +
    (if 3 ≤ j then 2 else 0) + (if 5 ≤ j then 2 else 0) - (if 7 ≤ j then 3 else 0)

private def activeCost (q u j : ℕ) : ℤ :=
  if j = 1 then u else if j < q then 2 * (1 + (primeCount j : ℤ)) else 1 + (primeCount q : ℤ)

theorem comparisonCost_eq_active (q u j : ℕ) (hq : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7)
    (hj : 1 ≤ j) : comparisonCost q u j = activeCost q u j := by
  have hp2 : primeCount 2 = 1 := by decide
  have hp3 : primeCount 3 = 2 := by decide
  have hp4 : primeCount 4 = 2 := by decide
  have hp5 : primeCount 5 = 3 := by decide
  have hp6 : primeCount 6 = 3 := by decide
  have hp7 : primeCount 7 = 4 := by decide
  by_cases hsmall : j < 7
  · interval_cases j <;> rcases hq with rfl | rfl | rfl | rfl <;>
      norm_num [comparisonCost, activeCost, hp2, hp3, hp4, hp5, hp6, hp7] <;> ring
  · have h1 : j ≠ 1 := by omega
    have h2 : 2 ≤ j := by omega
    have h3 : 3 ≤ j := by omega
    have h5 : 5 ≤ j := by omega
    have h7 : 7 ≤ j := by omega
    have hn2 : ¬j < 2 := by omega
    have hn3 : ¬j < 3 := by omega
    have hn5 : ¬j < 5 := by omega
    rcases hq with rfl | rfl | rfl | rfl <;>
      norm_num [comparisonCost, activeCost, h1, h2, h3, h5, h7, hn2, hn3, hn5,
        hsmall, hp2, hp3, hp5, hp7] <;> ring

theorem comparison_component_cost (q j : ℕ) (f : ℕ → K) (D : Poly K)
    (hq : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7) (hj : 1 ≤ j)
    (hf : ∀ a ∈ smoothNumbers (primesUpTo q) j, f a ≠ 0)
    (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    comparisonCost q (weight D) j ≤ (weight (smoothInterval (primesUpTo q) j f * D) : ℤ) := by
  rw [comparisonCost_eq_active q (weight D) j hq hj]
  by_cases h1 : j = 1
  · subst j
    rw [component_profile_one q f D (hf 1 (one_mem_smoothNumbers _ le_rfl))]
    simp [activeCost]
  · by_cases hbefore : j < q
    · have h := component_profile_before q j f D hf (by omega) hbefore hnorm hlargest
      simp only [activeCost, if_neg h1, if_pos hbefore]
      exact_mod_cast h
    · have h := component_profile_after q j f D hf hlargest.1 (by omega) hD
      simp only [activeCost, if_neg h1, if_neg hbefore]
      exact_mod_cast h

private theorem sum_indicator_int (R : Finset ℕ) (p : ℕ → Prop) [DecidablePred p]
    (a : ℤ) : (∑ b ∈ R, if p b then a else 0) = a * ((R.filter p).card : ℤ) := by
  rw [← Finset.sum_filter]
  simp [mul_comm]

theorem comparison_component_sum_lower (q n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hq : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7)
    (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    (∑ b ∈ roughNumbers (primesUpTo q) n, comparisonCost q (weight D) (n / b)) ≤
      (weight (interval n c * D) : ℤ) := by
  rw [weight_interval_mul_eq_sum_rough_components (primesUpTo q) n c D
    (Pilz.primesUpTo_prime q) (largestPrime_vars_subset D q hlargest), Nat.cast_sum]
  apply Finset.sum_le_sum
  intro b hb
  obtain ⟨hbpos, hbn, _⟩ := (mem_roughNumbers (primesUpTo q) n b).mp hb
  exact comparison_component_cost q (n / b) _ D hq
    ((Nat.le_div_iff_mul_le hbpos).mpr (by simpa using hbn))
    (component_weights_nonzero _ n b c hc hb) hD hnorm hlargest

theorem sum_comparisonCost_two (n u : ℕ) :
    (∑ b ∈ roughNumbers (primesUpTo 2) n, comparisonCost 2 u (n / b)) =
      Arithmetic.roughProfile2 n u := by
  simp only [comparisonCost, if_true, Finset.sum_add_distrib, sum_indicator_int,
    Pilz.card_roughNumbers_index_ge _ _ 2 (by decide), Finset.sum_const, nsmul_eq_mul]
  unfold Arithmetic.roughProfile2 Arithmetic.roughCount Pilz.primesUpTo Pilz.roughCount
  ring

theorem sum_comparisonCost_three (n u : ℕ) :
    (∑ b ∈ roughNumbers (primesUpTo 3) n, comparisonCost 3 u (n / b)) =
      Arithmetic.roughProfile3 n u := by
  simp only [comparisonCost, show (3 : ℕ) ≠ 2 by decide, if_false, if_true,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_indicator_int,
    Pilz.card_roughNumbers_index_ge _ _ 2 (by decide),
    Pilz.card_roughNumbers_index_ge _ _ 3 (by decide), Finset.sum_const, nsmul_eq_mul, one_mul]
  unfold Arithmetic.roughProfile3 Arithmetic.roughCount Pilz.primesUpTo Pilz.roughCount
  ring

theorem sum_comparisonCost_five (n u : ℕ) :
    (∑ b ∈ roughNumbers (primesUpTo 5) n, comparisonCost 5 u (n / b)) =
      Arithmetic.roughProfile5 n u := by
  simp only [comparisonCost, show (5 : ℕ) ≠ 2 by decide, show (5 : ℕ) ≠ 3 by decide,
    if_false, if_true, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_indicator_int,
    Pilz.card_roughNumbers_index_ge _ _ 2 (by decide),
    Pilz.card_roughNumbers_index_ge _ _ 3 (by decide),
    Pilz.card_roughNumbers_index_ge _ _ 5 (by decide), Finset.sum_const, nsmul_eq_mul]
  unfold Arithmetic.roughProfile5 Arithmetic.roughCount Pilz.primesUpTo Pilz.roughCount
  ring

theorem sum_comparisonCost_seven (n u : ℕ) :
    (∑ b ∈ roughNumbers (primesUpTo 7) n, comparisonCost 7 u (n / b)) =
      Arithmetic.roughProfile7 n u := by
  simp only [comparisonCost, show (7 : ℕ) ≠ 2 by decide, show (7 : ℕ) ≠ 3 by decide,
    show (7 : ℕ) ≠ 5 by decide, if_false,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_indicator_int,
    Pilz.card_roughNumbers_index_ge _ _ 2 (by decide),
    Pilz.card_roughNumbers_index_ge _ _ 3 (by decide),
    Pilz.card_roughNumbers_index_ge _ _ 5 (by decide),
    Pilz.card_roughNumbers_index_ge _ _ 7 (by decide), Finset.sum_const, nsmul_eq_mul]
  unfold Arithmetic.roughProfile7 Arithmetic.roughCount Pilz.primesUpTo Pilz.roughCount
  ring

theorem comparison_profile_two (n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D 2) :
    Arithmetic.roughProfile2 n (weight D) ≤ (weight (interval n c * D) : ℤ) := by
  rw [← sum_comparisonCost_two]
  exact comparison_component_sum_lower 2 n c D hc (by omega) hD hnorm hlargest

theorem comparison_profile_three (n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D 3) :
    Arithmetic.roughProfile3 n (weight D) ≤ (weight (interval n c * D) : ℤ) := by
  rw [← sum_comparisonCost_three]
  exact comparison_component_sum_lower 3 n c D hc (by omega) hD hnorm hlargest

theorem comparison_profile_five (n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D 5) :
    Arithmetic.roughProfile5 n (weight D) ≤ (weight (interval n c * D) : ℤ) := by
  rw [← sum_comparisonCost_five]
  exact comparison_component_sum_lower 5 n c D hc (by omega) hD hnorm hlargest

theorem comparison_profile_seven (n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D 7) :
    Arithmetic.roughProfile7 n (weight D) ≤ (weight (interval n c * D) : ℤ) := by
  rw [← sum_comparisonCost_seven]
  exact comparison_component_sum_lower 7 n c D hc (by omega) hD hnorm hlargest

theorem deletionMinimal_of_weight_le_seven (n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66) (hu : weight D ≤ 7) :
    DeletionMinimal n c D := by
  intro T hT hTnonempty hproper
  have hsupp := support_restrictTerms_of_subset D T hT
  have hR : restrictTerms D T ≠ 0 := by
    apply MvPolynomial.support_nonempty.mp
    rwa [hsupp]
  have hcard : weight (restrictTerms D T) < weight D := by
    change (restrictTerms D T).support.card < D.support.card
    rw [hsupp]
    exact Finset.card_lt_card ⟨hT, fun hDT => hproper (Finset.Subset.antisymm hT hDT)⟩
  exact middle_six_term_bound n c _ hc hn hn' hR (by omega)

theorem comparison_quantitative_cut (n q q₀ : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (hq₀ : 0 < q₀) (hq : q₀ ≤ q) (hnorm : Normalized D) (hlargest : LargestPrime D q)
    (hu : weight D ≤ 7) :
    Arithmetic.quantitativeCut n (weight D) q₀ ≤ (weight (interval n c * D) : ℤ) := by
  have h := deletionMinimal_product_lower_bound n q c hc D hlargest.1 (hnorm q)
    hlargest.2.1 (deletionMinimal_of_weight_le_seven n c D hc hn hn' hu)
  have hdiv : n / q ≤ n / q₀ := Nat.div_le_div_left hq hq₀
  have hmult := Nat.mul_le_mul_left (2 * (weight D - 1)) hdiv
  have hweight : 1 ≤ weight D := by
    obtain ⟨d, hd, _⟩ := hlargest.2.1
    exact Finset.card_pos.mpr ⟨d, hd⟩
  have hnat : 2 * n ≤ weight (interval n c * D) + 2 * (weight D - 1) * (n / q₀) := by omega
  have hint : (2 : ℤ) * n ≤ weight (interval n c * D) + 2 * ((weight D : ℤ) - 1) * (n / q₀ : ℕ) := by
    exact_mod_cast hnat
  unfold Arithmetic.quantitativeCut
  linarith

end WeightedPilz

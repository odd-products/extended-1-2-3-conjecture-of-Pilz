import WeightedPilz.BinaryComparison

/-! The sharpened five-prime row and the finite binary comparison table. -/
noncomputable section
namespace WeightedPilz
open scoped BigOperators
open Pilz (primesUpTo roughNumbers mem_roughNumbers)
variable {K : Type*} [Field K]

theorem comparison_profile_five_plus (n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hD : D ≠ 0) (hnorm : Normalized D)
    (hlargest : LargestPrime D 5)
    (hcore : 27 ≤ n ∧ n ≤ 48 → 6 ≤ distance (smoothInterval (primesUpTo 5) n c)) :
    Arithmetic.roughProfile5plus n (weight D) ≤ (weight (interval n c * D) : ℤ) := by
  by_cases hn : 27 ≤ n ∧ n ≤ 48
  · have hone : 1 ∈ roughNumbers (primesUpTo 5) n := by
      apply (mem_roughNumbers _ _ _).mpr
      refine ⟨le_rfl, by omega, ?_⟩
      intro p hp hdiv
      exact (Pilz.primesUpTo_prime 5 p hp).ne_one (Nat.eq_one_of_dvd_one hdiv)
    have hsum : (∑ b ∈ roughNumbers (primesUpTo 5) n,
        (comparisonCost 5 (weight D) (n / b) + (if b = 1 then 2 else 0))) ≤
        ∑ b ∈ roughNumbers (primesUpTo 5) n,
          (weight (smoothInterval (primesUpTo 5) (n / b) (fun a => c (b * a)) * D) : ℤ) := by
      apply Finset.sum_le_sum
      intro b hb
      by_cases hb1 : b = 1
      · subst b
        have hsix := (hcore hn).trans (distance_le_weight_mul _ D hD)
        have hcost : comparisonCost 5 (weight D) n = 4 := by
          have h2 : 2 ≤ n := by omega
          have h3 : 3 ≤ n := by omega
          have h5 : 5 ≤ n := by omega
          norm_num [comparisonCost, h2, h3, h5]
        simp only [Nat.div_one, if_pos rfl, one_mul, hcost]
        exact_mod_cast hsix
      · obtain ⟨hbpos, hbn, _⟩ := (mem_roughNumbers (primesUpTo 5) n b).mp hb
        simp only [if_neg hb1, add_zero]
        exact comparison_component_cost 5 (n / b) _ D (by omega)
          ((Nat.le_div_iff_mul_le hbpos).mpr (by simpa using hbn))
          (component_weights_nonzero _ n b c hc hb) hD hnorm hlargest
    rw [Finset.sum_add_distrib, sum_comparisonCost_five] at hsum
    have hindicator : (∑ b ∈ roughNumbers (primesUpTo 5) n,
        if b = 1 then (2 : ℤ) else 0) = 2 := by simp [hone]
    rw [hindicator] at hsum
    rw [Arithmetic.roughProfile5plus, if_pos hn,
      weight_interval_mul_eq_sum_rough_components (primesUpTo 5) n c D
        (Pilz.primesUpTo_prime 5) (largestPrime_vars_subset D 5 hlargest), Nat.cast_sum]
    exact hsum
  · simpa only [Arithmetic.roughProfile5plus, if_neg hn, add_zero] using
      comparison_profile_five n c D hc hD hnorm hlargest

/-- A comparison threshold combines the four active-prime profiles with the
quantitative cut. The exact number of terms of the multiplier is retained. -/
theorem comparison_profiles_bound (n q q₀ u L : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q)
    (hu : weight D = u) (hu7 : u ≤ 7) (hq₀ : 0 < q₀) (hq₀' : q₀ ≤ 11)
    (hcut : (L : ℤ) ≤ Arithmetic.quantitativeCut n u q₀)
    (h2 : 2 < q₀ → (L : ℤ) ≤ Arithmetic.roughProfile2 n u)
    (h3 : 3 < q₀ → (L : ℤ) ≤ Arithmetic.roughProfile3 n u)
    (h5 : 5 < q₀ → (L : ℤ) ≤ Arithmetic.roughProfile5plus n u)
    (h7 : 7 < q₀ → (L : ℤ) ≤ Arithmetic.roughProfile7 n u)
    (hcore : 27 ≤ n ∧ n ≤ 48 → 6 ≤ distance (smoothInterval (primesUpTo 5) n c)) :
    L ≤ weight (interval n c * D) := by
  by_cases hlarge : q₀ ≤ q
  · have h := comparison_quantitative_cut n q q₀ c D hc hn hn' hq₀ hlarge
      hnorm hlargest (by omega)
    rw [hu] at h
    exact_mod_cast hcut.trans h
  · have hq : q < 11 := by omega
    have hprime := hlargest.1
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by
      interval_cases q <;> first | omega | norm_num at hprime
    rcases hcases with rfl | rfl | rfl | rfl
    · have h := comparison_profile_two n c D hc hD hnorm hlargest
      rw [hu] at h
      exact_mod_cast (h2 (by omega)).trans h
    · have h := comparison_profile_three n c D hc hD hnorm hlargest
      rw [hu] at h
      exact_mod_cast (h3 (by omega)).trans h
    · have h := comparison_profile_five_plus n c D hc hD hnorm hlargest hcore
      rw [hu] at h
      exact_mod_cast (h5 (by omega)).trans h
    · have h := comparison_profile_seven n c D hc hD hnorm hlargest
      rw [hu] at h
      exact_mod_cast (h7 (by omega)).trans h

theorem comparison_row_bound (a b u q₀ cut h2 h3 h5 L n q : ℕ)
    (c : ℕ → K) (D : Poly K) (hc : NonzeroWeights n c)
    (hn : 25 ≤ n) (hn' : n ≤ 66) (hab : n ∈ Finset.Icc a b)
    (hrow : Arithmetic.ComparisonRow a b u q₀ cut h2 h3 h5)
    (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q)
    (hu : weight D = u) (hu7 : u ≤ 7) (hq₀ : 0 < q₀) (hq₀' : q₀ ≤ 11)
    (hLcut : L ≤ cut) (hL2 : L ≤ h2) (hL3 : L ≤ h3) (hL5 : L ≤ h5)
    (h7 : 7 < q₀ → (L : ℤ) ≤ Arithmetic.roughProfile7 n u)
    (hcore : 27 ≤ n ∧ n ≤ 48 → 6 ≤ distance (smoothInterval (primesUpTo 5) n c)) :
    L ≤ weight (interval n c * D) := by
  rcases hrow with ⟨hcut, hh2, hh3, hh5⟩
  have hcut' := Finset.min_le_of_eq (Finset.mem_image.mpr ⟨n, hab, rfl⟩) hcut
  have h2' := Finset.min_le_of_eq (Finset.mem_image.mpr ⟨n, hab, rfl⟩) hh2
  have h3' := Finset.min_le_of_eq (Finset.mem_image.mpr ⟨n, hab, rfl⟩) hh3
  have h5' := Finset.min_le_of_eq (Finset.mem_image.mpr ⟨n, hab, rfl⟩) hh5
  apply comparison_profiles_bound n q q₀ u L c D hc hn hn' hD hnorm hlargest
    hu hu7 hq₀ hq₀' ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) h7 hcore
  · exact le_trans (show (L : ℤ) ≤ cut by exact_mod_cast hLcut) hcut'
  · exact le_trans (show (L : ℤ) ≤ h2 by exact_mod_cast hL2) h2'
  · exact le_trans (show (L : ℤ) ≤ h3 by exact_mod_cast hL3) h3'
  · exact le_trans (show (L : ℤ) ≤ h5 by exact_mod_cast hL5) h5'

theorem binary_comparison_25 (q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights 25 c) (hD : D ≠ 0) (hnorm : Normalized D)
    (hlargest : LargestPrime D q) (hu : weight D = 3) :
    28 ≤ weight (interval 25 c * D) := by
  obtain ⟨hcut, h2, h3⟩ := Arithmetic.comparison_25
  apply comparison_profiles_bound 25 q 5 3 28 c D hc (by omega) (by omega)
    hD hnorm hlargest hu (by omega) (by omega) (by omega)
  · omega
  · intro _; omega
  · intro _; omega
  · omega
  · omega
  · omega

theorem binary_comparison_27_28 (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 27 ≤ n) (hn' : n ≤ 28)
    (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q) (hu : weight D = 4)
    (hcore : 6 ≤ distance (smoothInterval (primesUpTo 5) n c)) :
    32 ≤ weight (interval n c * D) := by
  exact comparison_row_bound 27 28 4 7 32 42 33 32 32 n q c D hc (by omega) (by omega)
    (Finset.mem_Icc.mpr ⟨hn, hn'⟩) Arithmetic.comparison_27_28 hD hnorm hlargest hu
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (fun _ => hcore)

theorem binary_comparison_34_35 (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 34 ≤ n) (hn' : n ≤ 35)
    (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q) (hu : weight D = 4)
    (hcore : 6 ≤ distance (smoothInterval (primesUpTo 5) n c)) :
    40 ≤ weight (interval n c * D) := by
  exact comparison_row_bound 34 35 4 7 40 50 40 40 40 n q c D hc (by omega) (by omega)
    (Finset.mem_Icc.mpr ⟨hn, hn'⟩) Arithmetic.comparison_34_35 hD hnorm hlargest hu
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (fun _ => hcore)

theorem binary_comparison_36 (q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights 36 c) (hD : D ≠ 0) (hnorm : Normalized D)
    (hlargest : LargestPrime D q) (hu : weight D = 4)
    (hcore : 6 ≤ distance (smoothInterval (primesUpTo 5) 36 c)) :
    40 ≤ weight (interval 36 c * D) := by
  exact comparison_row_bound 36 36 4 7 42 54 44 40 40 36 q c D hc (by omega) (by omega)
    (by simp) Arithmetic.comparison_36 hD hnorm hlargest hu
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (fun _ => hcore)

theorem binary_comparison_38 (q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights 38 c) (hD : D ≠ 0) (hnorm : Normalized D)
    (hlargest : LargestPrime D q) (hu : weight D = 4)
    (hcore : 6 ≤ distance (smoothInterval (primesUpTo 5) 38 c)) :
    44 ≤ weight (interval 38 c * D) := by
  exact comparison_row_bound 38 38 4 7 46 56 48 44 44 38 q c D hc (by omega) (by omega)
    (by simp) Arithmetic.comparison_38 hD hnorm hlargest hu
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (fun _ => hcore)

theorem binary_comparison_39_40 (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 39 ≤ n) (hn' : n ≤ 40)
    (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q) (hu : weight D = 4)
    (hcore : 6 ≤ distance (smoothInterval (primesUpTo 5) n c)) :
    46 ≤ weight (interval n c * D) := by
  exact comparison_row_bound 39 40 4 7 48 60 47 46 46 n q c D hc (by omega) (by omega)
    (Finset.mem_Icc.mpr ⟨hn, hn'⟩) Arithmetic.comparison_39_40 hD hnorm hlargest hu
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (fun _ => hcore)

theorem binary_comparison_49_51 (n q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 49 ≤ n) (hn' : n ≤ 51)
    (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q) (hu : weight D = 4) :
    56 ≤ weight (interval n c * D) := by
  exact comparison_row_bound 49 51 4 7 56 74 62 60 56 n q c D hc (by omega) (by omega)
    (Finset.mem_Icc.mpr ⟨hn, hn'⟩) Arithmetic.comparison_49_51 hD hnorm hlargest hu
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

theorem binary_comparison_58 (q : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights 58 c) (hD : D ≠ 0) (hnorm : Normalized D)
    (hlargest : LargestPrime D q) (hu : weight D = 5) :
    69 ≤ weight (interval 58 c * D) := by
  exact comparison_row_bound 58 58 5 11 76 100 78 73 69 58 q c D hc (by omega) (by omega)
    (by simp) Arithmetic.comparison_58 hD hnorm hlargest hu
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by intro _; norm_num [Arithmetic.comparison_58_seven]) (by omega)

end WeightedPilz

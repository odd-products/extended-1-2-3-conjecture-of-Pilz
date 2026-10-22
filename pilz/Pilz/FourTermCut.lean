import Pilz.FewMultipliers

/-! The four-term directed split used in the exceptional small intervals. -/

noncomputable section

namespace Pilz

open MvPolynomial

/-- Split a normalized four-term multiplier at zero versus positive
exponent in one occurring variable. Both pieces have at most three terms. -/
theorem exists_four_term_cut (D : Poly) (q : ℕ) (hweight : weight D = 4)
    (hzero : ∃ d ∈ D.support, d q = 0) (hpos : ∃ d ∈ D.support, 0 < d q) :
    ∃ L U : Poly, L + U = D ∧ L ≠ 0 ∧ U ≠ 0 ∧ weight L ≤ 3 ∧ weight U ≤ 3 ∧
      (∀ e ∈ L.support, e q = 0) ∧ (∀ e ∈ U.support, 1 ≤ e q) := by
  classical
  let S := D.support.filter (fun d => d q = 0)
  let T := D.support.filter (fun d => d q ≠ 0)
  let L := restrictTerms D S
  let U := restrictTerms D T
  have hSsub : S ⊆ D.support := Finset.filter_subset _ _
  have hTsub : T ⊆ D.support := Finset.filter_subset _ _
  have hSnonempty : S.Nonempty := by
    obtain ⟨d, hd, hdq⟩ := hzero
    exact ⟨d, Finset.mem_filter.mpr ⟨hd, hdq⟩⟩
  have hTnonempty : T.Nonempty := by
    obtain ⟨d, hd, hdq⟩ := hpos
    exact ⟨d, Finset.mem_filter.mpr ⟨hd, ne_of_gt hdq⟩⟩
  have hSproper : S ≠ D.support := by
    intro h
    obtain ⟨d, hd, hdq⟩ := hpos
    have hmem : d ∈ S := by rw [h]; exact hd
    have := (Finset.mem_filter.mp hmem).2
    omega
  have hTproper : T ≠ D.support := by
    intro h
    obtain ⟨d, hd, hdq⟩ := hzero
    have hmem : d ∈ T := by rw [h]; exact hd
    exact (Finset.mem_filter.mp hmem).2 hdq
  have hLsupp : L.support = S := support_restrictTerms_of_subset D S hSsub
  have hUsupp : U.support = T := support_restrictTerms_of_subset D T hTsub
  have hLne : L ≠ 0 := MvPolynomial.support_nonempty.mp (by rw [hLsupp]; exact hSnonempty)
  have hUne : U ≠ 0 := MvPolynomial.support_nonempty.mp (by rw [hUsupp]; exact hTnonempty)
  have hLcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hSsub, hSproper⟩)
  have hUcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTsub, hTproper⟩)
  have hLfew : weight L ≤ 3 := by
    unfold weight at hweight ⊢
    rw [hLsupp]
    omega
  have hUfew : weight U ≤ 3 := by
    unfold weight at hweight ⊢
    rw [hUsupp]
    omega
  have hsplit : L + U = D := by
    apply MvPolynomial.ext
    intro d
    change (if d ∈ S then coeff d D else 0) +
      (if d ∈ T then coeff d D else 0) = coeff d D
    by_cases hd : d ∈ D.support
    · by_cases hdq : d q = 0 <;> simp [S, T, hd, hdq]
    · have hz : coeff d D = 0 := MvPolynomial.notMem_support_iff.mp hd
      simp [S, T, hd, hz]
  refine ⟨L, U, hsplit, hLne, hUne, hLfew, hUfew, ?_, ?_⟩
  · intro e he
    rw [hLsupp] at he
    exact (Finset.mem_filter.mp he).2
  · intro e he
    rw [hUsupp] at he
    have := (Finset.mem_filter.mp he).2
    omega

private theorem four_term_cut_pair_cost (n q : ℕ) (D L U : Poly)
    (hsplit : L + U = D) (hLne : L ≠ 0) (hUne : U ≠ 0)
    (hLfew : weight L ≤ 3) (hUfew : weight U ≤ 3)
    (hU : ∀ e ∈ U.support, 1 ≤ e q) :
    2 * n ≤ weight (interval n * D) +
      2 * (((interval n).support ×ˢ L.support).filter
        (fun st => 1 ≤ st.1 q + st.2 q)).card := by
  have hLprod := three_multipliers n L hLne hLfew
  have hUprod := three_multipliers n U hUne hUfew
  have hcancel := weight_add_cancellation (interval n * L) (interval n * U)
  have hpair := support_cut_pair_bound (interval n) L U q 1 hU
  have hsum : interval n * L + interval n * U = interval n * D := by
    rw [← mul_add, hsplit]
  rw [hsum] at hcancel
  omega

/-- The paper's `2n-6 floor(n/q)` lower bound, without truncated subtraction. -/
theorem four_term_cut_prime (n q : ℕ) (D : Poly) (hq : Nat.Prime q)
    (hweight : weight D = 4) (hzero : ∃ d ∈ D.support, d q = 0)
    (hpos : ∃ d ∈ D.support, 0 < d q) :
    2 * n ≤ weight (interval n * D) + 6 * (n / q) := by
  classical
  obtain ⟨L, U, hsplit, hLne, hUne, hLfew, hUfew, hL, hU⟩ :=
    exists_four_term_cut D q hweight hzero hpos
  have hcut := four_term_cut_pair_cost n q D L U hsplit hLne hUne hLfew hUfew hU
  have hfilter : ((interval n).support ×ˢ L.support).filter
      (fun st => 1 ≤ st.1 q + st.2 q) =
      ((interval n).support.filter (fun d => 1 ≤ d q)) ×ˢ L.support := by
    ext st
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨hs, ht⟩, he⟩
      exact ⟨⟨hs, by simpa [hL st.2 ht] using he⟩, ht⟩
    · rintro ⟨⟨hs, he⟩, ht⟩
      exact ⟨⟨hs, ht⟩, by simpa [hL st.2 ht] using he⟩
  rw [hfilter, Finset.card_product, interval_exponent_count n q 1 hq, pow_one] at hcut
  have hcost : 2 * (n / q * weight L) ≤ 6 * (n / q) := by
    calc
      _ = (2 * (n / q)) * weight L := by ring
      _ ≤ (2 * (n / q)) * 3 := Nat.mul_le_mul_left _ hLfew
      _ = _ := by ring
  exact hcut.trans (Nat.add_le_add_left hcost _)

theorem four_term_cut_seven (n q : ℕ) (D : Poly) (hq : Nat.Prime q) (hq7 : 7 ≤ q)
    (hweight : weight D = 4) (hnorm : Normalized D) (hocc : VariableOccurs D q) :
    2 * n ≤ weight (interval n * D) + 6 * (n / 7) := by
  have h := four_term_cut_prime n q D hq hweight (hnorm q) hocc
  exact h.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left 6 (Nat.div_le_div_left hq7 (by decide))) _)

/-- A nonprime variable is absent from the arithmetic interval, so the two
pieces have disjoint product supports and the estimate strengthens to 2n. -/
theorem four_term_cut_nonprime (n q : ℕ) (D : Poly) (hq : ¬Nat.Prime q)
    (hweight : weight D = 4) (hnorm : Normalized D) (hocc : VariableOccurs D q) :
    2 * n ≤ weight (interval n * D) := by
  classical
  obtain ⟨L, U, hsplit, hLne, hUne, hLfew, hUfew, hL, hU⟩ :=
    exists_four_term_cut D q hweight (hnorm q) hocc
  have hP : ∀ d ∈ (interval n).support, d q = 0 := by
    intro d hd
    have hpos : ∀ a ∈ Finset.Icc 1 n, 0 < a :=
      fun a ha => (Finset.mem_Icc.mp ha).1
    rw [interval_eq_polynomialOf, support_polynomialOf _ hpos] at hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    exact Nat.factorization_eq_zero_of_non_prime a hq
  have hcut := four_term_cut_pair_cost n q D L U hsplit hLne hUne hLfew hUfew hU
  have hfilter : ((interval n).support ×ˢ L.support).filter
      (fun st => 1 ≤ st.1 q + st.2 q) = ∅ := by
    ext st
    simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
    rintro ⟨hst, hine⟩
    obtain ⟨hs, ht⟩ := Finset.mem_product.mp hst
    simp [hP st.1 hs, hL st.2 ht] at hine
  simpa only [hfilter, Finset.card_empty, Nat.mul_zero, Nat.add_zero] using hcut

end Pilz

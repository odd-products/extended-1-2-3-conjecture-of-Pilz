import WeightedPilz.MiddleSix

/-! Sharp finite comparison bounds lift from normalized prime-variable
cofactors to arbitrary polynomial cofactors of the same term count. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]
attribute [local instance] Classical.propDecidable

theorem outside_fiber_comparison_lifting (S : Set ℕ) (P H : Poly K)
    (hP : (P.vars : Set ℕ) ⊆ S) (hH : H ≠ 0) (u N L : ℕ)
    (hweight : weight H = u) (hL : L ≤ 2 * N)
    (hsmall : ∀ D : Poly K, D ≠ 0 → weight D ≤ u → N ≤ weight (P * D))
    (hbase : ∀ D : Poly K, D ≠ 0 → (D.vars : Set ℕ) ⊆ S →
      weight D = u → L ≤ weight (P * D)) : L ≤ weight (P * H) := by
  classical
  obtain ⟨a, ha⟩ := support_nonempty.mpr hH
  let β := outsideExponent S a
  have hslice_ne {d : ℕ →₀ ℕ} (hd : d ∈ H.support) :
      outsideSlice S (outsideExponent S d) H ≠ 0 := by
    intro hz
    have hh := congrArg (coeff d) hz
    rw [coeff_outsideSlice, if_pos rfl, coeff_zero] at hh
    exact mem_support_iff.mp hd hh
  by_cases hall : ∀ d ∈ H.support, outsideExponent S d = β
  · have hslice : outsideSlice S β H = H := by
      ext d
      rw [coeff_outsideSlice]
      by_cases hd : d ∈ H.support
      · rw [if_pos (hall d hd)]
      · simp only [notMem_support_iff.mp hd, ite_self]
    obtain ⟨D, hfactor, hDvars⟩ := outsideSlice_division S β
      (outsideExponent_idempotent S a) H
    rw [hslice] at hfactor
    have hD : D ≠ 0 := by
      intro hz
      exact hH (by rw [hfactor, hz, mul_zero])
    have hDw : weight D = u := by
      rw [hfactor, weight_monomial_mul] at hweight
      exact hweight
    have hb := hbase D hD hDvars hDw
    rwa [hfactor, mul_left_comm, weight_monomial_mul]
  · push_neg at hall
    obtain ⟨b, hb, hba⟩ := hall
    let γ := outsideExponent S b
    have hβγ : β ≠ γ := Ne.symm hba
    have hβN := hsmall (outsideSlice S β H) (hslice_ne ha)
      (by rw [← hweight]; exact weight_outsideSlice_le S β H)
    have hγN := hsmall (outsideSlice S γ H) (hslice_ne hb)
      (by rw [← hweight]; exact weight_outsideSlice_le S γ H)
    have hsub : (outsideSlice S β (P * H)).support ∪
        (outsideSlice S γ (P * H)).support ⊆ (P * H).support := by
      apply Finset.union_subset
      · rw [support_outsideSlice]
        exact Finset.filter_subset _ _
      · rw [support_outsideSlice]
        exact Finset.filter_subset _ _
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint (disjoint_support_outsideSlice S β γ
      (P * H) (P * H) hβγ)] at hcard
    change weight (outsideSlice S β (P * H)) +
      weight (outsideSlice S γ (P * H)) ≤ weight (P * H) at hcard
    rw [outsideSlice_mul S β P H hP, outsideSlice_mul S γ P H hP] at hcard
    omega

theorem largestPrime_of_primeOnly_weight {D : Poly K} (hprime : PrimeOnly D)
    (hweight : 2 ≤ weight D) : ∃ q : ℕ, LargestPrime D q := by
  classical
  have hvars : D.vars.Nonempty := by
    by_contra hnone
    have hempty : D.vars = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    have hsub : D.support ⊆ {0} := by
      intro d hd
      apply Finset.mem_singleton.mpr
      ext p
      exact mem_support_notMem_vars_zero hd (by simp [hempty])
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hcard
    change weight D ≤ 1 at hcard
    omega
  let q := D.vars.max' hvars
  have hqmem : q ∈ D.vars := Finset.max'_mem D.vars hvars
  have hqocc : VariableOccurs D q := (variableOccurs_iff_mem_vars D q).mpr hqmem
  refine ⟨q, hprime q hqocc, hqocc, ?_⟩
  intro p hp
  exact ⟨hprime p hp, Finset.le_max' D.vars p ((variableOccurs_iff_mem_vars D p).mp hp)⟩

theorem prime_comparison_lifting (n : ℕ) (c : ℕ → K) (u L : ℕ)
    (hc : NonzeroWeights n c) (hn25 : 25 ≤ n) (hn66 : n ≤ 66)
    (hu2 : 2 ≤ u) (hu6 : u ≤ 6) (hL : L ≤ 2 * n)
    (hbound : ∀ (D : Poly K) (q : ℕ), D ≠ 0 → Normalized D →
      LargestPrime D q → weight D = u → L ≤ weight (interval n c * D))
    (H : Poly K) (hH : H ≠ 0) (hweight : weight H = u) :
    L ≤ weight (interval n c * H) := by
  apply outside_fiber_comparison_lifting {p : ℕ | p.Prime} (interval n c) H
    (vars_interval_subset_primes n c) hH u n L hweight hL
  · intro D hD hw
    exact middle_six_term_bound n c D hc hn25 hn66 hD (hw.trans hu6)
  · intro D hD hvars hw
    have hprime : PrimeOnly D := fun p hp =>
      hvars ((variableOccurs_iff_mem_vars D p).mp hp)
    obtain ⟨e, E, _, hE, hnorm, hEw, hproducts, hoccurs⟩ := exists_normalization D hD
    have hEprime : PrimeOnly E := fun p hp => hprime p (hoccurs p hp)
    have hEweight : weight E = u := hEw.trans hw
    obtain ⟨q, hq⟩ := largestPrime_of_primeOnly_weight hEprime (hEweight ▸ hu2)
    rw [← hproducts (interval n c)]
    exact hbound E q hE hnorm hq hEweight

end WeightedPilz

import WeightedPilz.LocalizedSupport
import WeightedPilz.DirectedCut
import WeightedPilz.Normalize

/-!
# Large intervals against every multiplier in the base prime variables

A least-support counterexample can be normalized without changing its term
count. Deletion minimality supplies the directed cut; the fully proved
localized estimate then excludes that counterexample.
-/

noncomputable section

namespace WeightedPilz

variable {K : Type*} [Field K]

/-- Only prime variables at most `n/2` occur in a base multiplier. -/
def FreshPrimeBounded (n : ℕ) (D : Poly K) : Prop :=
  ∀ p, VariableOccurs D p → Nat.Prime p ∧ p ≤ n / 2

theorem freshPrimeBounded_of_support_subset (n : ℕ) (P Q : Poly K)
    (hsub : P.support ⊆ Q.support) (hQ : FreshPrimeBounded n Q) :
    FreshPrimeBounded n P := by
  intro p hp
  obtain ⟨d, hd, hdp⟩ := hp
  exact hQ p ⟨d, hsub hd, hdp⟩

theorem variableOccurs_iff_mem_vars (D : Poly K) (p : ℕ) :
    VariableOccurs D p ↔ p ∈ D.vars := by
  simp [VariableOccurs, MvPolynomial.mem_vars, Finsupp.mem_support_iff,
    Nat.pos_iff_ne_zero]

theorem exists_largestPrime_of_short (n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hD : D ≠ 0) (hshort : weight (interval n c * D) < n)
    (hbound : FreshPrimeBounded n D) : ∃ q : ℕ, LargestPrime D q := by
  classical
  have hvars : D.vars.Nonempty := by
    by_contra hnone
    have hempty : D.vars = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    have hall : ∀ d ∈ D.support, d = 0 := by
      intro d hd
      ext p
      have hnot : p ∉ D.vars := by simp [hempty]
      exact MvPolynomial.mem_support_notMem_vars_zero hd hnot
    have hsupp : D.support = {0} :=
      Finset.eq_singleton_iff_nonempty_unique_mem.mpr
        ⟨MvPolynomial.support_nonempty.mpr hD, hall⟩
    have hcoeff : MvPolynomial.coeff 0 D ≠ 0 :=
      MvPolynomial.mem_support_iff.mp (by rw [hsupp]; simp)
    have hmono : D = MvPolynomial.monomial 0 (MvPolynomial.coeff 0 D) := by
      conv_lhs => rw [MvPolynomial.as_sum D, hsupp]
      simp
    rw [hmono, mul_comm, weight_scalar_monomial_mul 0 hcoeff, weight_interval n c hc] at hshort
    omega
  let q := D.vars.max' hvars
  have hqmem : q ∈ D.vars := Finset.max'_mem D.vars hvars
  have hqocc : VariableOccurs D q := (variableOccurs_iff_mem_vars D q).mpr hqmem
  refine ⟨q, (hbound q hqocc).1, hqocc, ?_⟩
  intro p hp
  exact ⟨(hbound p hp).1,
    Finset.le_max' D.vars p ((variableOccurs_iff_mem_vars D p).mp hp)⟩

/-- Prepare an actual weighted counterexample, including every property needed
by the cut and localized theorem. No preparation premise is left undischarged. -/
theorem counterexample_preparation (n : ℕ) (c : ℕ → K) (H : Poly K)
    (hc : NonzeroWeights n c) (hH : H ≠ 0) (hHshort : weight (interval n c * H) < n)
    (hHbound : FreshPrimeBounded n H) :
    ∃ (D : Poly K) (q : ℕ), D ≠ 0 ∧ weight (interval n c * D) < n ∧
      FreshPrimeBounded n D ∧ Normalized D ∧ DeletionMinimal n c D ∧ LargestPrime D q := by
  classical
  let admissible : ℕ → Prop := fun u =>
    ∃ E : Poly K, E ≠ 0 ∧ weight (interval n c * E) < n ∧
      FreshPrimeBounded n E ∧ weight E = u
  have hex : ∃ u, admissible u := ⟨weight H, H, hH, hHshort, hHbound, rfl⟩
  obtain ⟨E, hE, hEshort, hEbound, hEweight⟩ := Nat.find_spec hex
  obtain ⟨e, D, _hfactor, hD, hnorm, hweight, hproducts, hoccurs⟩ :=
    exists_normalization E hE
  have hDshort : weight (interval n c * D) < n := by
    rw [hproducts]
    exact hEshort
  have hDbound : FreshPrimeBounded n D := by
    intro p hp
    exact hEbound p (hoccurs p hp)
  have hminimal : DeletionMinimal n c D := by
    intro T hT hTnonempty hTproper
    by_contra hnot
    let R := restrictTerms D T
    have hsupp : R.support = T := support_restrictTerms_of_subset D T hT
    have hR : R ≠ 0 := by
      intro hz
      have hne : R.support.Nonempty := by rw [hsupp]; exact hTnonempty
      simp [hz] at hne
    have hRshort : weight (interval n c * R) < n := Nat.lt_of_not_ge hnot
    have hRbound : FreshPrimeBounded n R :=
      freshPrimeBounded_of_support_subset n R D (by rw [hsupp]; exact hT) hDbound
    have hleast : Nat.find hex ≤ weight R :=
      Nat.find_min' hex ⟨R, hR, hRshort, hRbound, rfl⟩
    have hlt : weight R < weight D := by
      unfold weight
      rw [hsupp]
      exact Finset.card_lt_card ⟨hT, fun hDT => hTproper (Finset.Subset.antisymm hT hDT)⟩
    omega
  obtain ⟨q, hq⟩ := exists_largestPrime_of_short n c D hc hD hDshort hDbound
  exact ⟨D, q, hD, hDshort, hDbound, hnorm, hminimal, hq⟩

/-- Every nonzero multiplier in the base prime variables satisfies the large
weighted interval bound. This is the algebraic assertion behind `eq:large-base`. -/
theorem interval_mul_base_lower (n : ℕ) (c : ℕ → K) (H : Poly K)
    (hc : NonzeroWeights n c) (hn : 67 ≤ n) (hH : H ≠ 0)
    (hbound : FreshPrimeBounded n H) : n ≤ weight (interval n c * H) := by
  by_contra hnot
  have hshort : weight (interval n c * H) < n := by omega
  obtain ⟨D, q, hD, hDshort, hDbound, hnorm, hmin, hlargest⟩ :=
    counterexample_preparation n c H hc hH hshort hbound
  have hcut := deletionMinimal_prime_bound n q c hc D hlargest.1
    (hnorm q) hlargest.2.1 hmin hDshort
  have hlocalized := localized_expansion n q c D hc hn hD hnorm hlargest
    (hDbound q hlargest.2.1).2 hcut
  omega

end WeightedPilz

import WeightedPilz.LargeBase
import WeightedPilz.Convolution

/-! Normalize a short weighted multiple while retaining its input term budget. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

def PrimeOnly (D : Poly K) : Prop := ∀ p, VariableOccurs D p → Nat.Prime p

theorem PrimeOnly.of_support_subset {P Q : Poly K} (hQ : PrimeOnly Q)
    (hsub : P.support ⊆ Q.support) : PrimeOnly P := by
  intro p hp
  obtain ⟨d, hd, hdp⟩ := hp
  exact hQ p ⟨d, hsub hd, hdp⟩

theorem largestPrime_of_primeOnly_short (n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hD : D ≠ 0) (hshort : weight (interval n c * D) < n)
    (hprime : PrimeOnly D) : ∃ q : ℕ, LargestPrime D q := by
  classical
  have hvars : D.vars.Nonempty := by
    by_contra hnone
    have hempty : D.vars = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    have hall : ∀ d ∈ D.support, d = 0 := by
      intro d hd
      ext p
      exact MvPolynomial.mem_support_notMem_vars_zero hd (by simp [hempty])
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
  refine ⟨q, hprime q hqocc, hqocc, ?_⟩
  intro p hp
  exact ⟨hprime p hp, Finset.le_max' D.vars p ((variableOccurs_iff_mem_vars D p).mp hp)⟩

/-- The arbitrary-variable input supplies a normalized deletion-minimal
counterexample using only prime variables, with no increase in input weight. -/
theorem prime_counterexample_preparation (n : ℕ) (c : ℕ → K) (H : Poly K)
    (hc : NonzeroWeights n c) (hH : H ≠ 0) (hshort : weight (interval n c * H) < n) :
    ∃ (D : Poly K) (q : ℕ), D ≠ 0 ∧ weight (interval n c * D) < n ∧
      weight D ≤ weight H ∧ PrimeOnly D ∧ Normalized D ∧
      DeletionMinimal n c D ∧ LargestPrime D q := by
  classical
  obtain ⟨H₀, hH₀, hHvars, hHw, hHP⟩ := exists_base_multiplier_with_weight
    {p : ℕ | p.Prime} (interval n c) H (vars_interval_subset_primes n c) hH
  have hHprime : PrimeOnly H₀ := fun p hp => hHvars ((variableOccurs_iff_mem_vars H₀ p).mp hp)
  have hHshort := hHP.trans_lt hshort
  let admissible : ℕ → Prop := fun u =>
    ∃ E : Poly K, E ≠ 0 ∧ weight (interval n c * E) < n ∧ PrimeOnly E ∧ weight E = u
  have hex : ∃ u, admissible u := ⟨weight H₀, H₀, hH₀, hHshort, hHprime, rfl⟩
  obtain ⟨E, hE, hEshort, hEprime, hEweight⟩ := Nat.find_spec hex
  have hleastH : Nat.find hex ≤ weight H₀ :=
    Nat.find_min' hex ⟨H₀, hH₀, hHshort, hHprime, rfl⟩
  obtain ⟨e, D, _, hD, hnorm, hweight, hproducts, hoccurs⟩ := exists_normalization E hE
  have hDshort : weight (interval n c * D) < n := by
    rw [hproducts]
    exact hEshort
  have hDprime : PrimeOnly D := fun p hp => hEprime p (hoccurs p hp)
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
    have hRprime : PrimeOnly R := hDprime.of_support_subset (by rw [hsupp]; exact hT)
    have hleast : Nat.find hex ≤ weight R :=
      Nat.find_min' hex ⟨R, hR, hRshort, hRprime, rfl⟩
    have hlt : weight R < weight D := by
      unfold weight
      rw [hsupp]
      exact Finset.card_lt_card ⟨hT, fun hDT => hTproper (Finset.Subset.antisymm hT hDT)⟩
    omega
  obtain ⟨q, hq⟩ := largestPrime_of_primeOnly_short n c D hc hD hDshort hDprime
  exact ⟨D, q, hD, hDshort, by omega, hDprime, hnorm, hminimal, hq⟩

end WeightedPilz

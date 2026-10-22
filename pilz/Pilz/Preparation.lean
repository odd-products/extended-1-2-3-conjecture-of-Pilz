import Pilz.Statements
import Pilz.Normalize
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Tactic.FinCases

/-!
# Preparing a smooth counterexample

Choose a counterexample with the fewest multiplier terms, normalize it
without changing that number, and then select its largest prime. This uses
the same reductions as the paper; choosing global minimal term count
avoids having to transport deletion minimality through monomial division.
-/

noncomputable section

namespace Pilz

theorem freshPrimeBounded_of_support_subset (n : ℕ) (P Q : Poly)
    (hsub : P.support ⊆ Q.support) (hQ : FreshPrimeBounded n Q) :
    FreshPrimeBounded n P := by
  intro p hp
  obtain ⟨d, hd, hdp⟩ := hp
  exact hQ p ⟨d, hsub hd, hdp⟩

theorem variableOccurs_iff_mem_vars (D : Poly) (p : ℕ) :
    VariableOccurs D p ↔ p ∈ D.vars := by
  simp [VariableOccurs, MvPolynomial.mem_vars, Finsupp.mem_support_iff,
    Nat.pos_iff_ne_zero]

theorem exists_largestPrime_of_short (n : ℕ) (D : Poly)
    (hD : D ≠ 0) (hshort : weight (interval n * D) < n)
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
    have hcoeffone : MvPolynomial.coeff 0 D = (1 : ZMod 2) := by
      generalize hc : MvPolynomial.coeff 0 D = c at *
      fin_cases c <;> simp_all
    have hone : D = 1 := by
      rw [MvPolynomial.as_sum D, hsupp]
      simp [hcoeffone]
    rw [hone, mul_one, weight_interval] at hshort
    omega
  let q := D.vars.max' hvars
  have hqmem : q ∈ D.vars := Finset.max'_mem D.vars hvars
  have hqocc : VariableOccurs D q := (variableOccurs_iff_mem_vars D q).mpr hqmem
  refine ⟨q, (hbound q hqocc).1, hqocc, ?_⟩
  intro p hp
  exact ⟨(hbound p hp).1,
    Finset.le_max' D.vars p ((variableOccurs_iff_mem_vars D p).mp hp)⟩

/-- The complete elementary preparation step used after fresh elimination. -/
theorem counterexamplePreparation (n : ℕ) : CounterexamplePreparation n := by
  classical
  intro H hH hHshort hHbound
  let admissible : ℕ → Prop := fun u =>
    ∃ E : Poly, E ≠ 0 ∧ weight (interval n * E) < n ∧
      FreshPrimeBounded n E ∧ weight E = u
  have hex : ∃ u, admissible u := ⟨weight H, H, hH, hHshort, hHbound, rfl⟩
  obtain ⟨E, hE, hEshort, hEbound, hEweight⟩ := Nat.find_spec hex
  obtain ⟨e, D, _hfactor, hD, hnorm, hweight, hproducts, hoccurs⟩ :=
    exists_normalization E hE
  have hDshort : weight (interval n * D) < n := by
    rw [hproducts]
    exact hEshort
  have hDbound : FreshPrimeBounded n D := by
    intro p hp
    exact hEbound p (hoccurs p hp)
  have hminimal : DeletionMinimal n D := by
    intro T hT hTnonempty hTproper
    by_contra hnot
    let R := restrictTerms D T
    have hsupp : R.support = T := support_restrictTerms_of_subset D T hT
    have hR : R ≠ 0 := by
      intro hz
      have hne : R.support.Nonempty := by rw [hsupp]; exact hTnonempty
      simp [hz] at hne
    have hRshort : weight (interval n * R) < n := by
      exact Nat.lt_of_not_ge hnot
    have hRbound : FreshPrimeBounded n R :=
      freshPrimeBounded_of_support_subset n R D (by rw [hsupp]; exact hT) hDbound
    have hleast : Nat.find hex ≤ weight R :=
      Nat.find_min' hex ⟨R, hR, hRshort, hRbound, rfl⟩
    have hlt : weight R < weight D := by
      unfold weight
      rw [hsupp]
      exact Finset.card_lt_card ⟨hT, fun hDT => hTproper (Finset.Subset.antisymm hT hDT)⟩
    omega
  obtain ⟨q, hq⟩ := exists_largestPrime_of_short n D hD hDshort hDbound
  exact ⟨D, q, hD, hDshort, hDbound, hnorm, hminimal, hq⟩

end Pilz

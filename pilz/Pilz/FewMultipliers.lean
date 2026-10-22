import Pilz.Preparation
import Pilz.ComponentHelpers
import Pilz.TwoPrimeCounts
import Pilz.SmallCases
import Pilz.LocalizedSmallQ
import Pilz.Support

/-!
# Multipliers with few terms

The monomial case is immediate. For two terms we use the same directed
intersection estimate as the paper's cut lemma after the elementary
normalization and deletion reductions. Variable slicing first removes
variables absent from the interval, without increasing multiplier weight.
-/

noncomputable section

namespace Pilz

open MvPolynomial
open scoped BigOperators

private theorem nonzero_zmod_two_eq_one {c : ZMod 2} (hc : c ≠ 0) : c = 1 := by
  fin_cases c <;> simp_all

/-- A one-term F2 polynomial has coefficient one. -/
theorem exists_monomial_of_weight_one (H : Poly) (hH : weight H = 1) :
    ∃ d : ℕ →₀ ℕ, H = monomial d 1 := by
  classical
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hH
  have hc : coeff d H = 1 := nonzero_zmod_two_eq_one
    (mem_support_iff.mp (by rw [hd]; simp))
  refine ⟨d, ?_⟩
  rw [MvPolynomial.as_sum H, hd]
  simp [hc]

/-- One multiplier gives exactly n terms, as in the paper. -/
theorem weight_interval_mul_of_weight_one (n : ℕ) (H : Poly) (hH : weight H = 1) :
    weight (interval n * H) = n := by
  obtain ⟨d, rfl⟩ := exists_monomial_of_weight_one H hH
  rw [weight_mul_monomial, weight_interval]

/-- A short multiple cannot have a constant multiplier. -/
theorem counterexample_vars_nonempty (n : ℕ) (D : Poly)
    (hD : D ≠ 0) (hshort : weight (interval n * D) < n) : D.vars.Nonempty := by
  classical
  by_contra hnone
  have hempty : D.vars = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
  have hall : ∀ d ∈ D.support, d = 0 := by
    intro d hd
    ext p
    have hnot : p ∉ D.vars := by simp [hempty]
    exact MvPolynomial.mem_support_notMem_vars_zero hd hnot
  have hsupp : D.support = {0} := Finset.eq_singleton_iff_nonempty_unique_mem.mpr
    ⟨MvPolynomial.support_nonempty.mpr hD, hall⟩
  have hweight : weight D = 1 := by simp [weight, hsupp]
  rw [weight_interval_mul_of_weight_one n D hweight] at hshort
  exact (Nat.lt_irrefl n) hshort

/-- All elementary reductions preserve an upper bound on multiplier terms.
The resulting multiplier uses only actual primes at most n. -/
theorem exists_few_minimal_counterexample (n k : ℕ) (H : Poly)
    (hH : H ≠ 0) (hshort : weight (interval n * H) < n) (hfew : weight H ≤ k) :
    ∃ D : Poly, D ≠ 0 ∧ weight (interval n * D) < n ∧ Normalized D ∧
      DeletionMinimal n D ∧ D.vars ⊆ primesUpTo n ∧ weight D ≤ k := by
  classical
  have hIvars : (interval n).vars ⊆ primesUpTo n := by
    rw [← smoothInterval_primesUpTo_eq_interval (show n ≤ n from le_rfl)]
    exact smoothInterval_vars_subset _ _
  obtain ⟨A, hA, hAvars, hAfew, hAprod⟩ :=
    exists_base_multiplier_with_weight (primesUpTo n) (interval n) H hIvars hH
  have hAshort := hAprod.trans_lt hshort
  let admissible : ℕ → Prop := fun u => ∃ E : Poly,
    E ≠ 0 ∧ weight (interval n * E) < n ∧ E.vars ⊆ primesUpTo n ∧ weight E = u
  have hex : ∃ u, admissible u := ⟨weight A, A, hA, hAshort, hAvars, rfl⟩
  obtain ⟨E, hE, hEshort, hEvars, hEweight⟩ := Nat.find_spec hex
  obtain ⟨e, D, _hfactor, hD, hnorm, hweight, hproducts, hoccurs⟩ :=
    exists_normalization E hE
  have hDshort : weight (interval n * D) < n := by rw [hproducts]; exact hEshort
  have hDvars : D.vars ⊆ primesUpTo n := by
    intro p hp
    exact hEvars ((variableOccurs_iff_mem_vars E p).mp
      (hoccurs p ((variableOccurs_iff_mem_vars D p).mpr hp)))
  have hDleast : weight D = Nat.find hex := hweight.trans hEweight
  have hDsmall : weight D ≤ k := by
    calc
      weight D = Nat.find hex := hDleast
      _ ≤ weight A := Nat.find_min' hex ⟨A, hA, hAshort, hAvars, rfl⟩
      _ ≤ k := hAfew.trans hfew
  have hminimal : DeletionMinimal n D := by
    intro T hT hTnonempty hTproper
    by_contra hnot
    let R := restrictTerms D T
    have hsupp : R.support = T := support_restrictTerms_of_subset D T hT
    have hR : R ≠ 0 := by
      intro hz
      have hne : R.support.Nonempty := by rw [hsupp]; exact hTnonempty
      simp [hz] at hne
    have hRshort : weight (interval n * R) < n := Nat.lt_of_not_ge hnot
    have hRvars : R.vars ⊆ primesUpTo n := by
      intro p hp
      obtain ⟨d, hd, hdp⟩ := (MvPolynomial.mem_vars p).mp hp
      have hdD : d ∈ D.support := hT (by rw [← hsupp]; exact hd)
      exact hDvars ((MvPolynomial.mem_vars p).mpr ⟨d, hdD, hdp⟩)
    have hleast : Nat.find hex ≤ weight R :=
      Nat.find_min' hex ⟨R, hR, hRshort, hRvars, rfl⟩
    have hlt : weight R < weight D := by
      unfold weight
      rw [hsupp]
      exact Finset.card_lt_card ⟨hT, fun hDT => hTproper (Finset.Subset.antisymm hT hDT)⟩
    exact (Nat.not_lt_of_ge (hDleast.trans_le hleast)) hlt
  exact ⟨D, hD, hDshort, hnorm, hminimal, hDvars, hDsmall⟩

private theorem small_prime_cut_impossible (p u : ℕ)
    (hp : 2 ≤ p) (hu : u ≤ 2) (hcut : p < 2 * (u - 1)) : False := by omega

/-- The one- and two-multiplier bound, for every interval length. -/
theorem two_multipliers (n : ℕ) (H : Poly) (hH : H ≠ 0) (hfew : weight H ≤ 2) :
    n ≤ weight (interval n * H) := by
  by_contra hnot
  have hshort : weight (interval n * H) < n := Nat.lt_of_not_ge hnot
  obtain ⟨D, hD, hDshort, hnorm, hminimal, hDvars, hDsmall⟩ :=
    exists_few_minimal_counterexample n 2 H hH hshort hfew
  obtain ⟨p, hp⟩ := counterexample_vars_nonempty n D hD hDshort
  have hprime := ((mem_primesUpTo n p).mp (hDvars hp)).1
  have hpos := (variableOccurs_iff_mem_vars D p).mpr hp
  have hcut := deletionMinimal_prime_bound n p D hprime (hnorm p) hpos hminimal hDshort
  exact small_prime_cut_impossible p (weight D) hprime.two_le hDsmall hcut


private theorem count_singleton_twice (n a : ℕ) (ha : a ≤ n / 2) :
    n ≤ 2 * (n - a) := by omega

/-- A multiplier in one prime variable satisfies the full interval bound. -/
theorem one_prime (n p : ℕ) (D : Poly) (hp : Nat.Prime p) (hD : D ≠ 0)
    (hvars : D.vars ⊆ {p}) : n ≤ weight (interval n * D) := by
  classical
  by_cases h1 : weight D = 1
  · exact (weight_interval_mul_of_weight_one n D h1).ge
  have hpos := weight_pos hD
  have hu : 2 ≤ weight D := by omega
  have hprime : ∀ r ∈ ({p} : Finset ℕ), Nat.Prime r := by
    intro r hr
    have heq := Finset.mem_singleton.mp hr
    subst r
    exact hp
  have hprofile : ∀ j : ℕ, 1 ≤ j → 2 ≤ weight (smoothInterval {p} j * D) := by
    intro j hj
    by_cases hjp : j < p
    · rw [smoothInterval_eq_one_below {p} j hj (by
        intro r hr
        simpa only [Finset.mem_singleton.mp hr] using hjp), one_mul]
      exact hu
    · have hactive : ∀ r ∈ ({p} : Finset ℕ), r ≤ j := by
        intro r hr
        have heq := Finset.mem_singleton.mp hr
        subst r
        exact Nat.le_of_not_gt hjp
      have h := smooth_component_endpoints {p} {p} j D hj hD (fun _ hr => hr)
        hprime hactive
      simpa only [Finset.card_singleton] using h
  have hbudget := uniform_component_budget_set {p} n 2 D hprime hvars hprofile
  have hdiv : n / p ≤ n / 2 := Nat.div_le_div_left hp.two_le (by decide)
  have hcount := count_singleton_twice n (n / p) hdiv
  rw [← roughCount_singleton p n hp] at hcount
  exact hcount.trans hbudget

private theorem pair_primes (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    ∀ r ∈ ({p, q} : Finset ℕ), Nat.Prime r := by
  intro r hr
  rcases Finset.mem_insert.mp hr with hr | hr
  · subst r; exact hp
  · have heq := Finset.mem_singleton.mp hr
    subst r; exact hq

/-- Between p and q, two q-slices each see the constant and x_p. -/
theorem two_prime_component_middle (p q j : ℕ) (D : Poly)
    (hp : Nat.Prime p) (hpq : p < q) (hpj : p ≤ j) (hjq : j < q)
    (hnorm : Normalized D) (hocc : VariableOccurs D q) :
    4 ≤ weight (smoothInterval {p, q} j * D) := by
  have hj : 1 ≤ j := hp.pos.trans_le hpj
  exact independent_two_slice_expansion_two (smoothInterval {p, q} j) D p q
    (ne_of_lt hpq) (smoothInterval_independent_above _ j q hjq)
    (smoothInterval_coeff_zero _ j hj)
    (smoothInterval_coeff_prime _ j p hp (by simp) hpj) (hnorm q) hocc

/-- The three-term uniform profile for two support primes. -/
theorem two_prime_component_profile (p q j : ℕ) (D : Poly)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q) (hD : D ≠ 0)
    (hnorm : Normalized D) (hocc : VariableOccurs D q)
    (hu : 3 ≤ weight D) (hj : 1 ≤ j) :
    3 ≤ weight (smoothInterval {p, q} j * D) := by
  classical
  by_cases hjp : j < p
  · have hbelow : ∀ r ∈ ({p, q} : Finset ℕ), j < r := by
      intro r hr
      rcases Finset.mem_insert.mp hr with hr | hr
      · subst r; exact hjp
      · have heq := Finset.mem_singleton.mp hr
        subst r; exact hjp.trans hpq
    rw [smoothInterval_eq_one_below {p, q} j hj hbelow, one_mul]
    exact hu
  · by_cases hjq : j < q
    · exact (by decide : 3 ≤ 4).trans
        (two_prime_component_middle p q j D hp hpq (Nat.le_of_not_gt hjp) hjq hnorm hocc)
    · have hactive : ∀ r ∈ ({p, q} : Finset ℕ), r ≤ j := by
        intro r hr
        rcases Finset.mem_insert.mp hr with hr | hr
        · subst r; exact hpq.le.trans (Nat.le_of_not_gt hjq)
        · have heq := Finset.mem_singleton.mp hr
          subst r; exact Nat.le_of_not_gt hjq
      have h := smooth_component_endpoints {p, q} {p, q} j D hj hD (fun _ hr => hr)
        (pair_primes p q hp hq) hactive
      simpa [ne_of_lt hpq] using h

private theorem sum_index_two (R : Finset ℕ) (n : ℕ) :
    (∑ b ∈ R, if n / b = 2 then 1 else 0) = (R.filter (fun b => n / b = 2)).card := by
  rw [← Finset.sum_filter]
  simp

/-- For 2,3 the index-two component supplements the three-term baseline. -/
theorem two_three_component_budget (n : ℕ) (D : Poly) (hD : D ≠ 0)
    (hnorm : Normalized D) (hvars : D.vars ⊆ {2, 3})
    (hocc : VariableOccurs D 3) (hu : 3 ≤ weight D) :
    3 * roughCount {2, 3} n +
      (roughCount {2, 3} (n / 2) - roughCount {2, 3} (n / 3)) ≤
      weight (interval n * D) := by
  classical
  let R := roughNumbers {2, 3} n
  have hsum : (∑ b ∈ R, (3 + if n / b = 2 then 1 else 0)) =
      3 * roughCount {2, 3} n +
        (roughCount {2, 3} (n / 2) - roughCount {2, 3} (n / 3)) := by
    rw [Finset.sum_add_distrib, sum_index_two]
    change (∑ _b ∈ R, 3) +
      ((roughNumbers {2, 3} n).filter (fun b => n / b = 2)).card = _
    rw [card_roughNumbers_index_two]
    simp [R, roughCount, Nat.mul_comm]
  calc
    _ = ∑ b ∈ R, (3 + if n / b = 2 then 1 else 0) := hsum.symm
    _ ≤ ∑ b ∈ R, weight (smoothInterval {2, 3} (n / b) * D) := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨hbpos, hbn, _⟩ := (mem_roughNumbers {2, 3} n b).mp hb
      have hj : 1 ≤ n / b := (Nat.le_div_iff_mul_le hbpos).mpr (by simpa using hbn)
      by_cases hi : n / b = 2
      · rw [if_pos hi]
        have hfour := two_prime_component_middle 2 3 2 D (by decide) (by decide)
          (by decide) (by decide) hnorm hocc
        simpa only [hi] using hfour
      · rw [if_neg hi, Nat.add_zero]
        exact two_prime_component_profile 2 3 (n / b) D (by decide) (by decide)
          (by decide) hD hnorm hocc hu hj
    _ = _ := (weight_interval_mul_eq_sum_rough_components {2, 3} n D
      (pair_primes 2 3 (by decide) (by decide)) hvars).symm

/-- The paper's two-prime theorem, including all small interval lengths. -/
theorem two_primes (n p q : ℕ) (D : Poly)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hD : D ≠ 0) (hnorm : Normalized D) (hvars : D.vars ⊆ {p, q}) :
    n ≤ weight (interval n * D) := by
  classical
  by_cases hfew : weight D ≤ 2
  · exact two_multipliers n D hD hfew
  have hu : 3 ≤ weight D := by omega
  by_cases hqocc : q ∈ D.vars
  · have hocc := (variableOccurs_iff_mem_vars D q).mpr hqocc
    by_cases hexcept : p ≠ 2 ∨ q ≠ 3
    · have hcount := roughCount_two_primes_three p q n hp hq hpq hexcept
      have hbudget := uniform_component_budget_set {p, q} n 3 D
        (pair_primes p q hp hq) hvars
        (fun j hj => two_prime_component_profile p q j D hp hq hpq hD hnorm hocc hu hj)
      exact hcount.trans hbudget
    · have hp2 : p = 2 := by tauto
      have hq3 : q = 3 := by tauto
      subst p q
      by_cases hn : n ≤ 4
      · exact conjectureAt_le_four n hn D hD
      · exact (roughCount_two_three_with_index_two n (by omega)).trans
          (two_three_component_budget n D hD hnorm hvars hocc hu)
  · apply one_prime n p D hp hD
    intro r hr
    have hmem := hvars hr
    rcases Finset.mem_insert.mp hmem with heq | heq
    · exact Finset.mem_singleton.mpr heq
    · have hrq := Finset.mem_singleton.mp heq
      subst r
      exact False.elim (hqocc hr)

private theorem three_term_prime (p u : ℕ) (hp : 2 ≤ p) (hu : u ≤ 3)
    (hcut : p < 2 * (u - 1)) : p = 2 ∨ p = 3 := by omega

/-- Three multipliers reduce by the directed cut to the two-prime theorem. -/
theorem three_multipliers (n : ℕ) (H : Poly) (hH : H ≠ 0) (hfew : weight H ≤ 3) :
    n ≤ weight (interval n * H) := by
  by_contra hnot
  have hshort : weight (interval n * H) < n := Nat.lt_of_not_ge hnot
  obtain ⟨D, hD, hDshort, hnorm, hminimal, hDvars, hDsmall⟩ :=
    exists_few_minimal_counterexample n 3 H hH hshort hfew
  have hvars : D.vars ⊆ {2, 3} := by
    intro p hp
    have hprime := ((mem_primesUpTo n p).mp (hDvars hp)).1
    have hpos := (variableOccurs_iff_mem_vars D p).mpr hp
    have hcut := deletionMinimal_prime_bound n p D hprime (hnorm p) hpos hminimal hDshort
    rcases three_term_prime p (weight D) hprime.two_le hDsmall hcut with rfl | rfl <;> simp
  exact (Nat.not_lt_of_ge (two_primes n 2 3 D (by decide) (by decide) (by decide)
    hD hnorm hvars)) hDshort

end Pilz

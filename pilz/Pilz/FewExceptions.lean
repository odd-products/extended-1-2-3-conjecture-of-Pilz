import Pilz.FourSmallComponents
import Pilz.FourTermCut

/-! The strengthened bounds for four-term multipliers at the exceptional lengths. -/

noncomputable section

namespace Pilz

open MvPolynomial
open scoped BigOperators

private theorem vars_nonempty_of_four_terms (D : Poly) (hw : weight D = 4) :
    D.vars.Nonempty := by
  classical
  by_contra hnone
  have hempty : D.vars = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
  have hsupp : D.support ⊆ {0} := by
    intro d hd
    apply Finset.mem_singleton.mpr
    ext p
    exact MvPolynomial.mem_support_notMem_vars_zero hd (by simp [hempty])
  have hc := Finset.card_le_card hsupp
  change weight D ≤ _ at hc
  rw [hw, Finset.card_singleton] at hc
  omega

/-- A normalized four-term polynomial either uses a foreign variable or
has an actual largest prime variable. -/
theorem four_term_variable_cases (D : Poly) (hw : weight D = 4) :
    (∃ q : ℕ, ¬Nat.Prime q ∧ VariableOccurs D q) ∨
      (∃ q : ℕ, LargestPrime D q) := by
  classical
  by_cases hforeign : ∃ q : ℕ, ¬Nat.Prime q ∧ VariableOccurs D q
  · exact Or.inl hforeign
  · right
    have hvars := vars_nonempty_of_four_terms D hw
    let q := D.vars.max' hvars
    have hq : VariableOccurs D q := (variableOccurs_iff_mem_vars D q).mpr
      (Finset.max'_mem D.vars hvars)
    have hall : ∀ p : ℕ, VariableOccurs D p → Nat.Prime p := by
      intro p hp
      by_contra hnot
      exact hforeign ⟨p, hnot, hp⟩
    refine ⟨q, hall q hq, hq, ?_⟩
    intro p hp
    exact ⟨hall p hp,
      Finset.le_max' D.vars p ((variableOccurs_iff_mem_vars D p).mp hp)⟩

private theorem four_term_bound_from_largest (n b : ℕ) (hnb : b ≤ 2 * n)
    (hlargest : ∀ D : Poly, D ≠ 0 → weight D = 4 → Normalized D →
      ∀ q : ℕ, LargestPrime D q → b ≤ weight (interval n * D))
    (H : Poly) (hw : weight H = 4) : b ≤ weight (interval n * H) := by
  have hH : H ≠ 0 := by intro hz; simp [hz] at hw
  obtain ⟨e, D, _hfactor, hD, hnorm, hweight, hproducts, _hoccurs⟩ :=
    exists_normalization H hH
  have hDweight : weight D = 4 := hweight.trans hw
  rw [← hproducts (interval n)]
  rcases four_term_variable_cases D hDweight with ⟨q, hq, hocc⟩ | ⟨q, hq⟩
  · exact hnb.trans (four_term_cut_nonprime n q D hq hDweight hnorm hocc)
  · exact hlargest D hD hDweight hnorm q hq

private theorem prime_below_seven (q : ℕ) (hq : Nat.Prime q) (hlt : q < 7) :
    q = 2 ∨ q = 3 ∨ q = 5 := by
  have hsmall : ∀ r : Fin 7, Nat.Prime r.val →
      r.val = 2 ∨ r.val = 3 ∨ r.val = 5 := by decide
  exact hsmall ⟨q, hlt⟩ hq

/-- The paper's forty exception, for every four-term multiplier. -/
theorem four_term_at_forty (D : Poly) (hw : weight D = 4) :
    44 ≤ weight (interval 40 * D) := by
  apply four_term_bound_from_largest 40 44 (by decide) ?_ D hw
  intro E hE hweight hnorm q hq
  by_cases hq7 : 7 ≤ q
  · have hcut := four_term_cut_seven 40 q E hq.1 hq7 hweight hnorm hq.2.1
    omega
  · rcases prime_below_seven q hq.1 (by omega) with rfl | rfl | rfl
    · exact (four_term_largest_two_exceptions E hE hweight hq).1
    · exact (four_term_largest_three_exceptions E hE hweight hnorm hq).1
    · exact four_term_largest_five_at_forty E hE hweight hnorm hq

/-- The strengthened bound on the four lengths 49,50,51,52. -/
theorem four_term_at_forty_nine_to_fifty_two (n : ℕ) (D : Poly)
    (hn : 49 ≤ n) (hn' : n ≤ 52) (hw : weight D = 4) :
    56 ≤ weight (interval n * D) := by
  apply four_term_bound_from_largest n 56 (by omega) ?_ D hw
  intro E hE hweight hnorm q hq
  by_cases hq7 : 7 ≤ q
  · have hcut := four_term_cut_seven n q E hq.1 hq7 hweight hnorm hq.2.1
    omega
  · rcases prime_below_seven q hq.1 (by omega) with rfl | rfl | rfl
    · exact (four_term_largest_two_exceptions E hE hweight hq).2.2 n hn
    · exact (four_term_largest_three_exceptions E hE hweight hnorm hq).2.2 n hn
    · exact four_term_largest_five_ge_forty_nine n E hn hE hweight hnorm hq

/-- The exact seven-component decomposition used at n=27 and q=5. -/
theorem four_term_five_components_at_twenty_seven (D : Poly)
    (hvars : D.vars ⊆ primesUpTo 5) :
    weight (interval 27 * D) =
      weight (smoothInterval (primesUpTo 5) 27 * D) +
      weight (interval 3 * D) + 2 * weight (interval 2 * D) + 3 * weight D := by
  have hrough : roughNumbers (primesUpTo 5) 27 = {1, 7, 11, 13, 17, 19, 23} := by decide
  rw [weight_interval_mul_eq_sum_rough_components (primesUpTo 5) 27 D
    (primesUpTo_prime 5) hvars, hrough]
  have h3 : smoothInterval (primesUpTo 5) 3 = interval 3 :=
    smoothInterval_primesUpTo_eq_interval (by decide)
  have h2 : smoothInterval (primesUpTo 5) 2 = interval 2 :=
    smoothInterval_primesUpTo_eq_interval (by decide)
  simp [Finset.sum_insert, h3, h2, smoothInterval_one]
  omega

/-- The q=5 case at 27, with the two independently proved inputs explicit. -/
theorem four_term_largest_five_at_twenty_seven (D : Poly) (hD : D ≠ 0)
    (hw : weight D = 4) (hnorm : Normalized D) (hlargest : LargestPrime D 5)
    (hcore : 7 ≤ distance (smoothInterval (primesUpTo 5) 27))
    (hcompat : 12 ≤ weight (interval 2 * D) + weight (interval 3 * D)) :
    36 ≤ weight (interval 27 * D) := by
  have hcoreMul := hcore.trans
    (distance_le_weight_mul (smoothInterval (primesUpTo 5) 27) D hD)
  change 7 ≤ weight (smoothInterval (primesUpTo 5) 27 * D) at hcoreMul
  have heven := four_term_product_even (smoothInterval (primesUpTo 5) 27) D hw
  obtain ⟨k, hk⟩ := heven
  have hcoreEight : 8 ≤ weight (smoothInterval (primesUpTo 5) 27 * D) := by omega
  have htwo := component_profile_before 5 2 D (by decide) (by decide) hnorm hlargest
  have hpi : primeCount 2 = 1 := by decide
  have h2 : smoothInterval (primesUpTo 5) 2 = interval 2 :=
    smoothInterval_primesUpTo_eq_interval (by decide)
  rw [hpi, h2] at htwo
  rw [four_term_five_components_at_twenty_seven D (largestPrime_vars_subset D 5 hlargest), hw]
  omega

/-- The complete 27 exception once its smooth-core and compatibility inputs
have been supplied by their independent proofs. -/
theorem four_term_at_twenty_seven_of_core_compatibility
    (hcore : 7 ≤ distance (smoothInterval (primesUpTo 5) 27))
    (hcompat : ∀ D : Poly, weight D = 4 → Normalized D → VariableOccurs D 5 →
      12 ≤ weight (interval 2 * D) + weight (interval 3 * D))
    (D : Poly) (hw : weight D = 4) : 36 ≤ weight (interval 27 * D) := by
  apply four_term_bound_from_largest 27 36 (by decide) ?_ D hw
  intro E hE hweight hnorm q hq
  by_cases hq7 : 7 ≤ q
  · have hcut := four_term_cut_seven 27 q E hq.1 hq7 hweight hnorm hq.2.1
    omega
  · rcases prime_below_seven q hq.1 (by omega) with rfl | rfl | rfl
    · exact (four_term_largest_two_exceptions E hE hweight hq).2.1
    · exact (four_term_largest_three_exceptions E hE hweight hnorm hq).2.1
    · exact four_term_largest_five_at_twenty_seven E hE hweight hnorm hq hcore
        (hcompat E hweight hnorm hq.2.1)

end Pilz

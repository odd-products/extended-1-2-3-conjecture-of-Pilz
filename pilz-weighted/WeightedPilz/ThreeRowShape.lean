import WeightedPilz.RowWeights

/-! The exact row shape when two endpoint bounds exhaust a seven-term budget. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ K : Type*} [Field K]

theorem three_row_shape_four_one_two (G : MvPolynomial (Option σ) K)
    (lo hi : ℕ) (hne : lo ≠ hi)
    (hlo : 4 ≤ weight ((optionEquivLeft K σ G).coeff lo))
    (hhi : 2 ≤ weight ((optionEquivLeft K σ G).coeff hi))
    (hrows : 3 ≤ (optionEquivLeft K σ G).support.card) (hw : weight G ≤ 7) :
    ∃ mid : ℕ, mid ≠ lo ∧ mid ≠ hi ∧
      (optionEquivLeft K σ G).support = {lo, mid, hi} ∧
      weight ((optionEquivLeft K σ G).coeff lo) = 4 ∧
      weight ((optionEquivLeft K σ G).coeff mid) = 1 ∧
      weight ((optionEquivLeft K σ G).coeff hi) = 2 := by
  classical
  let W := optionEquivLeft K σ G
  have hcard : ({lo, hi} : Finset ℕ).card < W.support.card := by
    have hp := Finset.card_le_two (a := lo) (b := hi)
    change 3 ≤ W.support.card at hrows
    omega
  obtain ⟨mid, hm, hmout⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hmne : mid ≠ lo ∧ mid ≠ hi := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hmout
  have hmid : 1 ≤ weight (W.coeff mid) := by
    exact Nat.succ_le_iff.mpr (by
      simpa [weight, Finset.card_pos, support_nonempty] using Polynomial.mem_support_iff.mp hm)
  have hsum : weight (W.coeff lo) + weight (W.coeff mid) + weight (W.coeff hi) ≤ weight G := by
    have h := weight_option_slices_le G {lo, mid, hi}
    simpa only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
      Finset.mem_singleton, hne, hmne.1.symm, hmne.2, or_self, not_false_eq_true,
      add_assoc] using h
  change 4 ≤ weight (W.coeff lo) at hlo
  change 2 ≤ weight (W.coeff hi) at hhi
  have hloeq : weight (W.coeff lo) = 4 := by omega
  have hmidEq : weight (W.coeff mid) = 1 := by omega
  have hhieq : weight (W.coeff hi) = 2 := by omega
  refine ⟨mid, hmne.1, hmne.2, ?_, hloeq, hmidEq, hhieq⟩
  apply Finset.Subset.antisymm
  · intro k hk
    by_contra hknot
    have hkne : k ≠ lo ∧ k ≠ mid ∧ k ≠ hi := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hknot
    have hkpos : 1 ≤ weight (W.coeff k) := by
      exact Nat.succ_le_iff.mpr (by
        simpa [weight, Finset.card_pos, support_nonempty] using Polynomial.mem_support_iff.mp hk)
    have h := weight_option_slices_le G {lo, mid, hi, k}
    have h' : weight (W.coeff lo) + weight (W.coeff mid) + weight (W.coeff hi) +
        weight (W.coeff k) ≤ weight G := by
      simpa only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
        Finset.mem_singleton, hne, hmne.1.symm, hmne.2,
        hkne.1.symm, hkne.2.1.symm, hkne.2.2.symm,
        or_self, not_false_eq_true, add_assoc] using h
    omega
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · apply Polynomial.mem_support_iff.mpr
      intro hz
      change W.coeff k = 0 at hz
      simp [hz, weight] at hlo
    · exact hm
    · apply Polynomial.mem_support_iff.mpr
      intro hz
      change W.coeff k = 0 at hz
      simp [hz, weight] at hhi

end WeightedPilz

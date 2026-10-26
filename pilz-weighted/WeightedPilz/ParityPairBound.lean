import WeightedPilz.ParityTwoPairs
import WeightedPilz.ParityClassCount

/-! The complete three-plus-one parity bound at the three exceptional indices. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K] [ExpChar K 2]

private theorem residue_canonical_of_positive (q : ℕ) (P : Poly K) (α : ℕ →₀ ℕ)
    (h : 0 < residueWeight q P α) : residueExponent q α = α := by
  classical
  obtain ⟨d, hd⟩ := Finset.card_pos.mp h
  have hdα : residueExponent q d = α := by
    by_contra hne
    have hcoeff := MvPolynomial.mem_support_iff.mp hd
    rw [coeff_residuePart, if_neg hne] at hcoeff
    exact hcoeff rfl
  rw [← hdα, residueExponent_idempotent]

theorem interval_unpairedSquarefree_bound (n : ℕ) (hn : n ≤ 48)
    (c : ℕ → K) (hc : NonzeroWeights n c)
    (D : Poly K) (β γ : ℕ →₀ ℕ)
    (hβ : residueWeight 2 D β = 3) (hγ : residueWeight 2 D γ = 1)
    (hD : D = residuePart 2 D β + residuePart 2 D γ) :
    4 * (unpairedSquarefree n (residueExponent 2 (β + γ))).card ≤ weight (interval n c * D) := by
  classical
  apply interval_parity_unpaired_sum n hn c hc D β γ hβ hγ hD
  · intro s hs
    have hsmem := (Finset.mem_filter.mp hs).1
    have hsq := (Arithmetic.mem_squarefreeNumbers n s).mp hsmem
    exact ⟨hsq.2.2, hsq.2.1⟩
  · intro s hs
    have hnot := (Finset.mem_filter.mp hs).2
    have hshift : residueExponent 2 (s.factorization + β + γ) =
        residueExponent 2 (s.factorization + residueExponent 2 (β + γ)) := by
      ext p
      simp [residueExponent_apply, Finsupp.add_apply, Nat.add_mod, Nat.add_assoc]
    by_contra hne
    have hmem := mem_residueIndices_of_part_ne_zero 2 (interval n c) hne
    rw [residueIndices_interval_parity n c hc, hshift] at hmem
    exact hnot hmem

/-- Lemma `fin-parity-pair`, with arbitrary coefficients and arbitrary
multiplier variables, including variables not encoding primes. -/
theorem interval_three_one_parity_bound (n : ℕ)
    (hn : n = 27 ∨ n = 28 ∨ n = 36)
    (c : ℕ → K) (hc : NonzeroWeights n c)
    (D : Poly K) (β γ : ℕ →₀ ℕ)
    (hβ : residueWeight 2 D β = 3) (hγ : residueWeight 2 D γ = 1)
    (hD : D = residuePart 2 D β + residuePart 2 D γ) :
    (if n = 36 then 44 else 36) ≤ weight (interval n c * D) := by
  classical
  let ν := residueExponent 2 (β + γ)
  have hβcan := residue_canonical_of_positive 2 D β (by omega)
  have hγcan := residue_canonical_of_positive 2 D γ (by omega)
  have hνlt : ∀p, ν p < 2 := fun p => Nat.mod_lt _ (by decide)
  have hν0 : ν ≠ 0 := by
    intro hz
    have hβγ : β = γ := by
      ext p
      have hb := congrArg (fun d : ℕ →₀ ℕ => d p) hβcan
      have hg := congrArg (fun d : ℕ →₀ ℕ => d p) hγcan
      have hv := congrArg (fun d : ℕ →₀ ℕ => d p) hz
      simp only [ν, residueExponent_apply, Finsupp.add_apply, Finsupp.zero_apply] at hb hg hv
      omega
    rw [hβγ] at hβ
    omega
  by_cases hνtwo : ν = Finsupp.single 2 1
  · have hb := interval_parity_two_budget n (by omega) c hc D β γ hβ hγ hD hνtwo
    obtain ⟨h27, h28, h36⟩ := Arithmetic.parity_two_budgets
    rcases hn with rfl | rfl | rfl <;> norm_num <;> omega
  · have hex : ∃p, p ≠ 2 ∧ ν p = 1 := by
      by_contra hh
      push_neg at hh
      have hzero : ∀p, p ≠ 2 → ν p = 0 := by
        intro p hp
        have h := hνlt p
        have hne := hh p hp
        omega
      have htwo : ν 2 = 1 := by
        have h := hνlt 2
        by_contra hne
        have hz : ν 2 = 0 := by omega
        apply hν0
        ext p
        by_cases hp : p = 2
        · simpa [hp] using hz
        · exact hzero p hp
      apply hνtwo
      ext p
      by_cases hp : p = 2
      · simp [hp, htwo]
      · simp [Finsupp.single_eq_of_ne hp, hzero p hp]
    obtain ⟨p, hp2, hpν⟩ := hex
    have hpmod : ν p % 2 = 1 := by rw [hpν]
    have hweight := interval_unpairedSquarefree_bound n (by omega) c hc D β γ hβ hγ hD
    change 4 * (unpairedSquarefree n ν).card ≤ _ at hweight
    by_cases hp : p.Prime
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      obtain ⟨h27, h28, h36⟩ := unpairedSquarefree_odd_prime_bounds ν p hp hp3 hpmod
      rcases hn with rfl | rfl | rfl <;> norm_num <;> omega
    · rw [unpairedSquarefree_eq_of_nonprime n ν p hp hpmod] at hweight
      obtain ⟨h27, h28, h36⟩ := Arithmetic.parity_pair_squarefree_counts
      rcases hn with rfl | rfl | rfl <;> norm_num <;> omega

end WeightedPilz


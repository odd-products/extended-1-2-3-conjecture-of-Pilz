import WeightedPilz.ParityUnpaired

/-! Exact pairing of the odd and even squarefree classes for displacement two. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K] [ExpChar K 2]

private theorem squarefree_double {s : ℕ} (hs : Squarefree s) (hodd : s % 2 = 1) :
    Squarefree (2 * s) :=
  (Nat.squarefree_mul (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hodd))).mpr
    ⟨Nat.prime_two.squarefree, hs⟩

private theorem parity_shift_double {s : ℕ} (hs : Squarefree s) (hodd : s % 2 = 1)
    (β γ : ℕ →₀ ℕ) (hν : residueExponent 2 (β + γ) = Finsupp.single 2 1) :
    residueExponent 2 ((2 * s).factorization + β + γ) = s.factorization := by
  have hs2 : s.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by intro h; have := Nat.mod_eq_zero_of_dvd h; omega)
  rw [Nat.factorization_mul (by decide : 2 ≠ 0) hs.ne_zero,
    Nat.prime_two.factorization]
  ext p
  have hνp := congrArg (fun d : ℕ →₀ ℕ => d p) hν
  have hsp := congrArg (fun d : ℕ →₀ ℕ => d p) (residue_factorization_squarefree hs)
  simp only [residueExponent_apply, Finsupp.add_apply] at hνp hsp ⊢
  by_cases hp : p = 2
  · subst p
    simp only [Finsupp.single_eq_same, hs2] at hνp ⊢
    omega
  · simp only [Finsupp.single_eq_of_ne hp] at hνp ⊢
    omega

/-- When the two input residues differ only at the prime two, summing the
actual output pair costs gives precisely the finite arithmetic table. -/
theorem interval_parity_two_budget (n : ℕ) (hn : n ≤ 48)
    (c : ℕ → K) (hc : NonzeroWeights n c)
    (D : Poly K) (β γ : ℕ →₀ ℕ)
    (hβ : residueWeight 2 D β = 3) (hγ : residueWeight 2 D γ = 1)
    (hD : D = residuePart 2 D β + residuePart 2 D γ)
    (hν : residueExponent 2 (β + γ) = Finsupp.single 2 1) :
    Arithmetic.parityTwoBudget n ≤ weight (interval n c * D) := by
  classical
  let U := Arithmetic.oddSquarefreeNumbers n
  let V := U ∪ U.image (fun s => 2 * s)
  let f := fun s : ℕ => residueExponent 2 (s.factorization + β)
  have hU : ∀s∈U, Squarefree s ∧ s % 2 = 1 := by
    intro s hs
    obtain ⟨hs, hodd⟩ := Finset.mem_filter.mp hs
    exact ⟨((Arithmetic.mem_squarefreeNumbers n s).mp hs).2.2, hodd⟩
  have hV : ∀s∈V, Squarefree s := by
    intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · exact (hU s hs).1
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      exact squarefree_double (hU t ht).1 (hU t ht).2
  have hdis : Disjoint U (U.image (fun s => 2 * s)) := by
    apply Finset.disjoint_left.mpr
    intro s hs himage
    obtain ⟨t, _, hts⟩ := Finset.mem_image.mp himage
    change 2 * t = s at hts
    have hodd := (hU s hs).2
    omega
  have htwo : Set.InjOn (fun s : ℕ => 2 * s) (U : Set ℕ) := by
    intro s hs t ht heq
    change 2 * s = 2 * t at heq
    omega
  have hfinj := parity_translated_factorization_injective V hV β
  have hsum := sum_residueWeights_le 2 (interval n c * D) (V.image f)
  rw [Finset.sum_image hfinj] at hsum
  change (∑s∈U ∪ U.image (fun s => 2 * s), residueWeight 2 (interval n c * D) (f s)) ≤ _ at hsum
  rw [Finset.sum_union hdis, Finset.sum_image htwo, ← Finset.sum_add_distrib] at hsum
  have hcost : ∀s∈U,
      Arithmetic.parityPairCost (Nat.sqrt (n / (2 * s))) (Nat.sqrt (n / s)) ≤
      residueWeight 2 (interval n c * D) (f s) +
        residueWeight 2 (interval n c * D) (f (2 * s)) := by
    intro s hs
    have hsq := (hU s hs).1
    have hodd := (hU s hs).2
    have h := interval_parity_pair_cost n (2 * s) s hn c hc (squarefree_double hsq hodd) hsq
      D β γ hβ hγ hD (parity_shift_double hsq hodd β γ hν)
    simpa only [f, Nat.add_comm] using h
  exact (Finset.sum_le_sum hcost).trans hsum

end WeightedPilz

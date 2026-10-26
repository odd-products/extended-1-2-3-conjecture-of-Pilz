import WeightedPilz.ParityPairing

/-! Summing the surviving costs of all unpaired occupied parity classes. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K] [ExpChar K 2]

theorem parity_translated_factorization_injective
    (U : Finset ℕ) (hU : ∀ s ∈ U, Squarefree s) (β : ℕ →₀ ℕ) :
    Set.InjOn (fun s : ℕ => residueExponent 2 (s.factorization + β)) (U : Set ℕ) := by
  intro s hs t ht heq
  have hfact := residueExponent_add_right_cancel 2 s.factorization t.factorization β heq
  rw [residue_factorization_squarefree (hU s hs), residue_factorization_squarefree (hU t ht)] at hfact
  exact Nat.factorization_inj (hU s hs).ne_zero (hU t ht).ne_zero hfact

private theorem parity_cross_translate (s t β γ : ℕ →₀ ℕ)
    (hs : residueExponent 2 s = s) (ht : residueExponent 2 t = t)
    (h : residueExponent 2 (s + β) = residueExponent 2 (t + γ)) :
    residueExponent 2 (s + β + γ) = t := by
  ext i
  have hi := congrArg (fun d : ℕ →₀ ℕ => d i) h
  have hti := congrArg (fun d : ℕ →₀ ℕ => d i) ht
  simp only [residueExponent_apply, Finsupp.add_apply] at hi hti ⊢
  omega

/-- Every unpaired occupied kernel class contributes its complete three-term
cost and its complete monomial cost, in distinct output classes. -/
theorem interval_parity_unpaired_sum (n : ℕ) (hn : n ≤ 48)
    (c : ℕ → K) (hc : NonzeroWeights n c)
    (D : Poly K) (β γ : ℕ →₀ ℕ)
    (hβ : residueWeight 2 D β = 3) (hγ : residueWeight 2 D γ = 1)
    (hD : D = residuePart 2 D β + residuePart 2 D γ)
    (U : Finset ℕ) (hU : ∀s∈U, Squarefree s ∧ s ≤ n)
    (hempty : ∀s∈U,
      residuePart 2 (interval n c) (residueExponent 2 (s.factorization + β + γ)) = 0) :
    4 * U.card ≤ weight (interval n c * D) := by
  classical
  let f := fun s : ℕ => residueExponent 2 (s.factorization + β)
  let g := fun s : ℕ => residueExponent 2 (s.factorization + γ)
  have hfs := parity_translated_factorization_injective U (fun s hs => (hU s hs).1) β
  have hgs := parity_translated_factorization_injective U (fun s hs => (hU s hs).1) γ
  have hdis : Disjoint (U.image f) (U.image g) := by
    apply Finset.disjoint_left.mpr
    intro α hαf hαg
    obtain ⟨s, hs, hsf⟩ := Finset.mem_image.mp hαf
    obtain ⟨t, ht, htg⟩ := Finset.mem_image.mp hαg
    have hcross := parity_cross_translate s.factorization t.factorization β γ
      (residue_factorization_squarefree (hU s hs).1)
      (residue_factorization_squarefree (hU t ht).1) (hsf.trans htg.symm)
    have hz := hempty s hs
    rw [hcross] at hz
    have hw := interval_parity_class_weight n t c hc (hU t ht).1
    rw [residueWeight, hz] at hw
    have hpos : 0 < Nat.sqrt (n / t) := Nat.sqrt_pos.mpr
      (Nat.div_pos (hU t ht).2 (Nat.pos_of_ne_zero (hU t ht).1.ne_zero))
    simp only [weight_zero] at hw
    omega
  have hsum := sum_residueWeights_le 2 (interval n c * D) (U.image f ∪ U.image g)
  rw [Finset.sum_union hdis, Finset.sum_image hfs, Finset.sum_image hgs, ← Finset.sum_add_distrib] at hsum
  have hcost : ∀s∈U, 4 ≤ residueWeight 2 (interval n c * D) (f s) +
      residueWeight 2 (interval n c * D) (g s) := by
    intro s hs
    have hsSq := (hU s hs).1
    have hthree := interval_parity_unpaired_three_cost n s hn c hc hsSq D β γ hβ hD (hempty s hs)
    have hconv := parity_convolution_two (interval n c) D s.factorization γ β
      (residue_factorization_squarefree hsSq) (hD.trans (add_comm _ _))
    have hz : residuePart 2 (interval n c) (residueExponent 2 (s.factorization + γ + β)) = 0 := by
      convert hempty s hs using 1 <;> ac_rfl
    rw [hz, zero_mul, add_zero] at hconv
    have hone : residueWeight 2 (interval n c * D) (g s) = Nat.sqrt (n / s) := by
      rw [residueWeight, hconv]
      exact interval_parity_mul_one_weight n s c hc hsSq D γ hγ
    have hkpos : 0 < Nat.sqrt (n / s) := Nat.sqrt_pos.mpr
      (Nat.div_pos (hU s hs).2 (Nat.pos_of_ne_zero hsSq.ne_zero))
    have hkmax : Nat.sqrt (n / s) ≤ 6 :=
      (Nat.sqrt_le_sqrt ((Nat.div_le_self n s).trans hn)).trans
        (Nat.le_of_lt_succ (Nat.sqrt_lt.mpr (by decide : 48 < 7 * 7)))
    have hkcost : 4 ≤ Arithmetic.parityTripleCost (Nat.sqrt (n / s)) + Nat.sqrt (n / s) := by
      generalize Nat.sqrt (n / s) = k at *
      interval_cases k <;> norm_num [Arithmetic.parityTripleCost]
    change _ ≤ residueWeight 2 (interval n c * D) (f s) at hthree
    omega
  have hsumcost := Finset.sum_le_sum hcost
  simpa only [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm] using hsumcost.trans hsum

end WeightedPilz

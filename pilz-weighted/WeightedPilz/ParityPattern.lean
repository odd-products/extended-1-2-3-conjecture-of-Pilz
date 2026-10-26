import WeightedPilz.ParityPairBound

/-! Extracting the actual three-plus-one decomposition from a four-term input. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem residue_three_one_decomposition (q : ℕ) (D : Poly K) (hD : weight D = 4)
    (β : ℕ →₀ ℕ) (hβ : residueWeight q D β = 3) :
    ∃γ, residueWeight q D γ = 1 ∧ D = residuePart q D β + residuePart q D γ := by
  classical
  let R : Poly K := Finsupp.filter (fun d => residueExponent q d ≠ β) D
  have hRsupport : R.support = D.support.filter (fun d => residueExponent q d ≠ β) := by
    exact Finsupp.support_filter _ _
  have hsplit : D = residuePart q D β + R := by
    ext d
    rw [coeff_add, coeff_residuePart]
    have hRcoeff : coeff d R = if residueExponent q d ≠ β then coeff d D else 0 := rfl
    rw [hRcoeff]
    by_cases h : residueExponent q d = β <;> simp [h]
  have hRwt : weight R = 1 := by
    have hcard := Finset.filter_card_add_filter_neg_card_eq_card
      (s := D.support) (fun d => residueExponent q d = β)
    rw [← hRsupport] at hcard
    have hβcard : (D.support.filter (fun d => residueExponent q d = β)).card = 3 := by
      have he : D.support.filter (fun d => residueExponent q d = β) =
          (residuePart q D β).support := by ext d; simp [support_residuePart]
      rw [he]
      exact hβ
    change (D.support.filter (fun d => residueExponent q d = β)).card + weight R = weight D at hcard
    omega
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hRwt
  have hdR : d ∈ R.support := by rw [hd]; simp
  have hdβ : residueExponent q d ≠ β := by
    rw [hRsupport] at hdR
    exact (Finset.mem_filter.mp hdR).2
  have hmono : R = monomial d (coeff d R) := (Finsupp.support_eq_singleton.mp hd).2
  have hpartA : residuePart q (residuePart q D β) (residueExponent q d) = 0 := by
    ext e
    by_cases he : residueExponent q e = residueExponent q d
    · have heβ : residueExponent q e ≠ β := he ▸ hdβ
      simp [coeff_residuePart, he, hdβ]
    · simp [coeff_residuePart, he]
  have hpartR : residuePart q R (residueExponent q d) = R := by
    rw [hmono, residuePart_monomial, if_pos rfl]
  have hpartD : residuePart q D (residueExponent q d) = R := by
    conv_lhs => rw [hsplit, residuePart_add]
    rw [hpartA, hpartR, zero_add]
  refine ⟨residueExponent q d, ?_, ?_⟩
  · rw [residueWeight, hpartD]
    exact hRwt
  · rwa [hpartD]

theorem interval_four_term_three_class_bound [ExpChar K 2] (n : ℕ)
    (hn : n = 27 ∨ n = 28 ∨ n = 36)
    (c : ℕ → K) (hc : NonzeroWeights n c) (D : Poly K) (hD : weight D = 4)
    (hthree : ∃β, residueWeight 2 D β = 3) :
    (if n = 36 then 44 else 36) ≤ weight (interval n c * D) := by
  obtain ⟨β, hβ⟩ := hthree
  obtain ⟨γ, hγ, hsplit⟩ := residue_three_one_decomposition 2 D hD β hβ
  exact interval_three_one_parity_bound n hn c hc D β γ hβ hγ hsplit

end WeightedPilz

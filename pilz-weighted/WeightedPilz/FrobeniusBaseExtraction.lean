import WeightedPilz.Frobenius

/-! Frobenius extraction preserves coordinate independence of the multiplier. -/

noncomputable section

namespace WeightedPilz

open MvPolynomial

variable {σ K : Type*} [Field K]

theorem frobenius_extraction_preserving_zero_coordinates
    (p e : ℕ) [ExpChar K p] (P E : MvPolynomial σ K) (Z : Set σ)
    (hU : P ^ p ^ e * E ≠ 0)
    (hE : ∀ z ∈ Z, ∀ d ∈ E.support, d z = 0) :
    ∃ J : MvPolynomial σ K, J ≠ 0 ∧ P * J ≠ 0 ∧
      (∀ z ∈ Z, ∀ d ∈ J.support, d z = 0) ∧
      weight (P * J) ≤ weight (P ^ p ^ e * E) := by
  classical
  obtain ⟨α, hα⟩ := exists_nonzero_residuePart (p ^ e) (P ^ p ^ e * E) hU
  obtain ⟨J, hJ, hPJ, hJs, hPJs⟩ := frobenius_extraction_residue p e P E α hα
  have hq : 0 < p ^ e := pow_pos (expChar_pos K p) e
  refine ⟨J, hJ, hPJ, ?_, ?_⟩
  · intro z hz d hd
    have he := hE z hz (α + scaleExponent (p ^ e) d) (hJs d hd)
    simp only [Finsupp.add_apply, scaleExponent_apply] at he
    have hprod : p ^ e * d z = 0 := by omega
    exact (Nat.mul_eq_zero.mp hprod).resolve_left (ne_of_gt hq)
  · have hinj : Function.Injective (fun d : σ →₀ ℕ => α + scaleExponent (p ^ e) d) :=
      (add_right_injective α).comp (scaleExponent_injective hq)
    have hs : (P * J).support.image (fun d => α + scaleExponent (p ^ e) d) ⊆
        (residuePart (p ^ e) (P ^ p ^ e * E) α).support := by
      intro d hd
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
      exact hPJs a ha
    have hc := Finset.card_le_card hs
    rw [Finset.card_image_of_injective _ hinj] at hc
    exact hc.trans (weight_residuePart_le _ _ _)

end WeightedPilz

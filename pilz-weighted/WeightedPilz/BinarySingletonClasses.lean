import WeightedPilz.BinaryResidueComparison
import WeightedPilz.ParityConvolution
import WeightedPilz.ShortFreshTest

/-! Singleton kernel classes survive every correction for a one-class input. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [Field K] [DecidableEq σ]
namespace FreshData

/-- Protected singleton classes give a direct lower bound on the chosen short
output when its binary input is concentrated in one full parity class. -/
theorem ResidueCapacityWitness.singleton_class_lower (S : FreshData σ K) {N : ℕ}
    (W : S.ResidueCapacityWitness 2 N) (hr : 1 ≤ S.vars.card)
    (β : σ →₀ ℕ) (hD : W.A 1 = residuePart 2 (W.A 1) β)
    (T : Finset (σ →₀ ℕ)) (hT : ∀α∈T, residueExponent 2 α = α)
    (hsingle : ∀α∈T, residueWeight 2 S.F α = 1) :
    T.card * weight (W.A 1) ≤ weight (S.F * W.H) := by
  classical
  let f := fun α : σ →₀ ℕ => residueExponent 2 (α + β)
  have hf : Set.InjOn f (T : Set (σ →₀ ℕ)) := by
    intro α hα γ hγ heq
    have h := residueExponent_add_right_cancel 2 α γ β heq
    rwa [hT α hα, hT γ hγ] at h
  have hCsub : S.C.support ⊆ S.F.support := by
    rw [S.support_F]
    exact Finset.subset_union_left
  have hclass : ∀α∈T, residueWeight 2 (S.F * W.H) (f α) = weight (W.A 1) := by
    intro α hα
    have hCF : weight (residuePart 2 S.C α) ≤ residueWeight 2 S.F α := by
      apply Finset.card_le_card
      intro d hd
      simp only [support_residuePart, Finset.mem_filter] at hd ⊢
      exact ⟨hCsub hd.1, hd.2⟩
    have hCwt : weight (residuePart 2 S.C α * W.A 1) ≤ weight (W.A 1) := by
      have hmul := weight_mul_le (residuePart 2 S.C α) (W.A 1)
      rw [hsingle α hα] at hCF
      nlinarith
    have hconvC := residuePart_mul_residuePart 2 S.C (W.A 1) α β (hT α hα)
    rw [← hD] at hconvC
    have hcap : residueWeight 2 (S.comparison 2 W.A) (f α) ≤ S.positiveResidueCost 2 W.A := by
      rw [S.comparison_two, residueWeight, hconvC, S.positiveResidueCost_two]
      exact hCwt.trans (Nat.le_mul_of_pos_left _ hr)
    have hU := W.protected_class (f α) hcap
    have hconvF := residuePart_mul_residuePart 2 S.F (W.A 1) α β (hT α hα)
    rw [← hD] at hconvF
    have hG : S.F * W.H = S.correction 2 W.A + S.F * W.A 1 := by
      have h := W.binary_remainder_eq S
      linear_combination h
    rw [residueWeight, hG, residuePart_add, hU, zero_add, hconvF, mul_comm]
    exact weight_mul_of_weight_one _ _ (hsingle α hα)
  have hsum := sum_residueWeights_le 2 (S.F * W.H) (T.image f)
  rw [Finset.sum_image hf] at hsum
  have heq : (∑α∈T, residueWeight 2 (S.F * W.H) (f α)) = T.card * weight (W.A 1) := by
    rw [Finset.sum_congr rfl hclass]
    simp
  rwa [heq] at hsum

end FreshData
end WeightedPilz

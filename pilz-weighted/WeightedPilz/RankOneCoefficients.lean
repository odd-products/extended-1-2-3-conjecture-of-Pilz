import WeightedPilz.CoefficientRank
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! Rank-one finite-support vectors are scalar finite-support vectors times
one nonzero vector, with exactly the same support. -/

noncomputable section
namespace WeightedPilz

open Submodule Module

variable {α K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_scalar_factor_of_coefficientRank_le_one (f : α →₀ V)
    (hf : f ≠ 0) (hrank : finrank K (coefficientSpan (K := K) f) ≤ 1) :
    ∃ v : V, v ≠ 0 ∧ ∃ h : α →₀ K,
      h ≠ 0 ∧ h.support = f.support ∧ ∀ a, f a = h a • v := by
  classical
  let W := coefficientSpan (K := K) f
  letI : FiniteDimensional K W := by
    dsimp [W]
    rw [coefficientSpan_eq_support_span]
    exact FiniteDimensional.span_of_finite K (f.support.finite_toSet.image f)
  obtain ⟨v, hv⟩ := (finrank_le_one_iff (K := K) (V := W)).mp hrank
  have hfmem (a : α) : f a ∈ W := subset_span ⟨a, rfl⟩
  have hvne : (v : V) ≠ 0 := by
    intro hz
    apply hf
    ext a
    obtain ⟨c, hc⟩ := hv ⟨f a, hfmem a⟩
    have heq := congrArg Subtype.val hc
    simpa only [Submodule.coe_smul_of_tower, hz, smul_zero, Finsupp.zero_apply] using heq.symm
  choose g hg using fun a => hv ⟨f a, hfmem a⟩
  have hgval (a : α) : g a • (v : V) = f a := congrArg Subtype.val (hg a)
  let h : α →₀ K := Finsupp.onFinset f.support g (by
    intro a ha
    apply Finsupp.mem_support_iff.mpr
    intro hfa
    have hz : g a • (v : V) = 0 := (hgval a).trans hfa
    exact ha ((smul_eq_zero.mp hz).resolve_right hvne))
  have hh (a : α) : h a = g a := rfl
  have heq (a : α) : f a = h a • (v : V) := (hgval a).symm
  have hsupp : h.support = f.support := by
    ext a
    simp only [Finsupp.mem_support_iff]
    rw [heq a]
    exact ⟨fun ha hz => ha ((smul_eq_zero.mp hz).resolve_right hvne),
      fun ha hz => ha (by rw [hz, zero_smul])⟩
  refine ⟨v, hvne, h, ?_, hsupp, heq⟩
  intro hhzero
  apply hf
  ext a
  simpa only [hhzero, Finsupp.zero_apply, zero_smul] using heq a

theorem exists_mapRange_factor_of_coefficientRank_le_one (f : α →₀ V)
    (hf : f ≠ 0) (hrank : finrank K (coefficientSpan (K := K) f) ≤ 1) :
    ∃ v : V, v ≠ 0 ∧ ∃ h : α →₀ K,
      h ≠ 0 ∧ h.support = f.support ∧
      f = Finsupp.mapRange (fun c : K => c • v) (zero_smul K v) h := by
  obtain ⟨v, hv, h, hh, hsupp, heq⟩ :=
    exists_scalar_factor_of_coefficientRank_le_one f hf hrank
  refine ⟨v, hv, h, hh, hsupp, ?_⟩
  ext a
  exact heq a

end WeightedPilz

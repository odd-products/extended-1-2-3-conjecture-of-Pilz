import WeightedPilz.Convolution
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The finite-support linear-algebra argument behind `thm:coefficient-rank`. -/
noncomputable section
namespace WeightedPilz
open Submodule Module
variable {α K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def coefficientSpan (f : α →₀ V) : Submodule K V := span K (Set.range f)

theorem coefficientSpan_eq_support_span (f : α →₀ V) :
    coefficientSpan (K := K) f = span K (f '' (f.support : Set α)) := by
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨a, rfl⟩
    by_cases ha : a ∈ f.support
    · exact subset_span ⟨a, ha, rfl⟩
    · simpa only [Finsupp.notMem_support_iff.mp ha] using
        (zero_mem (span K (f '' (f.support : Set α))))
  · exact span_mono (Set.image_subset_range _ _)

theorem coefficientRank_le_support (f : α →₀ V) :
    finrank K (coefficientSpan (K := K) f) ≤ f.support.card := by
  classical
  rw [coefficientSpan_eq_support_span]
  have heq : f '' (f.support : Set α) = (f.support.image f : Set V) := by simp
  rw [heq]
  exact (finrank_span_finset_le_card (R := K) (f.support.image f)).trans
    Finset.card_image_le

/-- The Singleton argument for a vector-valued finite support: killing any
`rank - 1` selected coefficients leaves a nonzero scalar projection. The
support hypothesis is the scalar bound to which this linear-algebra step applies. -/
theorem coefficientRank_projection_bound (f : α →₀ V) (hf : f ≠ 0) (N : ℕ)
    (hscalar : ∀ φ : V →ₗ[K] K,
      Finsupp.mapRange φ φ.map_zero f ≠ 0 →
      N ≤ (Finsupp.mapRange φ φ.map_zero f).support.card) :
    N + finrank K (coefficientSpan (K := K) f) ≤ f.support.card + 1 := by
  classical
  let ρ := finrank K (coefficientSpan (K := K) f)
  have hrank : ρ ≤ f.support.card := coefficientRank_le_support f
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq
    ((Nat.sub_le ρ 1).trans hrank)
  let W : Submodule K V := span K (f '' (s : Set α))
  have hWle : W ≤ coefficientSpan (K := K) f :=
    span_mono (Set.image_subset_range _ _)
  have hWrank : finrank K W ≤ ρ - 1 := by
    have heq : f '' (s : Set α) = (s.image f : Set V) := by simp
    change finrank K (span K (f '' (s : Set α))) ≤ _
    rw [heq]
    exact (finrank_span_finset_le_card (R := K) (s.image f)).trans
      (Finset.card_image_le.trans (le_of_eq hcard))
  have hex : ∃ a, f a ∉ W := by
    by_contra! h
    have hle : coefficientSpan (K := K) f ≤ W :=
      span_le.mpr (by rintro _ ⟨a, rfl⟩; exact h a)
    have heq := le_antisymm hle hWle
    have hz : ρ = 0 := by
      have : ρ ≤ ρ - 1 := by
        change finrank K (coefficientSpan (K := K) f) ≤ _
        rw [heq]
        exact hWrank
      omega
    have hs0 : s = ∅ := Finset.card_eq_zero.mp (by omega)
    have hW0 : W = ⊥ := by simp [W, hs0]
    apply hf
    ext a
    have := h a
    simpa [hW0] using this
  obtain ⟨a, ha⟩ := hex
  obtain ⟨φ, hφa, hφW⟩ := W.exists_dual_map_eq_bot_of_notMem ha inferInstance
  have hφs : ∀ b ∈ s, φ (f b) = 0 := by
    intro b hb
    have hm : f b ∈ W := subset_span ⟨b, hb, rfl⟩
    have him : φ (f b) ∈ W.map φ := mem_map.mpr ⟨f b, hm, rfl⟩
    simpa [hφW] using him
  have hproj : Finsupp.mapRange φ φ.map_zero f ≠ 0 := by
    intro hz
    have heq := congrArg (fun g : α →₀ K => g a) hz
    exact hφa (by simpa using heq)
  have hsub : (Finsupp.mapRange φ φ.map_zero f).support ⊆ f.support \ s := by
    intro b hb
    apply Finset.mem_sdiff.mpr
    refine ⟨Finsupp.support_mapRange hb, ?_⟩
    intro hbs
    have hne := Finsupp.mem_support_iff.mp hb
    exact hne (hφs b hbs)
  have hbound := (hscalar φ hproj).trans (Finset.card_le_card hsub)
  rw [Finset.card_sdiff_of_subset hs, hcard] at hbound
  omega

end WeightedPilz

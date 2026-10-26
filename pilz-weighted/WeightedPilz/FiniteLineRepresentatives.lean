import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Card

/-! Finite fiber representatives extending a prescribed transversal. -/

namespace WeightedPilz

/-- Choose one point in every occupied fiber, retaining all points in a prescribed
transversal. No ordering or algebraic structure on the ambient sets is needed. -/
theorem exists_finite_fiber_representatives {α β : Type*} [DecidableEq β]
    (S : Finset α) (q : α → β) (T : Finset α) (hT : T ⊆ S)
    (hq : Set.InjOn q (T : Set α)) :
    ∃ R : Finset α, R ⊆ S ∧ T ⊆ R ∧ Set.InjOn q (R : Set α) ∧
      R.image q = S.image q ∧ R.card = (S.image q).card := by
  classical
  have hsurj : Set.SurjOn q {a | a ∈ S ∧ q a ∉ T.image q}
      ((S.image q \ T.image q : Finset β) : Set β) := by
    intro b hb
    obtain ⟨hbS, hbT⟩ := Finset.mem_sdiff.mp hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hbS
    exact ⟨a, ⟨ha, hbT⟩, rfl⟩
  obtain ⟨U, hU, hUq, hUimage⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn
      {a | a ∈ S ∧ q a ∉ T.image q} (S.image q \ T.image q) hsurj
  have hRsub : T ∪ U ⊆ S := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hT ha
    · exact (hU ha).1
  have hRinj : Set.InjOn q ((T ∪ U : Finset α) : Set α) := by
    intro a ha b hb hab
    rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · exact hq ha hb hab
    · exact ((hU hb).2 (hab ▸ Finset.mem_image_of_mem q ha)).elim
    · exact ((hU ha).2 (hab.symm ▸ Finset.mem_image_of_mem q hb)).elim
    · exact hUq ha hb hab
  have hRimage : (T ∪ U).image q = S.image q := by
    apply Finset.Subset.antisymm
    · exact Finset.image_subset_image hRsub
    · intro b hb
      by_cases hbT : b ∈ T.image q
      · rw [Finset.image_union]
        exact Finset.mem_union_left _ hbT
      · have hbU : b ∈ U.image q := by
          rw [hUimage]
          exact Finset.mem_sdiff.mpr ⟨hb, hbT⟩
        rw [Finset.image_union]
        exact Finset.mem_union_right _ hbU
  refine ⟨T ∪ U, hRsub, Finset.subset_union_left, hRinj, hRimage, ?_⟩
  rw [← Finset.card_image_of_injOn hRinj, hRimage]

end WeightedPilz

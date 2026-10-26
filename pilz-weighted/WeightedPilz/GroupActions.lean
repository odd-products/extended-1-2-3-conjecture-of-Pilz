import WeightedPilz.ModuleConsequences
import Mathlib.Algebra.Ring.Subring.Basic

/-! Commuting additive-group actions reduce to scalar actions of the
commutative subring they generate. The all-field interval theorem is explicit.
-/

namespace WeightedPilz

universe u
variable {G : Type u} [AddCommGroup G]

theorem intervalEndBound_commuting_group_of_field_bounds (n : ℕ)
    (φ : ℕ → AddMonoid.End G)
    (hcomm : ∀ a, 1 ≤ a → a ≤ n → ∀ b, 1 ≤ b → b ≤ n →
      Function.Commute (φ a) (φ b))
    (hinj : ∀ a, 1 ≤ a → a ≤ n → Function.Injective (φ a))
    (hfield : ∀ (K : Type u) [Field K] (d : ℕ → K),
      NonzeroWeights n d → IntervalBound n d) : IntervalEndBound n φ := by
  classical
  let W : Set (AddMonoid.End G) := φ '' {a | 1 ≤ a ∧ a ≤ n}
  have hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    rintro x ⟨a, ⟨ha, han⟩, rfl⟩ y ⟨b, ⟨hb, hbn⟩, rfl⟩
    apply DFunLike.ext
    intro z
    exact hcomm a ha han b hb hbn z
  let A := Subring.closure W
  letI : CommRing A := Subring.closureCommRingOfComm hW
  letI : Module A G := {
    smul := fun a x => a.val x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_zero := fun a => a.val.map_zero
    smul_add := fun a x y => a.val.map_add x y
    add_smul := fun _ _ _ => rfl
    zero_smul := fun _ => rfl }
  let c : ℕ → A := fun a =>
    if ha : 1 ≤ a ∧ a ≤ n then
      ⟨φ a, Subring.subset_closure ⟨a, ha, rfl⟩⟩ else 0
  have hca (a : ℕ) (ha : 1 ≤ a) (han : a ≤ n) :
      scalarWeightEnd (M := G) (c a) = φ a := by
    apply DFunLike.ext
    intro x
    change (c a).val x = φ a x
    simp only [c, dif_pos (And.intro ha han)]
  have hc : ∀ a, 1 ≤ a → a ≤ n →
      ReflectsZero (scalarWeightEnd (M := G) (c a)) := by
    intro a ha han
    rw [hca a ha han]
    exact (reflectsZero_iff_injective (φ a)).mpr (hinj a ha han)
  have hscalar := intervalEndBound_reflectsZero_of_field_bounds n c hc hfield
  intro f hf
  have hb := hscalar f hf
  have heq : intervalEndAction n (fun a => scalarWeightEnd (c a)) f =
      intervalEndAction n φ f := by
    unfold intervalEndAction
    apply Finset.sum_congr rfl
    intro a ha
    have han := Finset.mem_range.mp ha
    apply congrArg (Finsupp.mapDomain (fun b => intervalIndex a * b))
    apply Finsupp.ext
    intro b
    exact DFunLike.congr_fun (hca (a + 1) (by omega) (by omega)) (f b)
  rwa [heq] at hb

/-- The exact commuting-group criterion, derived from the all-field theorem. -/
theorem intervalEndBound_commuting_group_iff_of_field_bounds (n : ℕ)
    (φ : ℕ → AddMonoid.End G)
    (hcomm : ∀ a, 1 ≤ a → a ≤ n → ∀ b, 1 ≤ b → b ≤ n →
      Function.Commute (φ a) (φ b))
    (hfield : ∀ (K : Type u) [Field K] (d : ℕ → K),
      NonzeroWeights n d → IntervalBound n d) :
    IntervalEndBound n φ ↔ ∀ a, 1 ≤ a → a ≤ n → Function.Injective (φ a) := by
  constructor
  · intro h a ha han
    exact (reflectsZero_iff_injective (φ a)).mp (reflectsZero_of_intervalEndBound h ha han)
  · intro hinj
    exact intervalEndBound_commuting_group_of_field_bounds n φ hcomm hinj hfield

end WeightedPilz

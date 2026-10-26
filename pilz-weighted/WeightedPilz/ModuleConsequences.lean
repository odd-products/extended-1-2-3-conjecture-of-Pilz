import WeightedPilz.IntervalModule
import WeightedPilz.ActionConvolution

/-!
The module-coefficient and erasure conclusions as consequences of the all-field
interval theorem. The field theorem is an explicit hypothesis here; it is
discharged unconditionally in `WeightedPilz.FinalConsequences`.
-/

namespace WeightedPilz

universe u v
variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [Module R M]

/-- Unit weights remain nonzero in every residue field, where the assumed field
interval theorem supplies the scalar support bound. -/
theorem residue_intervalEndBound_of_field_bounds (n : ℕ) (c : ℕ → R)
    (hc : ∀ a, 1 ≤ a → a ≤ n → IsUnit (c a))
    (hfield : ∀ (K : Type u) [Field K] (d : ℕ → K),
      NonzeroWeights n d → IntervalBound n d)
    (I : Ideal R) (hI : I.IsMaximal) :
    IntervalEndBound (M := R ⧸ I) n
      (fun a => scalarWeightEnd (Ideal.Quotient.mk I (c a))) := by
  letI : I.IsMaximal := hI
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  apply (intervalEndBound_scalar_iff_intervalBound n _).mpr
  apply hfield
  intro a ha
  obtain ⟨ha, han⟩ := Finset.mem_Icc.mp ha
  exact ((hc a ha han).map (Ideal.Quotient.mk I)).ne_zero

/-- The all-field interval theorem implies the module bound for unit weights. -/
theorem intervalEndBound_units_of_field_bounds (n : ℕ) (c : ℕ → R)
    (hc : ∀ a, 1 ≤ a → a ≤ n → IsUnit (c a))
    (hfield : ∀ (K : Type u) [Field K] (d : ℕ → K),
      NonzeroWeights n d → IntervalBound n d) :
    IntervalEndBound (M := M) n (fun a => scalarWeightEnd (c a)) :=
  intervalEndBound_of_residue_bounds n c
    (residue_intervalEndBound_of_field_bounds n c hc hfield)

/-- Localization reduces zero-reflecting scalar weights to unit weights. -/
theorem intervalEndBound_reflectsZero_of_field_bounds (n : ℕ) (c : ℕ → R)
    (hc : ∀ a, 1 ≤ a → a ≤ n → ReflectsZero (scalarWeightEnd (M := M) (c a)))
    (hfield : ∀ (K : Type u) [Field K] (d : ℕ → K),
      NonzeroWeights n d → IntervalBound n d) :
    IntervalEndBound (M := M) n (fun a => scalarWeightEnd (c a)) := by
  apply intervalEndBound_of_localization n c hc
  apply intervalEndBound_units_of_field_bounds n _ _ hfield
  intro a ha han
  exact isUnit_intervalWeight_localization n c ha han

/-- The precise scalar zero-reflection criterion, conditional only on the
all-field interval theorem. -/
theorem intervalEndBound_scalar_iff_reflectsZero_of_field_bounds (n : ℕ) (c : ℕ → R)
    (hfield : ∀ (K : Type u) [Field K] (d : ℕ → K),
      NonzeroWeights n d → IntervalBound n d) :
    IntervalEndBound (M := M) n (fun a => scalarWeightEnd (c a)) ↔
      ∀ a, 1 ≤ a → a ≤ n → ReflectsZero (scalarWeightEnd (M := M) (c a)) := by
  constructor
  · intro h a ha han
    exact reflectsZero_of_intervalEndBound h ha han
  · intro hc
    exact intervalEndBound_reflectsZero_of_field_bounds n c hc hfield

/-- The scalar module criterion in its usual injectivity formulation. -/
theorem intervalEndBound_scalar_iff_injective_of_field_bounds
    (n : ℕ) (c : ℕ → R)
    (hfield : ∀ (K : Type u) [Field K] (d : ℕ → K),
      NonzeroWeights n d → IntervalBound n d) :
    IntervalEndBound (M := M) n (fun a => scalarWeightEnd (c a)) ↔
      ∀ a, 1 ≤ a → a ≤ n → Function.Injective (fun x : M => c a • x) := by
  letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  rw [intervalEndBound_scalar_iff_reflectsZero_of_field_bounds n c hfield]
  simp only [reflectsZero_iff_injective]
  rfl

/-- The concrete interval erasure inverse for unit weights over every
commutative ring, assuming the all-field interval theorem. This includes the
ring of universal invertible weights and every unit specialization. -/
theorem intervalMatrix_units_erasure_inverse_of_field_bounds
    (n : ℕ) (c : ℕ → R) (hc : ∀ a, 1 ≤ a → a ≤ n → IsUnit (c a))
    (hfield : ∀ (K : Type u) [Field K] (d : ℕ → K),
      NonzeroWeights n d → IntervalBound n d)
    (S : Finset ℕ+) (E : Finset (intervalOutputSet n S)) (hE : E.card < n) :
    ∃ L : Matrix S {i : intervalOutputSet n S // i ∉ E} R,
      L * (intervalMatrix n c S (intervalOutputSet n S)).submatrix
        (fun (i : {i : intervalOutputSet n S // i ∉ E}) => i.val) id = 1 :=
  intervalMatrix_erasure_left_inverse n c
    (residue_intervalEndBound_of_field_bounds n c hc hfield) S E hE

end WeightedPilz

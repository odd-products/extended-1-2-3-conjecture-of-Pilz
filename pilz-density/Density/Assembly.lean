import Density.LowerBound
import Density.Scaling
import Density.SmallSets
import Density.Dyadic

/-! # The unconditional sharp density theorem

All hypotheses concern the input finite set. Density existence, normalization,
the induction, and the dyadic calculation are supplied by proved theorems.
-/

noncomputable section

namespace PilzDensity

theorem dyadic_lower_bound (A : Finset ℕ) (hne : A.Nonempty)
    (hpow : ∀ a ∈ A, ∃ k : ℕ, a = 2 ^ k) (hnot : ¬ Exceptional A) :
    (3 : ℝ) / 2 ≤ density A :=
  dyadic_lower_bound_of hasDensity density_scale density_pair_ge_three_halves
    density_triple_ge_three_halves A hne hpow hnot

theorem baseline_density (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (hne : A.Nonempty) : (1 : ℝ) ≤ density A :=
  baseline_lower_bound_of hasDensity exists_normalized density_singleton A hA hne

/-- Every nonexceptional positive finite set has actual density at least 4/3. -/
theorem sharp_density_bound (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (hne : A.Nonempty) (hnot : ¬ Exceptional A) : (4 : ℝ) / 3 ≤ density A :=
  sharp_lower_bound_of hasDensity exists_normalized density_singleton
    dyadic_lower_bound A hA hne hnot

theorem density_gap (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    Exceptional A ∨ (4 : ℝ) / 3 ≤ density A := by
  classical
  by_cases h : Exceptional A
  · exact Or.inl h
  · exact Or.inr (sharp_density_bound A hA hne h)

theorem sharp_density_limit (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (hne : A.Nonempty) (hnot : ¬ Exceptional A) :
    ∃ d : ℝ, HasDensity A d ∧ (4 : ℝ) / 3 ≤ d :=
  ⟨density A, hasDensity A hA, sharp_density_bound A hA hne hnot⟩

theorem density_eq_one_iff (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (hne : A.Nonempty) : density A = 1 ↔ Exceptional A := by
  constructor
  · intro hd
    by_contra h
    have := sharp_density_bound A hA hne h
    linarith
  · exact density_exceptional A

end PilzDensity

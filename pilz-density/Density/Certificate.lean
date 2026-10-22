import Density.Assembly

/-! Public statements of existence, the density gap, and optimality. -/

noncomputable section

namespace PilzDensity

/-- The complete companion theorem, with a rational actual limit. -/
theorem companion_theorem (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (hne : A.Nonempty) :
    ∃ q : ℚ, HasDensity A (q : ℝ) ∧
      ((q : ℝ) = 1 ↔ Exceptional A) ∧
      (¬ Exceptional A → (4 : ℝ) / 3 ≤ (q : ℝ)) := by
  obtain ⟨q, hq⟩ := density_rational A hA
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa only [← hq] using hasDensity A hA
  · simpa only [← hq] using density_eq_one_iff A hA hne
  · intro hnot
    simpa only [← hq] using sharp_density_bound A hA hne hnot

/-- No larger uniform constant works outside the two exceptional families. -/
theorem four_thirds_optimal (c : ℝ)
    (hc : ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) → A.Nonempty →
      ¬ Exceptional A → c ≤ density A) : c ≤ (4 : ℝ) / 3 := by
  have h := hc {1, 3} (by simp) (by simp) one_three_not_exceptional
  simpa only [density_one_three] using h

/-- The equality example is a limit of the actual ordered representation count. -/
theorem sharpness_limit : HasDensity {1, 3} ((4 : ℝ) / 3) := by
  simpa only [density_one_three] using hasDensity {1, 3} (by simp)

end PilzDensity

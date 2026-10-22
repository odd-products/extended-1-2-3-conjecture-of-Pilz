import Pilz.OddProduct
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Odd-product counts and their asymptotic density

The count is the original Pilz odd representation count, with positive interval
inputs. `HasDensity` refers to its actual limit along natural interval lengths.
-/

noncomputable section

namespace PilzDensity

/-- The number of integers represented oddly by `A × {1, ..., n}`. -/
def count (A : Finset ℕ) (n : ℕ) : ℕ :=
  (Pilz.oddProduct A (Finset.Icc 1 n)).card

/-- The actual asymptotic odd-product density, normalized by interval length. -/
def HasDensity (A : Finset ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun n : ℕ => (count A n : ℝ) / (n : ℝ))
    Filter.atTop (nhds d)

/-- The limit when it exists; zero otherwise. Existence is proved separately. -/
def density (A : Finset ℕ) : ℝ := by
  classical
  exact if h : ∃ d, HasDensity A d then Classical.choose h else 0

theorem hasDensity_of_exists {A : Finset ℕ} (h : ∃ d, HasDensity A d) :
    HasDensity A (density A) := by
  classical
  simp only [density, dif_pos h]
  exact Classical.choose_spec h

theorem HasDensity.eq_density {A : Finset ℕ} {d : ℝ} (h : HasDensity A d) :
    density A = d :=
  tendsto_nhds_unique (hasDensity_of_exists ⟨d, h⟩) h

/-- The two positive exceptional families. -/
def Exceptional (A : Finset ℕ) : Prop :=
  ∃ a : ℕ, 0 < a ∧ (A = {a} ∨ A = {a, 2 * a})

end PilzDensity


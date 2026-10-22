import Density.Basic
import Density.FloorLimits

/-!
# Analytic bridges for odd-product density

These theorems apply the generic quotient limits to the actual odd-product
count.  The finite floor formula is an explicit hypothesis of the bridge;
this module does not assume or assert that formula without a proof.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace PilzDensity

/-- Density is unique because it is the limit of the actual counting sequence. -/
theorem HasDensity.unique {A : Finset ℕ} {d e : ℝ}
    (hd : HasDensity A d) (he : HasDensity A e) : d = e :=
  tendsto_nhds_unique hd he

/-- Every odd-product density is nonnegative. -/
theorem HasDensity.nonneg {A : Finset ℕ} {d : ℝ}
    (hd : HasDensity A d) : 0 ≤ d := by
  exact ge_of_tendsto hd (Filter.Eventually.of_forall fun n => by positivity)

/-- Passing from interval length `n` to `n / Q` divides the density by `Q`. -/
theorem HasDensity.div_index {A : Finset ℕ} {d : ℝ}
    (hd : HasDensity A d) (Q : ℕ) (hQ : 0 < Q) :
    Tendsto (fun n : ℕ => (count A (n / Q) : ℝ) / (n : ℝ))
      atTop (𝓝 (d / (Q : ℝ))) :=
  tendsto_div_index hd Q hQ

/-- An exact finite floor formula for the actual count proves existence of
its density, with the explicitly evaluated finite sum as the value. -/
theorem hasDensity_of_floor_sum {ι : Type*} (A : Finset ℕ)
    (s : Finset ι) (c : ι → ℝ) (a b : ι → ℕ)
    (hformula : ∀ n : ℕ,
      (count A n : ℝ) = ∑ i ∈ s, c i * ((n * a i / b i : ℕ) : ℝ)) :
    HasDensity A (∑ i ∈ s, c i * ((a i : ℝ) / (b i : ℝ))) := by
  unfold HasDensity
  simp_rw [hformula]
  exact tendsto_finite_floor_sum s c a b

end PilzDensity


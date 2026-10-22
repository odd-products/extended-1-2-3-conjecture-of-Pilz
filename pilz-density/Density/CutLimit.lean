import Density.Cut
import Density.Analytic
import Mathlib.Tactic.Ring

/-!
# Passing the exact divisibility cut to actual densities

This module proves the cut inequality for any supplied actual limits.
It does not assume or assert general existence of these limits.
-/

noncomputable section

namespace PilzDensity

/-- The sharp lower-side overlap in the finite cut gives the same sharp
coefficient in the asymptotic inequality. -/
theorem HasDensity.exact_cut {B C : Finset ℕ} {a b c : ℝ}
    (hA : HasDensity (B ∪ C) a) (hBlim : HasDensity B b) (hClim : HasDensity C c)
    (Q : ℕ) (hQ : 0 < Q) (hBC : Disjoint B C)
    (hB : ∀ x ∈ B, Nat.Coprime Q x) (hC : ∀ x ∈ C, Q ∣ x) :
    (1 - 2 / (Q : ℝ)) * b + c ≤ a := by
  have hrescale := hBlim.div_index Q hQ
  have hleft := Filter.Tendsto.add hBlim hClim
  have hright := Filter.Tendsto.add hA
    (Filter.Tendsto.mul (tendsto_const_nhds (x := (2 : ℝ))) hrescale)
  have hlimit : b + c ≤ a + 2 * (b / (Q : ℝ)) := by
    apply le_of_tendsto_of_tendsto' hleft hright
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hfinite : (count B n : ℝ) + (count C n : ℝ) ≤
        (count (B ∪ C) n : ℝ) + 2 * (count B (n / Q) : ℝ) := by
      exact_mod_cast count_exact_cut B C n Q hQ hBC hB hC
    simpa only [add_div, mul_div_assoc] using div_le_div_of_nonneg_right hfinite hn
  calc
    (1 - 2 / (Q : ℝ)) * b + c = b + c - 2 * (b / (Q : ℝ)) := by ring
    _ ≤ a := sub_le_iff_le_add.mpr hlimit

end PilzDensity


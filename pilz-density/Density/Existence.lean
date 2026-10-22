import Density.Analytic
import Density.InclusionExclusion
import Density.Intersections

/-!
# Existence and the exact formula for odd-product density

The finite parity identity is applied to the actual arithmetic progressions
whose symmetric difference is `Pilz.oddProduct`. Thus convergence here has no
assumed counting formula or existence-of-limit hypothesis.
-/

noncomputable section
open scoped BigOperators

namespace PilzDensity

/-- The least member of a nonempty finite set, with a harmless empty value. -/
def minCoeff (J : Finset ℕ) : ℕ :=
  if h : J.Nonempty then J.min' h else 0

@[simp] theorem minCoeff_of_nonempty (J : Finset ℕ) (hJ : J.Nonempty) :
    minCoeff J = J.min' hJ := by simp [minCoeff, hJ]

/-- Inclusion-exclusion with its empty term cancelled. -/
theorem odd_card_nonempty_inclusion_exclusion {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (I : Finset ι) (U : Finset α) (S : ι → Finset α) :
    ((U.filter fun x => Odd (I.filter fun i => x ∈ S i).card).card : ℝ) =
      ∑ J ∈ I.powerset.erase ∅, (-2 : ℝ) ^ (J.card - 1) *
        ((U.filter fun x => ∀ j ∈ J, x ∈ S j).card : ℝ) := by
  classical
  have h := odd_card_inclusion_exclusion I U S
  rw [← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset I)] at h
  simp only [Finset.card_empty, pow_zero, one_mul,
    Finset.notMem_empty, false_implies, implies_true, Finset.filter_true] at h
  have hi : (2 : ℤ) *
      ((U.filter fun x => Odd (I.filter fun i => x ∈ S i).card).card : ℤ) =
      - ∑ J ∈ I.powerset.erase ∅, (-2 : ℤ) ^ J.card *
          ((U.filter fun x => ∀ j ∈ J, x ∈ S j).card : ℤ) := by linarith
  have hr : (2 : ℝ) *
      ((U.filter fun x => Odd (I.filter fun i => x ∈ S i).card).card : ℝ) =
      - ∑ J ∈ I.powerset.erase ∅, (-2 : ℝ) ^ J.card *
          ((U.filter fun x => ∀ j ∈ J, x ∈ S j).card : ℝ) := by
    exact_mod_cast hi
  have hs :
      (∑ J ∈ I.powerset.erase ∅, (-2 : ℝ) ^ J.card *
          ((U.filter fun x => ∀ j ∈ J, x ∈ S j).card : ℝ)) =
      -2 * ∑ J ∈ I.powerset.erase ∅, (-2 : ℝ) ^ (J.card - 1) *
          ((U.filter fun x => ∀ j ∈ J, x ∈ S j).card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    have hpos : 0 < J.card := Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hJ).1)
    have he : J.card = (J.card - 1) + 1 := by omega
    have hp : (-2 : ℝ) ^ J.card = (-2 : ℝ) ^ (J.card - 1) * (-2) := by
      conv_lhs => rw [he, pow_succ]
    rw [hp]
    ring
  rw [hs] at hr
  linarith

/-- The exact finite signed-floor formula for the original odd product. -/
theorem count_floor_formula (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (n : ℕ) :
    (count A n : ℝ) =
      ∑ J ∈ A.powerset.erase ∅, (-2 : ℝ) ^ (J.card - 1) *
        ((n * minCoeff J / J.lcm id : ℕ) : ℝ) := by
  classical
  unfold count Pilz.oddProduct
  simp_rw [representationCount_eq_filter_card A hA n]
  rw [odd_card_nonempty_inclusion_exclusion]
  apply Finset.sum_congr rfl
  intro J hJ
  have hne : J.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hJ).1
  have hJA : J ⊆ A := Finset.mem_powerset.mp (Finset.mem_erase.mp hJ).2
  rw [intersection_card A J n hA hJA hne, minCoeff_of_nonempty J hne]

/-- Convergence to the explicit finite rational expression. -/
theorem hasDensity_formula (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    HasDensity A
      (∑ J ∈ A.powerset.erase ∅, (-2 : ℝ) ^ (J.card - 1) *
        ((minCoeff J : ℝ) / ((J.lcm id : ℕ) : ℝ))) := by
  exact hasDensity_of_floor_sum A (A.powerset.erase ∅)
    (fun J => (-2 : ℝ) ^ (J.card - 1)) minCoeff (fun J => J.lcm id)
    (count_floor_formula A hA)

/-- Every finite set of positive integers has an actual odd-product density. -/
theorem hasDensity (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    HasDensity A (density A) :=
  hasDensity_of_exists ⟨_, hasDensity_formula A hA⟩

/-- The density is the elementary inclusion-exclusion expression. -/
theorem density_formula (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    density A =
      ∑ J ∈ A.powerset.erase ∅, (-2 : ℝ) ^ (J.card - 1) *
        ((minCoeff J : ℝ) / ((J.lcm id : ℕ) : ℝ)) :=
  (hasDensity_formula A hA).eq_density

/-- In particular, every such density is rational. -/
theorem density_rational (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    ∃ q : ℚ, density A = (q : ℝ) := by
  refine ⟨∑ J ∈ A.powerset.erase ∅, (-2 : ℚ) ^ (J.card - 1) *
      ((minCoeff J : ℚ) / ((J.lcm id : ℕ) : ℚ)), ?_⟩
  rw [density_formula A hA]
  push_cast
  rfl

end PilzDensity

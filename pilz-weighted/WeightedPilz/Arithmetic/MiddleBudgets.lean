import WeightedPilz.Arithmetic.Counts
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Choose.Basic

/-! The numerical columns and complete exception sets of the frozen middle
interval argument. Every closed finite statement is proved by kernel reduction.
No external table is an input to these declarations. -/

set_option Elab.async false

namespace WeightedPilz.Arithmetic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- All four numerical extrema in a row of equation (fin-block-budgets). -/
def BlockBudgetRow (a b x y z t : ℕ) : Prop :=
  ((Finset.Icc a b).image (fun n => endpoint n + 7 * freshCount n - n)).min = x ∧
  ((Finset.Icc a b).image (fun n => freshCount n * endpoint n - n)).min = y ∧
  ((Finset.Icc a b).image (fun n => (n - 1 - endpoint n) / squareCost n)).max = z ∧
  ((Finset.Icc a b).image uniqueThreshold).max = t

instance (a b x y z t : ℕ) : Decidable (BlockBudgetRow a b x y z t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem min_image_eq_of_bounds {α : Type*} [LinearOrder α] [DecidableEq α]
    {s : Finset ℕ} {f : ℕ → α} {m : α}
    (hl : ∀ n ∈ s, m ≤ f n) (he : ∃ n ∈ s, f n = m) :
    (s.image f).min = m := by
  apply le_antisymm
  · obtain ⟨n, hn, he⟩ := he
    exact Finset.min_le (Finset.mem_image.mpr ⟨n, hn, he⟩)
  · apply Finset.le_min
    intro a ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    exact WithTop.coe_le_coe.mpr (hl n hn)

theorem max_image_eq_of_bounds {α : Type*} [LinearOrder α] [DecidableEq α]
    {s : Finset ℕ} {f : ℕ → α} {m : α}
    (hl : ∀ n ∈ s, f n ≤ m) (he : ∃ n ∈ s, f n = m) :
    (s.image f).max = m := by
  apply le_antisymm
  · apply Finset.max_le
    intro a ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    exact WithBot.coe_le_coe.mpr (hl n hn)
  · obtain ⟨n, hn, he⟩ := he
    exact Finset.le_max (Finset.mem_image.mpr ⟨n, hn, he⟩)

/-- A linear-size certificate for the exact extrema, including attainment. -/
private def BlockBudgetBounds (a b x y z t : ℕ) : Prop :=
  (∀ n ∈ Finset.Icc a b,
    x ≤ endpoint n + 7 * freshCount n - n ∧
    y ≤ freshCount n * endpoint n - n ∧
    (n - 1 - endpoint n) / squareCost n ≤ z ∧ uniqueThreshold n ≤ t) ∧
  (∃ n ∈ Finset.Icc a b, endpoint n + 7 * freshCount n - n = x) ∧
  (∃ n ∈ Finset.Icc a b, freshCount n * endpoint n - n = y) ∧
  (∃ n ∈ Finset.Icc a b, (n - 1 - endpoint n) / squareCost n = z) ∧
  (∃ n ∈ Finset.Icc a b, uniqueThreshold n = t)

private theorem blockBudgetRow_of_bounds {a b x y z t : ℕ}
    (h : BlockBudgetBounds a b x y z t) : BlockBudgetRow a b x y z t := by
  obtain ⟨hb, hx, hy, hz, ht⟩ := h
  exact ⟨min_image_eq_of_bounds (fun n hn => (hb n hn).1) hx,
    min_image_eq_of_bounds (fun n hn => (hb n hn).2.1) hy,
    max_image_eq_of_bounds (fun n hn => (hb n hn).2.2.1) hz,
    max_image_eq_of_bounds (fun n hn => (hb n hn).2.2.2) ht⟩

theorem blockBudget_25_26 : BlockBudgetRow 25 26 6 7 2 60 := by
  apply blockBudgetRow_of_bounds; unfold BlockBudgetBounds; weighted_decide
theorem blockBudget_27 : BlockBudgetRow 27 27 5 6 2 84 := by
  apply blockBudgetRow_of_bounds; unfold BlockBudgetBounds; weighted_decide
theorem blockBudget_28 : BlockBudgetRow 28 28 5 8 2 88 := by
  apply blockBudgetRow_of_bounds; unfold BlockBudgetBounds; weighted_decide
theorem blockBudget_29_33 : BlockBudgetRow 29 33 10 18 1 42 := by
  apply blockBudgetRow_of_bounds; unfold BlockBudgetBounds; weighted_decide
theorem blockBudget_34_37 : BlockBudgetRow 34 37 8 26 1 82 := by
  apply blockBudgetRow_of_bounds; unfold BlockBudgetBounds; weighted_decide
theorem blockBudget_38_50 : BlockBudgetRow 38 50 7 34 2 94 := by
  apply blockBudgetRow_of_bounds; unfold BlockBudgetBounds; weighted_decide
theorem blockBudget_51_66 : BlockBudgetRow 51 66 8 63 1 129 := by
  apply blockBudgetRow_of_bounds; unfold BlockBudgetBounds; weighted_decide

/-- The seven persistent-product blocks cover exactly the middle range. -/
theorem middle_blocks_cover {n : ℕ} (h₁ : 25 ≤ n) (h₂ : n ≤ 66) :
    (25 ≤ n ∧ n ≤ 26) ∨ n = 27 ∨ n = 28 ∨
    (29 ≤ n ∧ n ≤ 33) ∨ (34 ≤ n ∧ n ≤ 37) ∨
    (38 ≤ n ∧ n ≤ 50) ∨ (51 ≤ n ∧ n ≤ 66) := by omega

private theorem middleBasicBudgets_checked :
    ∀ n ∈ Finset.Icc 25 66,
      n ≤ endpoint n + 7 * freshCount n ∧
      n < freshCount n * endpoint n ∧
      (n - 1 - endpoint n) / squareCost n ≤ 2 := by weighted_decide

theorem middleBasicBudgets {n : ℕ} (h₁ : 25 ≤ n) (h₂ : n ≤ 66) :
    n ≤ endpoint n + 7 * freshCount n ∧
    n < freshCount n * endpoint n ∧
    (n - 1 - endpoint n) / squareCost n ≤ 2 :=
  middleBasicBudgets_checked n (Finset.mem_Icc.mpr ⟨h₁, h₂⟩)

/-- Exactly the four indices permitting a two-term affine square coefficient. -/
theorem affine_two_term_exceptions :
    (Finset.Icc 25 66).filter (fun n => 2 ≤ (n - 1 - endpoint n) / squareCost n) =
      {26, 27, 28, 40} := by weighted_decide

/-- The four rows following the seven-block budget table. -/
theorem affine_two_term_data :
    (affineLinearBudget 26 2, squareCost 26) = (0, 6) ∧
    (affineLinearBudget 27 2, squareCost 27) = (1, 6) ∧
    (affineLinearBudget 28 2, squareCost 28) = (1, 6) ∧
    (affineLinearBudget 40 2, squareCost 40) = (0, 10) := by weighted_decide

/-- The output lower bounds with negative terms moved to the other side. -/
theorem affine_two_term_output_budgets :
    26 + (26 - 2 * freshCount 26) * affineLinearBudget 26 2 ≤ 16 + 2 * squareCost 26 ∧
    27 + (27 - 2 * freshCount 27) * affineLinearBudget 27 2 ≤ 44 + 2 * squareCost 27 ∧
    28 + (28 - 2 * freshCount 28) * affineLinearBudget 28 2 ≤ 44 + 2 * squareCost 28 ∧
    40 + (40 - 2 * freshCount 40) * affineLinearBudget 40 2 ≤ 20 + 2 * squareCost 40 := by weighted_decide

/-- Exact failures of the elementary cube-residue estimate for the square. -/
theorem cube_residue_naive_exceptions :
    (Finset.Icc 25 66).filter (fun n => (squareCost n + 1)^3 ≤ n^2) =
      {26, 27, 28, 38, 39, 40} := by weighted_decide

/-- Prime count and endpoint values at the two characteristic-three exceptions. -/
theorem exceptional_cube_data :
    (freshCount 27, squareCost 27, endpoint 27) = (3, 6, 11) ∧
    (freshCount 28, squareCost 28, endpoint 28) = (3, 6, 12) := by weighted_decide

/-- Aggregate cost used for characteristic zero and for degrees below the characteristic. -/
def aggregateCost (n j : ℕ) : ℕ := Nat.choose (freshCount n + j - 1) j

/-- Exactly the possible higher top degrees after reserving the constant row. -/
theorem higher_degree_exceptions :
    ((Finset.Icc 25 66) ×ˢ (Finset.Icc 3 6)).filter
      (fun nj => endpoint nj.1 + aggregateCost nj.1 nj.2 < nj.1) =
      {(26, 3), (27, 3), (27, 4), (28, 3), (28, 4), (40, 3)} := by weighted_decide

private theorem higherResidueBudgets_checked :
    ∀ n ∈ Finset.Icc 25 66,
      n ≤ aggregateCost n 6 ∧
      ∀ j ∈ Finset.Icc 1 5, aggregateCost n j < n →
        n^j ≤ aggregateCost n j ^ (if j ≤ 4 then 5 else 7) := by weighted_decide

/-- Equation (fin-higher-residue), using only exact integer powers. -/
theorem higherResidueBudgets {n : ℕ} (h₁ : 25 ≤ n) (h₂ : n ≤ 66) :
    n ≤ aggregateCost n 6 ∧
    ∀ j ∈ Finset.Icc 1 5, aggregateCost n j < n →
      n^j ≤ aggregateCost n j ^ (if j ≤ 4 then 5 else 7) :=
  higherResidueBudgets_checked n (Finset.mem_Icc.mpr ⟨h₁, h₂⟩)

end WeightedPilz.Arithmetic




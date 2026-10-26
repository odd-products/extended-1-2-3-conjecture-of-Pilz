import WeightedPilz.Arithmetic.MiddleBudgets
import WeightedPilz.Arithmetic.UniqueProducts

/-! The seven independently computed persistent-product sets imply the
unique-product threshold for every middle index, including all endpoints. -/

set_option Elab.async false

namespace WeightedPilz.Arithmetic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem middle_natural_budgets_checked :
    ∀ n ∈ Finset.Icc 25 66, 2 * freshCount n ≤ n ∧ squareCost n ≤ n := by
  weighted_decide

/-- The subtraction conventions in the natural-number affine budgets are exact. -/
theorem middle_natural_budgets {n : ℕ} (hn : 25 ≤ n) (hn' : n ≤ 66) :
    2 * freshCount n ≤ n ∧ squareCost n ≤ n :=
  middle_natural_budgets_checked n (Finset.mem_Icc.mpr ⟨hn, hn'⟩)

private theorem unique_threshold_of_row {a b n x y z t l : ℕ}
    (ha : a ≤ n) (hb : n ≤ b) (hrow : BlockBudgetRow a b x y z t)
    (hell : ell a b = l) (htl : t ≤ l) :
    uniqueThreshold n ≤ (uniqueProducts n).card := by
  have hmax := hrow.2.2.2
  have hT : uniqueThreshold n ≤ t :=
    Finset.le_max_of_eq
      (Finset.mem_image.mpr ⟨n, Finset.mem_Icc.mpr ⟨ha, hb⟩, rfl⟩) hmax
  calc
    uniqueThreshold n ≤ t := hT
    _ ≤ l := htl
    _ = ell a b := hell.symm
    _ ≤ (uniqueProducts n).card := ell_le_uniqueProducts_card ha hb

/-- The final two columns of equation (fin-block-budgets), with coverage proved. -/
theorem middle_unique_threshold {n : ℕ} (hn : 25 ≤ n) (hn' : n ≤ 66) :
    uniqueThreshold n ≤ (uniqueProducts n).card := by
  rcases middle_blocks_cover hn hn' with h | h | h | h | h | h | h
  · exact unique_threshold_of_row h.1 h.2 blockBudget_25_26 ell_25_26 (by decide)
  · subst n
    exact unique_threshold_of_row (by decide) (by decide) blockBudget_27 ell_27_27 (by decide)
  · subst n
    exact unique_threshold_of_row (by decide) (by decide) blockBudget_28 ell_28_28 (by decide)
  · exact unique_threshold_of_row h.1 h.2 blockBudget_29_33 ell_29_33 (by decide)
  · exact unique_threshold_of_row h.1 h.2 blockBudget_34_37 ell_34_37 (by decide)
  · exact unique_threshold_of_row h.1 h.2 blockBudget_38_50 ell_38_50 (by decide)
  · exact unique_threshold_of_row h.1 h.2 blockBudget_51_66 ell_51_66 (by decide)

/-- The unique-product inequality with its sole negative term moved to the right. -/
theorem middle_unique_product_budget {n : ℕ} (hn : 25 ≤ n) (hn' : n ≤ 66) :
    n + (n - 2 * freshCount n) * affineLinearBudget n 1 ≤
      (uniqueProducts n).card + squareCost n := by
  have hT := middle_unique_threshold hn hn'
  have hR := (middle_natural_budgets hn hn').2
  unfold uniqueThreshold at hT
  omega

end WeightedPilz.Arithmetic


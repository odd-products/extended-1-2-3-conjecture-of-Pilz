import WeightedPilz.Arithmetic.ParityBudgets

/-! Literal exact extrema and pair-size multisets in the binary tables. -/

set_option Elab.async false

namespace WeightedPilz.Arithmetic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def binaryFiveMargin (n : ℕ) : ℤ := binaryKappa n + 5 * (freshCount n : ℤ) - n

theorem binary_margin_25_26 :
    ((Finset.Icc 25 26).image binaryFiveMargin).min = (3 : ℤ) := by
  apply min_image_eq_of_bounds
  · unfold binaryFiveMargin; weighted_decide
  · unfold binaryFiveMargin; weighted_decide
theorem binary_margin_27_33 :
    ((Finset.Icc 27 33).image binaryFiveMargin).min = (1 : ℤ) := by
  apply min_image_eq_of_bounds
  · unfold binaryFiveMargin; weighted_decide
  · unfold binaryFiveMargin; weighted_decide
theorem binary_margin_34_40 :
    ((Finset.Icc 34 40).image binaryFiveMargin).min = (1 : ℤ) := by
  apply min_image_eq_of_bounds
  · unfold binaryFiveMargin; weighted_decide
  · unfold binaryFiveMargin; weighted_decide
theorem binary_margin_41_48 :
    ((Finset.Icc 41 48).image binaryFiveMargin).min = (4 : ℤ) := by
  apply min_image_eq_of_bounds
  · unfold binaryFiveMargin; weighted_decide
  · unfold binaryFiveMargin; weighted_decide
theorem binary_margin_49_57 :
    ((Finset.Icc 49 57).image binaryFiveMargin).min = (1 : ℤ) := by
  apply min_image_eq_of_bounds
  · unfold binaryFiveMargin; weighted_decide
  · unfold binaryFiveMargin; weighted_decide
theorem binary_margin_58 : binaryFiveMargin 58 = -1 := by unfold binaryFiveMargin; weighted_decide
theorem binary_margin_59_66 :
    ((Finset.Icc 59 66).image binaryFiveMargin).min = (0 : ℤ) := by
  apply min_image_eq_of_bounds
  · unfold binaryFiveMargin; weighted_decide
  · unfold binaryFiveMargin; weighted_decide

def parityCapacities (n : ℕ) : ℕ × ℕ :=
  (3 * Nat.sqrt n + Nat.sqrt (n / 2), 2 * Nat.sqrt n + 2 * Nat.sqrt (n / 2))

theorem parity_capacities_27_28 :
    parityCapacities 27 = (18, 16) ∧ parityCapacities 28 = (18, 16) := by unfold parityCapacities; weighted_decide
theorem parity_capacities_34_35 :
    parityCapacities 34 = (19, 18) ∧ parityCapacities 35 = (19, 18) := by unfold parityCapacities; weighted_decide
theorem parity_capacities_36_40 :
    ∀ n ∈ ({36, 38, 39, 40} : Finset ℕ), parityCapacities n = (22, 20) := by unfold parityCapacities; weighted_decide
theorem parity_capacities_49_51 :
    ∀ n ∈ Finset.Icc 49 51, (parityCapacities n).1 ≤ 26 ∧ (parityCapacities n).2 ≤ 24 := by
  unfold parityCapacities
  weighted_decide

/-- Pair sizes include multiplicity: distinct odd squarefree parts can have equal sizes. -/
def parityTwoPairs (n : ℕ) : Multiset (ℕ × ℕ) :=
  (oddSquarefreeNumbers n).val.map
    (fun s => (Nat.sqrt (n / (2 * s)), Nat.sqrt (n / s)))

theorem parityTwoPairs_27 :
    parityTwoPairs 27 =
      (([(3, 5), (2, 3), (1, 2), (1, 1), (1, 1), (1, 1),
          (0, 1), (0, 1), (0, 1), (0, 1), (0, 1)] : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
  unfold parityTwoPairs
  weighted_decide

theorem parityTwoPairs_28 :
    parityTwoPairs 28 =
      (([(3, 5), (2, 3), (1, 2), (1, 2), (1, 1), (1, 1),
          (0, 1), (0, 1), (0, 1), (0, 1), (0, 1)] : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
  unfold parityTwoPairs
  weighted_decide

theorem parityTwoPairs_36 :
    parityTwoPairs 36 =
      (([(4, 6), (2, 3), (1, 2), (1, 2), (1, 1), (1, 1), (1, 1), (1, 1),
          (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1)] : List (ℕ × ℕ)) :
        Multiset (ℕ × ℕ)) := by
  unfold parityTwoPairs
  weighted_decide

end WeightedPilz.Arithmetic





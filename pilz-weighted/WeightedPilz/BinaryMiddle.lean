import WeightedPilz.BinaryMiddleEngine
import WeightedPilz.BinaryFourComparison

/-! The characteristic-two weighted interval theorem on the finite middle range. -/
namespace WeightedPilz
variable {K : Type*} [Field K] [CharP K 2]

theorem intervalBound_middle_charTwo (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn25 : 25 ≤ n) (hn66 : n ≤ 66) : IntervalBound n c :=
  intervalBound_middle_charTwo_of_capacities n c hc hn25 hn66
    (middle_binary_core_distance n c hc hn25 hn66)
    (fun H hH hu hclasses hex => binary_four_exception_capacity n c H hc hH hu hclasses hex)

end WeightedPilz

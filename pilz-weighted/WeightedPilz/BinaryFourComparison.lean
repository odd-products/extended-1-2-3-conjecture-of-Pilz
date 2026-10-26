import WeightedPilz.BinaryFourCapacity
import WeightedPilz.BinaryCore

/-! The exceptional four-term capacity bound with all smooth-core inputs proved. -/
noncomputable section
namespace WeightedPilz
variable {K : Type*} [Field K] [CharP K 2]

theorem binary_four_exception_capacity (n : ℕ) (c : ℕ → K) (H : Poly K)
    (hc : NonzeroWeights n c) (hH : H ≠ 0) (hu : weight H = 4)
    (hclasses : 2 ≤ (residueIndices 2 H).card)
    (hex : n ∈ ({27,28,34,35,36,38,39,40,49,50,51} : Finset ℕ)) :
    ∃ M : ℕ, (∀α, residueWeight 2 (intervalCore n c * H) α ≤ M) ∧
      2 * M ≤ n + 4 * Arithmetic.freshCount n ∧
      2 * M ≤ weight (interval n c * H) :=
  binary_four_exception_capacity_of_smooth n c H hc hH hu
    (fun hlo hhi => middle_binary_five_smooth_distance n c hc hlo hhi) hclasses hex

end WeightedPilz
import WeightedPilz.InitialNine
import WeightedPilz.InitialTenFinal
import WeightedPilz.InitialFourteen
import WeightedPilz.InitialSixteen
import WeightedPilz.InitialLateFinal

/-! All weighted initial intervals through twenty-four, over an arbitrary field. -/

noncomputable section
namespace WeightedPilz
variable {K : Type*} [Field K]

theorem intervalBound_initial (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c)
    (hn24 : n ≤ 24) : IntervalBound n c := by
  by_cases hn9 : n ≤ 9
  · exact intervalBound_le_nine n hn9 c hc
  by_cases hn18 : 18 ≤ n
  · exact intervalBound_eighteen_to_twentyFour n hn18 hn24 c hc
  have hn10 : 10 ≤ n := by omega
  have hn17 : n ≤ 17 := by omega
  interval_cases n
  · exact intervalBound_ten c hc
  · exact intervalBound_eleven c hc
  · exact intervalBound_twelve c hc
  · exact intervalBound_thirteen c hc
  · exact intervalBound_fourteen c hc
  · exact intervalBound_fifteen c hc
  · exact intervalBound_sixteen c hc
  · exact intervalBound_seventeen c hc

theorem distance_interval_initial (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c)
    (hn24 : n ≤ 24) : distance (interval n c) = n := by
  apply Nat.le_antisymm
  · simpa only [weight_interval n c hc] using distance_le_weight (interval n c)
  · exact (le_distance_iff _ n).mpr (intervalBound_initial n c hc hn24)

end WeightedPilz

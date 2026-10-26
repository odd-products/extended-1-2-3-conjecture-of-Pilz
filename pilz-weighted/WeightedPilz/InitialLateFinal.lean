import WeightedPilz.InitialLateIntervals
import WeightedPilz.InitialLateCoreBounds

/-! The last seven initial intervals, using the proved weighted core bounds. -/

noncomputable section
namespace WeightedPilz
variable {K : Type*} [Field K]

private theorem restrict_late_weights {m n : ℕ} (hmn : m ≤ n) (c : ℕ → K)
    (hc : NonzeroWeights n c) : NonzeroWeights m c := by
  intro a ha
  exact hc a (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1,
    (Finset.mem_Icc.mp ha).2.trans hmn⟩)

/-- The frozen initial interval theorem for every `18 ≤ n ≤ 24`, over every
field and for arbitrary nonzero weights. -/
theorem intervalBound_eighteen_to_twentyFour (n : ℕ) (hn : 18 ≤ n) (hn' : n ≤ 24)
    (c : ℕ → K) (hc : NonzeroWeights n c) : IntervalBound n c := by
  interval_cases n
  · apply intervalBound_initial_late_of_core 18 (by omega) c hc
    simpa [initialLateCoreLowerBound] using intervalCore_18_distance_lower c hc
  · apply intervalBound_nineteen_of_core c hc
    exact intervalCore_18_distance_lower c (restrict_late_weights (by decide) c hc)
  · exact intervalBound_twenty_of_core c hc (intervalCore_20_distance_lower c hc)
  · apply intervalBound_initial_late_of_core 21 (by omega) c hc
    simpa [initialLateCoreLowerBound] using intervalCore_21_distance_lower c hc
  · apply intervalBound_initial_late_of_core 22 (by omega) c hc
    simpa [initialLateCoreLowerBound] using intervalCore_22_distance_lower c hc
  · apply intervalBound_twentyThree_of_core c hc
    exact intervalCore_22_distance_lower c (restrict_late_weights (by decide) c hc)
  · apply intervalBound_initial_late_of_core 24 (by omega) c hc
    simpa [initialLateCoreLowerBound] using intervalCore_24_distance_lower c hc

end WeightedPilz

import Pilz.RepeatedLinearCore
import Pilz.SmallCoreParameters
import Pilz.SmallCoreLowTable
import Pilz.SmallCoreHighTable
import Pilz.SmallBTable

/-! The uniform distance lower bound for the small-interval cores. -/

namespace Pilz

theorem coreKappa_distance_lower (n : ℕ) (hn11 : 11 ≤ n) (hn66 : n ≤ 66) :
    coreKappa n ≤ distance (core n) := by
  by_cases hn26 : n ≤ 26
  · exact coreKappa_distance_lower_low n hn11 hn26
  · apply coreKappa_distance_lower_high_of_base n (by omega) hn66
    change smallBKappa n ≤ distance (smallB n)
    exact smallB_distance_lower n (by omega) hn66

end Pilz

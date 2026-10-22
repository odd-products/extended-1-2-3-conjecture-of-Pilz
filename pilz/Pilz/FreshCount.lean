import Pilz.ChebyshevConclusion
import Pilz.FiniteChecks

/-! Proposition 5.1's fresh-prime bound, combining the manuscript's finite
certificates with its elementary Chebyshev argument. -/

namespace Pilz

theorem freshPrimeCountBound (n : ℕ) (hn : 67 ≤ n) : Nat.sqrt n ≤ freshCount n := by
  by_cases hsmall : n ≤ 1023
  · exact (finitePrimeBounds_67_1023 hn hsmall).1
  · exact (Chebyshev.nat_sqrt_lt_freshCount (by omega : 1024 ≤ n)).le

theorem eight_le_freshCount (n : ℕ) (hn : 67 ≤ n) : 8 ≤ freshCount n := by
  by_cases hsmall : n ≤ 1023
  · exact (finitePrimeBounds_67_1023 hn hsmall).2.1
  · have hroot : 8 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
    exact hroot.trans (freshPrimeCountBound n hn)

end Pilz

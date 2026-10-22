import Pilz.LocalizedExpansion
import Pilz.ChebyshevConclusion

/-! The localized-support theorem with the Chebyshev count input discharged. -/

namespace Pilz

theorem localizedExpansionAt (n : ℕ) (hn : 67 ≤ n) : LocalizedExpansionAt n :=
  localizedExpansionAt_of_freshLogLowerBound Chebyshev.freshLogLowerBound n hn

end Pilz

import Pilz.Statements
import Pilz.Support
import Pilz.Preparation
import Pilz.IntervalElimination
import Pilz.FreshCount
import Pilz.LocalizedConclusion

/-! The fresh-prime, directed-cut, and localized-expansion branch for n ≥ 67. -/

namespace Pilz

/-- The paper's directed-cut prime restriction. -/
theorem directedCutAt (n : ℕ) : DirectedCutAt n := by
  intro D q _hD hshort hnorm hminimal hmax
  exact deletionMinimal_prime_bound n q D hmax.1 (hnorm q) hmax.2.1 hminimal hshort

/-- The large-length branch of the paper. -/
theorem conjectureAt_large (n : ℕ) (hn : 67 ≤ n) : ConjectureAt n := by
  intro H hH
  by_contra hnot
  have hshort : weight (interval n * H) < n := by omega
  obtain ⟨E, hE, hEshort, hEbound⟩ :=
    intervalFreshElimination n (by omega) (freshPrimeCountBound n hn) H hH hshort
  obtain ⟨D, q, hD, hDshort, hDbound, hDnorm, hDminimal, hDlargest⟩ :=
    counterexamplePreparation n E hE hEshort hEbound
  have hcut := directedCutAt n D q hD hDshort hDnorm hDminimal hDlargest
  have hqbound : q ≤ n / 2 := (hDbound q hDlargest.2.1).2
  have hlower := localizedExpansionAt n hn D q hD hDnorm hDlargest hqbound hcut
  omega

end Pilz

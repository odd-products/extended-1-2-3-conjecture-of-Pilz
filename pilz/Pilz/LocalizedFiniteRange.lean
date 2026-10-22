import Pilz.LocalizedFinite
import Pilz.FiniteChecks

/-! The exact finite prime-count certificate supplies both numerical hypotheses
of the prime-budget argument for `67 <= n <= 1023`. -/

noncomputable section

namespace Pilz

theorem localized_expansion_finite_largePrime (n q : ℕ) (D : Poly)
    (hn : 67 ≤ n) (hn' : n ≤ 1023)
    (hq : 17 ≤ q) (hqn : q ≤ n / 2) (hcut : q < 2 * (weight D - 1))
    (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    n ≤ weight (interval n * D) := by
  have hcert := finitePrimeBounds_67_1023 hn hn'
  exact localized_expansion_of_primeBudget n q D hq hqn hcut
    hcert.2.1 hcert.2.2 hD hnorm hlargest

end Pilz

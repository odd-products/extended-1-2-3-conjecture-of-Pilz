import Pilz.LocalizedFiniteRange
import Pilz.LocalizedReduction
import Pilz.LocalizedBands
import Pilz.LocalizedMiddle
import Pilz.LocalizedLargePrime
import Pilz.SieveDensity
import Pilz.FreshLargeReal
import Pilz.LocalizedSmallQ
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-! The three ranges of the paper's localized expansion theorem. The
Chebyshev fresh-log estimate is the sole arithmetic input; its unconditional
construction is provided separately by the Chebyshev modules. -/

noncomputable section

namespace Pilz

private theorem prime_above_thirteen_ge_seventeen {q : ℕ} (hp : Nat.Prime q)
    (hq : ¬q ≤ 13) : 17 ≤ q := by
  by_contra hn
  have hlo : 14 ≤ q := by omega
  have hhi : q ≤ 16 := by omega
  interval_cases q <;> norm_num at hp

private theorem prime_above_fiftythree_ge_fiftynine {q : ℕ} (hp : Nat.Prime q)
    (hq : ¬q ≤ 53) : 59 ≤ q := by
  by_contra hn
  have hlo : 54 ≤ q := by omega
  have hhi : q ≤ 58 := by omega
  interval_cases q <;> norm_num at hp

private theorem prime_above_twoseventyone_ge_twoseventyseven {q : ℕ}
    (hp : Nat.Prime q) (hq : ¬q ≤ 271) : 277 ≤ q := by
  by_contra hn
  have hlo : 272 ≤ q := by omega
  have hhi : q ≤ 276 := by omega
  interval_cases q <;> norm_num at hp

theorem localizedExpansionAt_of_freshLogLowerBound
    (rlog : Chebyshev.FreshLogLowerBound) (n : ℕ) (hn : 67 ≤ n) :
    LocalizedExpansionAt n := by
  intro D q hD hnorm hlargest hqn hcut
  by_cases hsmall : q ≤ 13
  · exact localized_prime_le_thirteen n q D hn hD hnorm hlargest hcut hsmall
  have hq17 := prime_above_thirteen_ge_seventeen hlargest.1 hsmall
  by_cases hfinite : n ≤ 1023
  · exact localized_expansion_finite_largePrime n q D hn hfinite hq17 hqn hcut hD hnorm hlargest
  have hn1024 : 1024 ≤ n := by omega
  by_contra hnot
  have hshort : weight (interval n * D) < n := by omega
  by_cases hq53 : q ≤ 53
  · have hh := localized_expansion_five_bands n q D hn1024 hq17 hq53 hcut hD hnorm hlargest
    have hshortR : (weight (interval n * D) : ℝ) < n := by exact_mod_cast hshort
    linarith
  by_cases hmedium : n ≤ 32768
  · have hr := Chebyshev.freshCount_gt_div_thirty_of_rlog rlog hn1024 hmedium
    have hu := weight_lt_thirty_of_short n q D hqn hlargest hshort hr
    have hq59 := prime_above_fiftythree_ge_fiftynine hlargest.1 hq53
    omega
  have hnlarge : 32768 ≤ n := by omega
  have hr := Chebyshev.freshCount_gt_log_of_rlog rlog hnlarge
  have huL := weight_lt_log_of_short n q D (by omega) hqn hlargest hshort hr
  by_cases hq271 : q ≤ 271
  · have hq59 := prime_above_fiftythree_ge_fiftynine hlargest.1 hq53
    have hh := localized_expansion_middle n q D hnlarge hq59 hq271 hcut hD hnorm hlargest
    have hshortR : (weight (interval n * D) : ℝ) < n := by exact_mod_cast hshort
    linarith
  · have hq277 := prime_above_twoseventyone_ge_twoseventyseven hlargest.1 hq271
    have hh := localized_expansion_large_support n q D hnlarge hq277 huL hcut hlargest
    have hshortR : (weight (interval n * D) : ℝ) < n := by exact_mod_cast hshort
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith

end Pilz

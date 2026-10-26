import WeightedPilz.BinaryComparisonTables
import WeightedPilz.ComparisonLifting

/-! Binary comparison-table bounds for multipliers with arbitrary extra variables. -/
noncomputable section
namespace WeightedPilz
variable {K : Type*} [Field K]

theorem binary_comparison_25_all (c : ℕ → K) (H : Poly K)
    (hc : NonzeroWeights 25 c) (hH : H ≠ 0) (hu : weight H = 3) :
    28 ≤ weight (interval 25 c * H) := by
  apply prime_comparison_lifting 25 c 3 28 hc (by omega) (by omega)
    (by omega) (by omega) (by omega) ?_ H hH hu
  intro D q hD hnorm hlargest hweight
  exact binary_comparison_25 q c D hc hD hnorm hlargest hweight

theorem binary_comparison_27_28_all (n : ℕ) (c : ℕ → K) (H : Poly K)
    (hc : NonzeroWeights n c) (hn : 27 ≤ n) (hn' : n ≤ 28)
    (hH : H ≠ 0) (hu : weight H = 4)
    (hcore : 6 ≤ distance (smoothInterval (Pilz.primesUpTo 5) n c)) :
    32 ≤ weight (interval n c * H) := by
  apply prime_comparison_lifting n c 4 32 hc (by omega) (by omega)
    (by omega) (by omega) (by omega) ?_ H hH hu
  intro D q hD hnorm hlargest hweight
  exact binary_comparison_27_28 n q c D hc hn hn' hD hnorm hlargest hweight hcore

theorem binary_comparison_34_35_all (n : ℕ) (c : ℕ → K) (H : Poly K)
    (hc : NonzeroWeights n c) (hn : 34 ≤ n) (hn' : n ≤ 35)
    (hH : H ≠ 0) (hu : weight H = 4)
    (hcore : 6 ≤ distance (smoothInterval (Pilz.primesUpTo 5) n c)) :
    40 ≤ weight (interval n c * H) := by
  apply prime_comparison_lifting n c 4 40 hc (by omega) (by omega)
    (by omega) (by omega) (by omega) ?_ H hH hu
  intro D q hD hnorm hlargest hweight
  exact binary_comparison_34_35 n q c D hc hn hn' hD hnorm hlargest hweight hcore

theorem binary_comparison_36_all (c : ℕ → K) (H : Poly K)
    (hc : NonzeroWeights 36 c) (hH : H ≠ 0) (hu : weight H = 4)
    (hcore : 6 ≤ distance (smoothInterval (Pilz.primesUpTo 5) 36 c)) :
    40 ≤ weight (interval 36 c * H) := by
  apply prime_comparison_lifting 36 c 4 40 hc (by omega) (by omega)
    (by omega) (by omega) (by omega) ?_ H hH hu
  intro D q hD hnorm hlargest hweight
  exact binary_comparison_36 q c D hc hD hnorm hlargest hweight hcore

theorem binary_comparison_38_all (c : ℕ → K) (H : Poly K)
    (hc : NonzeroWeights 38 c) (hH : H ≠ 0) (hu : weight H = 4)
    (hcore : 6 ≤ distance (smoothInterval (Pilz.primesUpTo 5) 38 c)) :
    44 ≤ weight (interval 38 c * H) := by
  apply prime_comparison_lifting 38 c 4 44 hc (by omega) (by omega)
    (by omega) (by omega) (by omega) ?_ H hH hu
  intro D q hD hnorm hlargest hweight
  exact binary_comparison_38 q c D hc hD hnorm hlargest hweight hcore

theorem binary_comparison_39_40_all (n : ℕ) (c : ℕ → K) (H : Poly K)
    (hc : NonzeroWeights n c) (hn : 39 ≤ n) (hn' : n ≤ 40)
    (hH : H ≠ 0) (hu : weight H = 4)
    (hcore : 6 ≤ distance (smoothInterval (Pilz.primesUpTo 5) n c)) :
    46 ≤ weight (interval n c * H) := by
  apply prime_comparison_lifting n c 4 46 hc (by omega) (by omega)
    (by omega) (by omega) (by omega) ?_ H hH hu
  intro D q hD hnorm hlargest hweight
  exact binary_comparison_39_40 n q c D hc hn hn' hD hnorm hlargest hweight hcore

theorem binary_comparison_49_51_all (n : ℕ) (c : ℕ → K) (H : Poly K)
    (hc : NonzeroWeights n c) (hn : 49 ≤ n) (hn' : n ≤ 51)
    (hH : H ≠ 0) (hu : weight H = 4) :
    56 ≤ weight (interval n c * H) := by
  apply prime_comparison_lifting n c 4 56 hc (by omega) (by omega)
    (by omega) (by omega) (by omega) ?_ H hH hu
  intro D q hD hnorm hlargest hweight
  exact binary_comparison_49_51 n q c D hc hn hn' hD hnorm hlargest hweight

theorem binary_comparison_58_all (c : ℕ → K) (H : Poly K)
    (hc : NonzeroWeights 58 c) (hH : H ≠ 0) (hu : weight H = 5) :
    69 ≤ weight (interval 58 c * H) := by
  apply prime_comparison_lifting 58 c 5 69 hc (by omega) (by omega)
    (by omega) (by omega) (by omega) ?_ H hH hu
  intro D q hD hnorm hlargest hweight
  exact binary_comparison_58 q c D hc hD hnorm hlargest hweight

end WeightedPilz

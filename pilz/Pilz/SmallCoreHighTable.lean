import Pilz.RepeatedLinearCore
import Pilz.SmallCoreParameters
import Pilz.SmallInitial
import Pilz.TrialSmooth
import Mathlib.Tactic.IntervalCases

/-! The core-sum decomposition for the finite range 27 through 66. The set
partitions below are exact finite arithmetic certificates; the distance bound
then follows from repeated endpoint slicing. -/

noncomputable section
namespace Pilz
open MvPolynomial
open scoped BigOperators

def smallSmoothCore (n : ℕ) : Poly :=
  smoothInterval (primesUpTo (Nat.sqrt n)) n

def linearCorePiece (n p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (n / p)).image (fun a => p * a)

def HighCorePartition (n : ℕ) : Prop :=
  Finset.Icc 1 n \ freshPrimes n =
    smoothNumbers (primesUpTo (Nat.sqrt n)) n ∪
      (linearCorePrimes n).biUnion (linearCorePiece n) ∧
  Disjoint (smoothNumbers (primesUpTo (Nat.sqrt n)) n)
    ((linearCorePrimes n).biUnion (linearCorePiece n)) ∧
  (∀ p ∈ linearCorePrimes n, ∀ q ∈ linearCorePrimes n, p ≠ q →
    Disjoint (linearCorePiece n p) (linearCorePiece n q)) ∧
  (∀ p ∈ linearCorePrimes n,
    1 ≤ n / p ∧ n / p ≤ 8 ∧ ∀ q ∈ linearCorePrimes n, n / p < q)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem highCorePartition (n : ℕ) (hn : 27 ≤ n) (hn' : n ≤ 66) :
    HighCorePartition n := by
  interval_cases n
  · have hs : Nat.sqrt 27 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 27 ∧ 27 < (5 + 1) * (5 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 28 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 28 ∧ 28 < (5 + 1) * (5 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 29 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 29 ∧ 29 < (5 + 1) * (5 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 30 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 30 ∧ 30 < (5 + 1) * (5 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 31 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 31 ∧ 31 < (5 + 1) * (5 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 32 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 32 ∧ 32 < (5 + 1) * (5 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 33 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 33 ∧ 33 < (5 + 1) * (5 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 34 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 34 ∧ 34 < (5 + 1) * (5 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 35 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 35 ∧ 35 < (5 + 1) * (5 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 36 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 36 ∧ 36 < (6 + 1) * (6 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 37 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 37 ∧ 37 < (6 + 1) * (6 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 38 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 38 ∧ 38 < (6 + 1) * (6 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 39 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 39 ∧ 39 < (6 + 1) * (6 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 40 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 40 ∧ 40 < (6 + 1) * (6 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 41 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 41 ∧ 41 < (6 + 1) * (6 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 42 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 42 ∧ 42 < (6 + 1) * (6 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 43 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 43 ∧ 43 < (6 + 1) * (6 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 44 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 44 ∧ 44 < (6 + 1) * (6 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 45 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 45 ∧ 45 < (6 + 1) * (6 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 46 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 46 ∧ 46 < (6 + 1) * (6 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 47 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 47 ∧ 47 < (6 + 1) * (6 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 48 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 48 ∧ 48 < (6 + 1) * (6 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 49 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 49 ∧ 49 < (7 + 1) * (7 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 50 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 50 ∧ 50 < (7 + 1) * (7 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 51 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 51 ∧ 51 < (7 + 1) * (7 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 52 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 52 ∧ 52 < (7 + 1) * (7 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 53 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 53 ∧ 53 < (7 + 1) * (7 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 54 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 54 ∧ 54 < (7 + 1) * (7 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 55 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 55 ∧ 55 < (7 + 1) * (7 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 56 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 56 ∧ 56 < (7 + 1) * (7 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 57 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 57 ∧ 57 < (7 + 1) * (7 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 58 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 58 ∧ 58 < (7 + 1) * (7 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 59 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 59 ∧ 59 < (7 + 1) * (7 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 60 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 60 ∧ 60 < (7 + 1) * (7 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 61 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 61 ∧ 61 < (7 + 1) * (7 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 62 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 62 ∧ 62 < (7 + 1) * (7 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 63 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 63 ∧ 63 < (7 + 1) * (7 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 64 = 8 :=
      (Nat.eq_sqrt.mpr (by decide : 8 * 8 ≤ 64 ∧ 64 < (8 + 1) * (8 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 65 = 8 :=
      (Nat.eq_sqrt.mpr (by decide : 8 * 8 ≤ 65 ∧ 65 < (8 + 1) * (8 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide
  · have hs : Nat.sqrt 66 = 8 :=
      (Nat.eq_sqrt.mpr (by decide : 8 * 8 ≤ 66 ∧ 66 < (8 + 1) * (8 + 1))).symm
    unfold HighCorePartition linearCorePrimes
    rw [hs]
    simp only [smoothNumbers_eq_trialSmoothNumbers]
    decide

theorem polynomialOf_linearCorePiece (n p : ℕ) (hp : Nat.Prime p) :
    polynomialOf (linearCorePiece n p) = interval (n / p) * X p := by
  classical
  calc
    _ = ∑ a ∈ Finset.Icc 1 (n / p), monomialOf (p * a) := by
      unfold polynomialOf linearCorePiece
      apply Finset.sum_image
      intro a ha b hb hab
      exact Nat.eq_of_mul_eq_mul_left hp.pos hab
    _ = ∑ a ∈ Finset.Icc 1 (n / p), monomialOf p * monomialOf a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact monomialOf_mul hp.ne_zero (ne_of_gt (Finset.mem_Icc.mp ha).1)
    _ = monomialOf p * interval (n / p) := by
      rw [← Finset.mul_sum]
      rfl
    _ = _ := by rw [monomialOf_prime hp]; exact mul_comm _ _

theorem highCore_identity (n : ℕ) (hn : 27 ≤ n) (hn' : n ≤ 66) :
    core n = smallSmoothCore n +
      ∑ p ∈ linearCorePrimes n, interval (n / p) * X p := by
  classical
  obtain ⟨hpart, hdis, hpair, _⟩ := highCorePartition n hn hn'
  unfold core
  rw [hpart]
  have hunion :
      polynomialOf (smoothNumbers (primesUpTo (Nat.sqrt n)) n ∪
        (linearCorePrimes n).biUnion (linearCorePiece n)) =
      smallSmoothCore n +
        ∑ p ∈ linearCorePrimes n, polynomialOf (linearCorePiece n p) := by
    unfold polynomialOf smallSmoothCore smoothInterval
    rw [Finset.sum_union hdis]
    congr 1
    apply Finset.sum_biUnion
    exact hpair
  rw [hunion]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  exact polynomialOf_linearCorePiece n p
    (primesUpTo_prime (n / 2) p (Finset.mem_filter.mp hp).1)

theorem constantCoeff_smoothInterval (T : Finset ℕ) (n : ℕ) (hn : 1 ≤ n) :
    constantCoeff (smoothInterval T n) = 1 := by
  have hpos : ∀ a ∈ smoothNumbers T n, 0 < a :=
    fun a ha => ((mem_smoothNumbers T n a).mp ha).1
  have hone : 1 ∈ smoothNumbers T n := by
    apply (mem_smoothNumbers T n 1).mpr
    refine ⟨by decide, hn, ?_⟩
    simp [Smooth]
  have hc := coeff_polynomialOf (smoothNumbers T n) hpos (a := 1) (by decide)
  change coeff 0 (polynomialOf (smoothNumbers T n)) = 1
  simpa [hone] using hc

theorem degreeOf_zero_of_vars_subset {P : Poly} {T : Finset ℕ}
    (hP : P.vars ⊆ T) {p : ℕ} (hp : p ∉ T) : P.degreeOf p = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply degreeOf_le_iff.mpr
  intro d hd
  exact (mem_support_notMem_vars_zero hd (fun hmem => hp (hP hmem))).le

theorem interval_degree_zero_of_greater {j p : ℕ} (hjp : j < p) :
    (interval j).degreeOf p = 0 := by
  apply degreeOf_zero_of_vars_subset
    (T := primesUpTo j)
  · have hh := smoothInterval_vars_subset (primesUpTo j) j
    rwa [smoothInterval_primesUpTo_eq_interval (q := j) le_rfl] at hh
  · intro hp
    exact (Nat.not_le_of_gt hjp) ((mem_primesUpTo j p).mp hp).2

theorem coreKappa_distance_lower_high_of_base (n : ℕ) (hn : 27 ≤ n) (hn' : n ≤ 66)
    (hbase : coreBKappa n ≤ distance (smallSmoothCore n)) :
    coreKappa n ≤ distance (core n) := by
  classical
  obtain ⟨_, _, _, hidx⟩ := highCorePartition n hn hn'
  have hC : constantCoeff (smallSmoothCore n) ≠ 0 := by
    rw [smallSmoothCore, constantCoeff_smoothInterval _ _ (by omega)]
    exact one_ne_zero
  have hA : ∀ p ∈ linearCorePrimes n, interval (n / p) ≠ 0 := by
    intro p hp hz
    have hw := weight_interval (n / p)
    rw [hz, weight_zero] at hw
    have hpos := (hidx p hp).1
    omega
  have hCdeg : ∀ p ∈ linearCorePrimes n, (smallSmoothCore n).degreeOf p = 0 := by
    intro p hp
    apply degreeOf_zero_of_vars_subset
      (P := smallSmoothCore n) (T := primesUpTo (Nat.sqrt n))
    · exact smoothInterval_vars_subset _ _
    · intro hmem
      have hlo := (Finset.mem_filter.mp hp).2
      have hhi := ((mem_primesUpTo _ p).mp hmem).2
      omega
  have hAdeg : ∀ p ∈ linearCorePrimes n, ∀ q ∈ linearCorePrimes n,
      (interval (n / p)).degreeOf q = 0 :=
    fun p hp q hq => interval_degree_zero_of_greater ((hidx p hp).2.2 q hq)
  have hsum := repeated_linear_core_distance (linearCorePrimes n) (smallSmoothCore n)
    (fun p => interval (n / p)) hC hA hCdeg hAdeg
  rw [← highCore_identity n hn hn'] at hsum
  have heq : (∑ p ∈ linearCorePrimes n, distance (interval (n / p))) =
      ∑ p ∈ linearCorePrimes n, n / p := by
    apply Finset.sum_congr rfl
    intro p hp
    exact distance_interval_eq_of_conjecture
      (conjectureAt_le_ten (n / p) (by have hh := (hidx p hp).2.1; omega))
  rw [heq] at hsum
  unfold coreKappa
  rw [if_neg (show ¬n ≤ 26 by omega)]
  exact (Nat.add_le_add_right hbase _).trans hsum

end Pilz


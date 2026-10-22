import Pilz.SmallInitial
import Pilz.SmallCoreBounds
import Pilz.SmallMonomials
import Pilz.SmallCoreParameters
import Pilz.RepeatedLinearCore
import Pilz.IntervalDegree

/-!
# The core-distance table for lengths eleven through twenty-six

Every row is an exact polynomial identity. Repeated endpoint slicing adds
the distances of its linear interval coefficients to the checked core bound.
-/

noncomputable section

namespace Pilz

open MvPolynomial
open scoped BigOperators

def lowCoreBase (n : ℕ) : Poly :=
  if n ≤ 11 then SmallCore.f9 else if n ≤ 15 then SmallCore.f12 else
  if n ≤ 17 then SmallCore.f16 else if n ≤ 23 then SmallCore.f18 else
  if n = 24 then SmallCore.f24 else SmallCore.f25

def lowCoreLinearPrimes (n : ℕ) : Finset ℕ :=
  if n ≤ 13 then {5} else if n ≤ 21 then {5, 7} else
  if n ≤ 24 then {5, 7, 11} else if n = 25 then {7, 11} else {7, 11, 13}

def lowCoreBaseKappa (n : ℕ) : ℕ :=
  if n ≤ 11 then 5 else if n ≤ 15 then 4 else if n ≤ 17 then 4 else
  if n ≤ 23 then 6 else if n = 24 then 5 else 8

private def lowCoreTerms (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  if n ≤ 11 then SmallCore.terms9 else if n ≤ 15 then SmallCore.terms12 else
  if n ≤ 17 then SmallCore.terms16 else if n ≤ 23 then SmallCore.terms18 else
  if n = 24 then SmallCore.terms24 else SmallCore.terms25

private theorem low_core_eq_11 :
    core 11 = lowCoreBase 11 +
      ∑ p ∈ lowCoreLinearPrimes 11, interval (11 / p) * X p := by
  have hs : Finset.Icc 1 11 \ freshPrimes 11 = ({1, 2, 3, 4, 5, 6, 8, 9, 10} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, lowCoreBase, lowCoreLinearPrimes, interval_two,
    monomialOf_one, SmallCore.f9, SmallCore.f9At, SmallCore.cAt, Finset.sum_range_succ]
  ring

private theorem low_core_eq_12 :
    core 12 = lowCoreBase 12 +
      ∑ p ∈ lowCoreLinearPrimes 12, interval (12 / p) * X p := by
  have hs : Finset.Icc 1 12 \ freshPrimes 12 = ({1, 2, 3, 4, 5, 6, 8, 9, 10, 12} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, lowCoreBase, lowCoreLinearPrimes, interval_two,
    monomialOf_one, SmallCore.f12, SmallCore.f12At, SmallCore.cAt, Finset.sum_range_succ]
  ring

private theorem low_core_eq_13 :
    core 13 = lowCoreBase 13 +
      ∑ p ∈ lowCoreLinearPrimes 13, interval (13 / p) * X p := by
  have hs : Finset.Icc 1 13 \ freshPrimes 13 = ({1, 2, 3, 4, 5, 6, 8, 9, 10, 12} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, lowCoreBase, lowCoreLinearPrimes, interval_two,
    monomialOf_one, SmallCore.f12, SmallCore.f12At, SmallCore.cAt, Finset.sum_range_succ]
  ring

private theorem low_core_eq_14 :
    core 14 = lowCoreBase 14 +
      ∑ p ∈ lowCoreLinearPrimes 14, interval (14 / p) * X p := by
  have hs : Finset.Icc 1 14 \ freshPrimes 14 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, lowCoreBase, lowCoreLinearPrimes, interval_two,
    monomialOf_one, SmallCore.f12, SmallCore.f12At, SmallCore.cAt, Finset.sum_range_succ]
  ring

private theorem low_core_eq_15 :
    core 15 = lowCoreBase 15 +
      ∑ p ∈ lowCoreLinearPrimes 15, interval (15 / p) * X p := by
  have hs : Finset.Icc 1 15 \ freshPrimes 15 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, lowCoreBase, lowCoreLinearPrimes, interval_two, interval_three,
    monomialOf_one, SmallCore.f12, SmallCore.f12At, SmallCore.cAt, Finset.sum_range_succ]
  ring

private theorem low_core_eq_16 :
    core 16 = lowCoreBase 16 +
      ∑ p ∈ lowCoreLinearPrimes 16, interval (16 / p) * X p := by
  have hs : Finset.Icc 1 16 \ freshPrimes 16 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, lowCoreBase, lowCoreLinearPrimes, interval_two, interval_three,
    monomialOf_one, SmallCore.f16, SmallCore.f16At, SmallCore.cAt, Finset.sum_range_succ]
  ring

private theorem low_core_eq_17 :
    core 17 = lowCoreBase 17 +
      ∑ p ∈ lowCoreLinearPrimes 17, interval (17 / p) * X p := by
  have hs : Finset.Icc 1 17 \ freshPrimes 17 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, lowCoreBase, lowCoreLinearPrimes, interval_two, interval_three,
    monomialOf_one, SmallCore.f16, SmallCore.f16At, SmallCore.cAt, Finset.sum_range_succ]
  ring

private theorem low_core_eq_18 :
    core 18 = lowCoreBase 18 +
      ∑ p ∈ lowCoreLinearPrimes 18, interval (18 / p) * X p := by
  have hs : Finset.Icc 1 18 \ freshPrimes 18 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, lowCoreBase, lowCoreLinearPrimes, interval_two, interval_three,
    monomialOf_one, SmallCore.f18, SmallCore.f18At, SmallCore.cAt, Finset.sum_range_succ]
  ring

private theorem low_core_eq_19 :
    core 19 = lowCoreBase 19 +
      ∑ p ∈ lowCoreLinearPrimes 19, interval (19 / p) * X p := by
  have hs : Finset.Icc 1 19 \ freshPrimes 19 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, lowCoreBase, lowCoreLinearPrimes, interval_two, interval_three,
    monomialOf_one, SmallCore.f18, SmallCore.f18At, SmallCore.cAt, Finset.sum_range_succ]
  ring

private theorem low_core_eq_20 :
    core 20 = lowCoreBase 20 +
      ∑ p ∈ lowCoreLinearPrimes 20, interval (20 / p) * X p := by
  have hs : Finset.Icc 1 20 \ freshPrimes 20 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, lowCoreBase, lowCoreLinearPrimes, interval_two, interval_four,
    monomialOf_one, SmallCore.f18, SmallCore.f18At, SmallCore.cAt, Finset.sum_range_succ]
  ring

private theorem low_core_eq_21 :
    core 21 = lowCoreBase 21 +
      ∑ p ∈ lowCoreLinearPrimes 21, interval (21 / p) * X p := by
  have hs : Finset.Icc 1 21 \ freshPrimes 21 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, lowCoreBase, lowCoreLinearPrimes, interval_three, interval_four,
    monomialOf_one, SmallCore.f18, SmallCore.f18At, SmallCore.cAt, Finset.sum_range_succ]
  ring

private theorem low_core_eq_22 :
    core 22 = lowCoreBase 22 +
      ∑ p ∈ lowCoreLinearPrimes 22, interval (22 / p) * X p := by
  have hs : Finset.Icc 1 22 \ freshPrimes 22 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, lowCoreBase, lowCoreLinearPrimes, interval_two, interval_three, interval_four,
    monomialOf_one, SmallCore.f18, SmallCore.f18At, SmallCore.cAt, Finset.sum_range_succ]
  ring

private theorem low_core_eq_23 :
    core 23 = lowCoreBase 23 +
      ∑ p ∈ lowCoreLinearPrimes 23, interval (23 / p) * X p := by
  have hs : Finset.Icc 1 23 \ freshPrimes 23 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, lowCoreBase, lowCoreLinearPrimes, interval_two, interval_three, interval_four,
    monomialOf_one, SmallCore.f18, SmallCore.f18At, SmallCore.cAt, Finset.sum_range_succ]
  ring

private theorem low_core_eq_24 :
    core 24 = lowCoreBase 24 +
      ∑ p ∈ lowCoreLinearPrimes 24, interval (24 / p) * X p := by
  have hs : Finset.Icc 1 24 \ freshPrimes 24 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, lowCoreBase, lowCoreLinearPrimes, interval_two, interval_three, interval_four,
    monomialOf_one, SmallCore.f24, SmallCore.f24At, SmallCore.cAt, Finset.sum_range_succ]
  ring

private theorem low_core_eq_25 :
    core 25 = lowCoreBase 25 +
      ∑ p ∈ lowCoreLinearPrimes 25, interval (25 / p) * X p := by
  have hs : Finset.Icc 1 25 \ freshPrimes 25 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24, 25} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, lowCoreBase, lowCoreLinearPrimes, interval_two, interval_three,
    monomialOf_one, SmallCore.f25, SmallCore.f25At, SmallCore.f24At, SmallCore.cAt, Finset.sum_range_succ]
  ring

private theorem low_core_eq_26 :
    core 26 = lowCoreBase 26 +
      ∑ p ∈ lowCoreLinearPrimes 26, interval (26 / p) * X p := by
  have hs : Finset.Icc 1 26 \ freshPrimes 26 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26} : Finset ℕ) := by decide
  rw [core, hs]
  simp [polynomialOf, lowCoreBase, lowCoreLinearPrimes, interval_two, interval_three,
    monomialOf_one, SmallCore.f25, SmallCore.f25At, SmallCore.f24At, SmallCore.cAt, Finset.sum_range_succ]
  ring

/-- The exact decompositions in the paper's first core table. -/
theorem lowCore_identity (n : ℕ) (hn11 : 11 ≤ n) (hn26 : n ≤ 26) :
    core n = lowCoreBase n +
      ∑ p ∈ lowCoreLinearPrimes n, interval (n / p) * X p := by
  interval_cases n
  · exact low_core_eq_11
  · exact low_core_eq_12
  · exact low_core_eq_13
  · exact low_core_eq_14
  · exact low_core_eq_15
  · exact low_core_eq_16
  · exact low_core_eq_17
  · exact low_core_eq_18
  · exact low_core_eq_19
  · exact low_core_eq_20
  · exact low_core_eq_21
  · exact low_core_eq_22
  · exact low_core_eq_23
  · exact low_core_eq_24
  · exact low_core_eq_25
  · exact low_core_eq_26

private theorem lowCoreBase_terms (n : ℕ) :
    lowCoreBase n = ∑ t ∈ lowCoreTerms n, SmallCore.coreTerm t := by
  unfold lowCoreBase lowCoreTerms
  split_ifs <;> first
    | exact SmallCore.f9_terms
    | exact SmallCore.f12_terms
    | exact SmallCore.f16_terms
    | exact SmallCore.f18_terms
    | exact SmallCore.f24_terms
    | exact SmallCore.f25_terms

private theorem lowCoreBase_constant (n : ℕ) : constantCoeff (lowCoreBase n) = 1 := by
  unfold lowCoreBase
  split_ifs <;> first
    | exact SmallCore.constantCoeff_f9
    | exact SmallCore.constantCoeff_f12
    | exact SmallCore.constantCoeff_f16
    | exact SmallCore.constantCoeff_f18
    | exact SmallCore.constantCoeff_f24
    | exact SmallCore.constantCoeff_f25

private theorem lowCoreBase_distance (n : ℕ) :
    lowCoreBaseKappa n ≤ distance (lowCoreBase n) := by
  unfold lowCoreBaseKappa lowCoreBase
  split_ifs <;> first
    | exact F9Param.f9_distance_lower_five
    | exact SmallCore.f12_distance_lower
    | exact SmallCore.f16_distance_four
    | exact SmallCore.f18_distance_six
    | exact SmallCore.f24_distance_five
    | exact SmallCore.f25_distance_eight

private theorem lowCore_quotients (n : ℕ) (hn11 : 11 ≤ n) (hn26 : n ≤ 26) :
    ∀ p ∈ lowCoreLinearPrimes n, 2 ≤ n / p ∧ n / p ≤ 4 ∧ 5 ≤ p := by
  interval_cases n <;> norm_num [lowCoreLinearPrimes]

private theorem lowCore_exponents (n : ℕ) (hn11 : 11 ≤ n) (hn26 : n ≤ 26) :
    ∀ p ∈ lowCoreLinearPrimes n, ∀ t ∈ lowCoreTerms n,
      SmallCore.coreExponent t.1 t.2.1 t.2.2 p = 0 := by
  interval_cases n <;>
    simp only [SmallCore.coreExponent, Finsupp.add_apply, Finsupp.single_apply] <;> decide

private theorem lowCoreBase_degree (n : ℕ) (hn11 : 11 ≤ n) (hn26 : n ≤ 26)
    (p : ℕ) (hp : p ∈ lowCoreLinearPrimes n) : (lowCoreBase n).degreeOf p = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [lowCoreBase_terms]
  refine (degreeOf_sum_le p (lowCoreTerms n) SmallCore.coreTerm).trans ?_
  apply Finset.sup_le
  intro t ht
  rw [SmallCore.coreTerm,
    degreeOf_monomial_eq _ p (one_ne_zero : (1 : ZMod 2) ≠ 0),
    lowCore_exponents n hn11 hn26 p hp t ht]

private theorem lowCoreKappa_eq (n : ℕ) (hn11 : 11 ≤ n) (hn26 : n ≤ 26) :
    coreKappa n = lowCoreBaseKappa n + ∑ p ∈ lowCoreLinearPrimes n, n / p := by
  interval_cases n <;> norm_num [coreKappa, lowCoreBaseKappa, lowCoreLinearPrimes]

/-- The complete checked lower-bound table for the cores at lengths 11–26. -/
theorem coreKappa_distance_lower_low (n : ℕ) (hn11 : 11 ≤ n) (hn26 : n ≤ 26) :
    coreKappa n ≤ distance (core n) := by
  have hC : constantCoeff (lowCoreBase n) ≠ 0 := by
    rw [lowCoreBase_constant]
    exact one_ne_zero
  have hA : ∀ p ∈ lowCoreLinearPrimes n, interval (n / p) ≠ 0 := by
    intro p hp
    exact interval_ne_zero (by have h := lowCore_quotients n hn11 hn26 p hp; omega)
  have hAdeg : ∀ p ∈ lowCoreLinearPrimes n, ∀ q ∈ lowCoreLinearPrimes n,
      (interval (n / p)).degreeOf q = 0 := by
    intro p hp q hq
    apply interval_degree_zero_of_lt
    have h := lowCore_quotients n hn11 hn26 p hp
    have h' := lowCore_quotients n hn11 hn26 q hq
    omega
  have hbudget := repeated_linear_core_distance (lowCoreLinearPrimes n) (lowCoreBase n)
    (fun p => interval (n / p)) hC hA (lowCoreBase_degree n hn11 hn26) hAdeg
  rw [← lowCore_identity n hn11 hn26] at hbudget
  change distance (lowCoreBase n) +
    (∑ p ∈ lowCoreLinearPrimes n, distance (interval (n / p))) ≤ distance (core n) at hbudget
  have hbase := lowCoreBase_distance n
  have hcoeff : (∑ p ∈ lowCoreLinearPrimes n, n / p) ≤
      ∑ p ∈ lowCoreLinearPrimes n, distance (interval (n / p)) := by
    apply Finset.sum_le_sum
    intro p hp
    rw [distance_interval_le_ten (n / p)
      (by have h := lowCore_quotients n hn11 hn26 p hp; omega)]
  rw [lowCoreKappa_eq n hn11 hn26]
  exact (Nat.add_le_add hbase hcoeff).trans hbudget

end Pilz


import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Tactic

/-!
# Finite inclusion-exclusion for parity

This module proves the finite Boolean identity underlying the ordinary
mathematical density proof. It is a complete identity for arbitrary finite
families, not yet the number-theoretic identification of intersections with
floor counts.
-/

noncomputable section
open scoped BigOperators

namespace PilzDensity

theorem parity_indicator (r : ℕ) :
    (2 : ℤ) * (if Odd r then 1 else 0) = 1 - (-1 : ℤ) ^ r := by
  by_cases hr : Odd r
  · simp [hr, hr.neg_one_pow]
  · have he : Even r := Nat.not_odd_iff_even.mp hr
    simp [hr, he.neg_one_pow]

theorem parity_powerset_identity {ι : Type*} (I : Finset ι)
    (P : ι → Prop) [DecidablePred P] :
    (2 : ℤ) * (if Odd (I.filter P).card then 1 else 0) =
      1 - ∑ J ∈ I.powerset,
        (-2 : ℤ) ^ J.card * (if ∀ j ∈ J, P j then 1 else 0) := by
  classical
  have hprod :
      (∏ i ∈ I, (1 + (if P i then (-2 : ℤ) else 0))) =
        (-1 : ℤ) ^ (I.filter P).card := by
    calc
      _ = ∏ i ∈ I, (if P i then (-1 : ℤ) else 1) := by
        apply Finset.prod_congr rfl
        intro i hi
        split_ifs <;> norm_num
      _ = _ := by rw [Finset.prod_ite]; simp
  rw [Finset.prod_one_add] at hprod
  have hsum :
      (∑ J ∈ I.powerset, ∏ i ∈ J, (if P i then (-2 : ℤ) else 0)) =
        ∑ J ∈ I.powerset,
          (-2 : ℤ) ^ J.card * (if ∀ j ∈ J, P j then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro J hJ
    rw [Finset.prod_ite_zero, Finset.prod_const]
    split_ifs <;> simp
  rw [hsum] at hprod
  rw [hprod]
  exact parity_indicator _

/-- Twice the number of points belonging to an odd number of the sets, in
a finite universe, expressed through all intersection cardinalities. -/
theorem odd_card_inclusion_exclusion {ι α : Type*} [DecidableEq α]
    (I : Finset ι) (U : Finset α) (S : ι → Finset α) :
    (2 : ℤ) *
      ((U.filter fun x => Odd (I.filter fun i => x ∈ S i).card).card : ℤ) =
    (U.card : ℤ) -
      ∑ J ∈ I.powerset, (-2 : ℤ) ^ J.card *
        ((U.filter fun x => ∀ j ∈ J, x ∈ S j).card : ℤ) := by
  classical
  have hc (P : α → Prop) [DecidablePred P] :
      ((U.filter P).card : ℤ) = ∑ x ∈ U, if P x then (1 : ℤ) else 0 := by
    simp
  rw [hc]
  rw [Finset.mul_sum]
  simp_rw [parity_powerset_identity]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [← Finset.mul_sum, hc]

#print axioms PilzDensity.odd_card_inclusion_exclusion

end PilzDensity



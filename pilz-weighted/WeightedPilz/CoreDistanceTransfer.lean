import WeightedPilz.CoreBudgets

/-! Transfer any weighted smooth-core distance bound to the full core. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K]

private theorem mem_linearCorePrimes {n p : ℕ} :
    p ∈ Arithmetic.linearCorePrimes n ↔
      Nat.Prime p ∧ Nat.sqrt n < p ∧ p ≤ n / 2 := Arithmetic.mem_linearCorePrimes n p

private theorem degree_zero_of_vars_subset {P : Poly K} {T : Finset ℕ}
    (hvars : P.vars ⊆ T) {p : ℕ} (hp : p ∉ T) : P.degreeOf p = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply degreeOf_le_iff.mpr
  intro d hd
  exact Nat.le_of_eq (mem_support_notMem_vars_zero hd (fun h => hp (hvars h)))

private theorem core_component_degree_zero (n : ℕ) (c : ℕ → K)
    (p : ℕ) (hp : p ∈ Arithmetic.linearCorePrimes n) :
    (smoothInterval (Pilz.primesUpTo (Nat.sqrt n)) n c).degreeOf p = 0 := by
  apply degree_zero_of_vars_subset (smoothInterval_vars_subset _ n c)
  intro h
  have hlo := (mem_linearCorePrimes.mp hp).2.1
  have hhi := ((Pilz.mem_primesUpTo _ _).mp h).2
  omega

private theorem linear_component_degree_zero (n : ℕ) (c : ℕ → K)
    (p : ℕ) (hp : p ∈ Arithmetic.linearCorePrimes n)
    (q : ℕ) (hq : q ∈ Arithmetic.linearCorePrimes n) :
    (interval (n / p) (fun a => c (p * a))).degreeOf q = 0 := by
  have hps := div_le_sqrt_of_sqrt_lt (mem_linearCorePrimes.mp hp).2.1
  have hv := smoothInterval_vars_subset (Pilz.primesUpTo (Nat.sqrt n))
    (n / p) (fun a => c (p * a))
  rw [smoothInterval_primesUpTo_eq_interval hps] at hv
  apply degree_zero_of_vars_subset hv
  intro h
  have hlo := (mem_linearCorePrimes.mp hq).2.1
  have hhi := ((Pilz.mem_primesUpTo _ _).mp h).2
  omega

theorem intervalCore_distance_of_smooth_distance (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 4 ≤ n)
    (hsmall : ∀ j ≤ Nat.sqrt n, ∀ w : ℕ → K, NonzeroWeights j w → IntervalBound j w)
    (b : ℕ) (hb : b ≤ distance (smoothInterval (Pilz.primesUpTo (Nat.sqrt n)) n c)) :
    b + Arithmetic.linearCoreCost n ≤ distance (intervalCore n c) := by
  classical
  let A := smoothInterval (Pilz.primesUpTo (Nat.sqrt n)) n c
  let B := fun p => interval (n / p) (fun a => c (p * a))
  have hA : constantCoeff A ≠ 0 := by
    change coeff 0 A ≠ 0
    dsimp [A]
    rw [smoothInterval_coeff_zero _ n c (by omega)]
    exact hc 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hB : ∀p∈Arithmetic.linearCorePrimes n, B p ≠ 0 := by
    intro p hp
    have hpdata := mem_linearCorePrimes.mp hp
    have hj : 0 < n / p := Nat.div_pos
      (hpdata.2.2.trans (Nat.div_le_self n 2)) hpdata.1.pos
    exact interval_ne_zero _ hj (linearCore_coefficient_weights n p c hc hp)
  have hagg := repeated_linear_core_distance (Arithmetic.linearCorePrimes n) A B hA hB
    (core_component_degree_zero n c) (linear_component_degree_zero n c)
  have hbase : b ≤ distance A := hb
  have hsum : (∑p∈Arithmetic.linearCorePrimes n, n / p) ≤
      ∑p∈Arithmetic.linearCorePrimes n, distance (B p) := by
    apply Finset.sum_le_sum
    intro p hp
    apply (le_distance_iff _ _).mpr
    exact hsmall _ (div_le_sqrt_of_sqrt_lt (mem_linearCorePrimes.mp hp).2.1) _
      (linearCore_coefficient_weights n p c hc hp)
  rw [intervalCore_eq_smooth_add_linear n c hn]
  exact (Nat.add_le_add hbase hsum).trans hagg

end WeightedPilz

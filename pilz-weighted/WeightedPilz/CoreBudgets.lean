import WeightedPilz.CoreDecomposition
import WeightedPilz.PowerGap

/-! Exact weighted endpoint and square budgets for the square-root core.
The only induction input is the interval theorem at the smaller component indices. -/

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

/-- Every small prime is a distinct pure vertex of the smooth core. -/
theorem smooth_core_prime_distance (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 0 < n) :
    1 + Pilz.primeCount (Nat.sqrt n) ≤
      distance (smoothInterval (Pilz.primesUpTo (Nat.sqrt n)) n c) := by
  have h0 : coeff 0 (smoothInterval (Pilz.primesUpTo (Nat.sqrt n)) n c) ≠ 0 := by
    rw [smoothInterval_coeff_zero _ n c hn]
    exact hc 1 (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)
  have hpure : ∀p∈Pilz.primesUpTo (Nat.sqrt n), ∃k:ℕ, 0 < k ∧
      coeff (Finsupp.single p k)
        (smoothInterval (Pilz.primesUpTo (Nat.sqrt n)) n c) ≠ 0 := by
    intro p hp
    obtain ⟨hpp, hps⟩ := (Pilz.mem_primesUpTo _ p).mp hp
    have hpn := hps.trans (Nat.sqrt_le_self n)
    refine ⟨1, by decide, ?_⟩
    rw [smoothInterval_coeff_prime _ n p c hpp hp hpn]
    exact hc p (Finset.mem_Icc.mpr ⟨hpp.pos, hpn⟩)
  simpa only [Pilz.card_primesUpTo, Nat.add_comm] using
    pure_endpoints_distance (Pilz.primesUpTo (Nat.sqrt n)) _ h0 hpure

/-- The manuscript's κ endpoint bound, retaining the inherited coefficients
`c (p*a)` in every smaller interval. -/
theorem intervalCore_endpoint_distance (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 4 ≤ n)
    (hsmall : ∀ j ≤ Nat.sqrt n, ∀ w : ℕ → K, NonzeroWeights j w → IntervalBound j w) :
    Arithmetic.endpoint n ≤ distance (intervalCore n c) := by
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
  have hbase := smooth_core_prime_distance n c hc (show 0 < n by omega)
  have hsum : (∑p∈Arithmetic.linearCorePrimes n, n / p) ≤
      ∑p∈Arithmetic.linearCorePrimes n, distance (B p) := by
    apply Finset.sum_le_sum
    intro p hp
    apply (le_distance_iff _ _).mpr
    exact hsmall _ (div_le_sqrt_of_sqrt_lt (mem_linearCorePrimes.mp hp).2.1) _
      (linearCore_coefficient_weights n p c hc hp)
  rw [intervalCore_eq_smooth_add_linear n c hn]
  exact (Nat.add_le_add hbase hsum).trans hagg

/-- Constant and prime-two coefficients give a one-term strict power gap,
without a characteristic or perfectness classification. -/
theorem square_gap_of_constant_and_two (P : Poly K) (h0 : coeff 0 P ≠ 0)
    (h1 : coeff (Finsupp.single 2 1) P ≠ 0) (h2 : (2 : K) ≠ 0) :
    distance P + 1 ≤ weight (P ^ 2) := by
  apply power_gap_of_residue_variation P 2 (mem_support_iff.mpr h0)
    (mem_support_iff.mpr h1) _ (by decide : 2 ≤ 2) h2
  simp

/-- In odd characteristic the pure square rows improve κ by one for the
constant component and one for every linear core prime. -/
theorem intervalCore_square_weight (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 4 ≤ n) (h2 : (2 : K) ≠ 0)
    (hsmall : ∀ j ≤ Nat.sqrt n, ∀ w : ℕ → K, NonzeroWeights j w → IntervalBound j w) :
    Arithmetic.endpoint n + Arithmetic.linearCoreCount n + 1 ≤
      weight (intervalCore n c ^ 2) := by
  classical
  let A := smoothInterval (Pilz.primesUpTo (Nat.sqrt n)) n c
  let B := fun p => interval (n / p) (fun a => c (p * a))
  have htwo : 2 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hA0 : coeff 0 A ≠ 0 := by
    dsimp [A]
    rw [smoothInterval_coeff_zero _ n c (by omega)]
    exact hc 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hA1 : coeff (Finsupp.single 2 1) A ≠ 0 := by
    dsimp [A]
    rw [smoothInterval_coeff_prime _ n 2 c Nat.prime_two
      ((Pilz.mem_primesUpTo _ _).mpr ⟨Nat.prime_two, htwo⟩) (by omega)]
    exact hc 2 (Finset.mem_Icc.mpr ⟨by decide, by omega⟩)
  have hAgap := square_gap_of_constant_and_two A hA0 hA1 h2
  have hAbase := smooth_core_prime_distance n c hc (show 0 < n by omega)
  have hBbound : ∀p∈Arithmetic.linearCorePrimes n,
      n / p + 1 ≤ weight (B p ^ 2) := by
    intro p hp
    have hpdata := mem_linearCorePrimes.mp hp
    have hj2 : 2 ≤ n / p := Arithmetic.linearCoreQuotient_lower hp
    have hw := linearCore_coefficient_weights n p c hc hp
    have hB0 : coeff 0 (B p) ≠ 0 := by
      have h := coeff_interval (n / p) (fun a => c (p * a)) (a := 1) (by decide)
      rw [if_pos (by omega : 1 ≤ n / p)] at h
      simpa [B, Nat.factorization_one] using
        h.trans_ne (hw 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩))
    have hB1 : coeff (Finsupp.single 2 1) (B p) ≠ 0 := by
      have h := coeff_interval (n / p) (fun a => c (p * a)) (a := 2) (by decide)
      rw [if_pos hj2] at h
      simpa [B, Nat.prime_two.factorization] using
        h.trans_ne (hw 2 (Finset.mem_Icc.mpr ⟨by decide, hj2⟩))
    have hgap := square_gap_of_constant_and_two (B p) hB0 hB1 h2
    have hdist : n / p ≤ distance (B p) := (le_distance_iff _ _).mpr
      (hsmall _ (div_le_sqrt_of_sqrt_lt hpdata.2.1) _ hw)
    omega
  have hsum := Finset.sum_le_sum hBbound
  have hagg := repeated_linear_core_square_weight (Arithmetic.linearCorePrimes n) A B
    (core_component_degree_zero n c) (linear_component_degree_zero n c)
  rw [intervalCore_eq_smooth_add_linear n c hn]
  change Arithmetic.endpoint n + Arithmetic.linearCoreCount n + 1 ≤
    weight ((A + ∑p∈Arithmetic.linearCorePrimes n, B p * X p) ^ 2)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one] at hsum
  have hcard := card_linearCorePrimes n hn
  rw [← hcard]
  unfold Arithmetic.endpoint Arithmetic.linearCoreCost
  change 1 + Pilz.primeCount (Nat.sqrt n) + _ + _ + 1 ≤ _
  change 1 + Pilz.primeCount (Nat.sqrt n) ≤ distance A at hAbase
  omega

end WeightedPilz

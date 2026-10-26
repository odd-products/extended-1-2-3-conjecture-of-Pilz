import WeightedPilz.MiddleHigherRows
import WeightedPilz.ExceptionalCorePowers
import WeightedPilz.MiddleAffineAll
import WeightedPilz.MiddleResidueCapacities
import WeightedPilz.FiniteResidueFormula
import WeightedPilz.QuadraticAggregate

/-! Full characteristic-zero and prime-characteristic-at-least-five middle
interval bounds, including all higher-degree output exceptions. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K]

theorem middle_scalar_rows_lower (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (hr : (intervalFreshPrimes n).Nonempty) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (t : Finset ℕ) (A : ℕ → Poly K)
    (hbase : ∀ k ∈ t, (intervalFreshData n c (by omega) hc hr).BaseOnly (A k))
    (hne : (∑ k ∈ t, (intervalFreshData n c (by omega) hc hr).freshSum ^ k * A k) ≠ 0)
    (hdiv : (intervalFreshData n c (by omega) hc hr).F ∣
      ∑ k ∈ t, (intervalFreshData n c (by omega) hc hr).freshSum ^ k * A k)
    (hcost : ∀ k ∈ t, weight ((intervalFreshData n c (by omega) hc hr).freshSum ^ k * A k) =
      Arithmetic.aggregateCost n k * weight (A k)) :
    n ≤ weight (∑ k ∈ t, (intervalFreshData n c (by omega) hc hr).freshSum ^ k * A k) := by
  let S := intervalFreshData n c (by omega) hc hr
  by_contra hnot
  have hshort : weight (∑ k ∈ t, S.freshSum ^ k * A k) < n := Nat.lt_of_not_ge hnot
  have hhigh := middle_aggregate_higher_rows_zero n c hc hn hn' hr t A hbase hne hdiv hshort hcost
    (fun hnsmall => exceptional_core_cube_weight n c hc (by omega) (by omega) h2 h3)
    (fun hnsmall => exceptional_core_quartic_weight n c hc (by omega) (by omega) h2 h3)
    (by intro heq; subst n; exact exceptional_core_cube_weight_forty c hc h2 h3)
  obtain ⟨D, B, hD, hB, hDB, hfactor⟩ :=
    S.affine_cofactor_of_quadratic_rows t A hbase hhigh hne hdiv
  have hlo := middle_affine_lower_all n c hc hn hn' hr h2 D B hD hB hDB
  rw [← hfactor] at hlo
  omega

theorem intervalBound_middle_charZero [CharZero K] (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66) : IntervalBound n c := by
  have hnpos : 0 < n := by omega
  have hr : (intervalFreshPrimes n).Nonempty := by
    apply Finset.card_pos.mp
    rw [Pilz.card_freshPrimes]
    exact lt_of_lt_of_le (by decide : 0 < 3) (Arithmetic.middle_fresh_count hn hn')
  let S := intervalFreshData n c hnpos hc hr
  obtain ⟨t, A, hA, hne, hdiv, hweight⟩ := S.exists_scalar_minimum
  have hcost : ∀ k ∈ t, weight (S.freshSum ^ k * A k) =
      Arithmetic.aggregateCost n k * weight (A k) := by
    intro k hk
    rw [S.weight_base_row_charZero k (A k) (hA k hk)]
    change ((intervalFreshPrimes n).card + k - 1).choose k * weight (A k) = _
    rw [Pilz.card_freshPrimes]
    rfl
  have hlo := middle_scalar_rows_lower n c hc hn hn' hr (by norm_num) (by norm_num)
    t A hA hne hdiv hcost
  rw [hweight] at hlo
  apply (le_distance_iff (interval n c) n).mp
  rw [distance_interval_eq_freshData n c hnpos hc hr]
  exact hlo

theorem intervalBound_middle_charLarge (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp5 : 5 ≤ p) (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66) : IntervalBound n c := by
  have hp : Nat.Prime p := Fact.out
  have hnpos : 0 < n := by omega
  have hr : (intervalFreshPrimes n).Nonempty := by
    apply Finset.card_pos.mp
    rw [Pilz.card_freshPrimes]
    exact lt_of_lt_of_le (by decide : 0 < 3) (Arithmetic.middle_fresh_count hn hn')
  let S := intervalFreshData n c hnpos hc hr
  have hcap : ∀ j, 0 < j → j < p → residueSigma p (S.C ^ j) ≤
      (S.vars.card + j - 1).choose j := by
    intro j hj hjp
    change residueSigma p (intervalCore n c ^ j) ≤
      ((intervalFreshPrimes n).card + j - 1).choose j
    rw [Pilz.card_freshPrimes]
    exact intervalCore_middle_residue_capacity n p j c hc hn hn' hp hp5 hj hjp
  obtain ⟨A, hA, hmin⟩ := S.exists_minimizing_residue_rows p hcap
  have hpowers : ∀ j < p, S.PowersInFresh p (A j) :=
    fun j hj => S.baseOnly_powersInFresh p _ (hA.1 j hj)
  have hne := S.aggregate_nonzero_of_nonzero_row p A hpowers hA.2.1
  have hdiv := aggregate_replacement_dvd (Finset.range p) id A S.C S.freshSum
  simp only [id_eq, hA.2.2, sub_zero] at hdiv
  have hcost : ∀ k ∈ Finset.range p, weight (S.freshSum ^ k * A k) =
      Arithmetic.aggregateCost n k * weight (A k) := by
    intro k hk
    rw [S.weight_freshSum_pow_mul_lt_char p k (A k) (Finset.mem_range.mp hk)
      (hpowers k (Finset.mem_range.mp hk))]
    change ((intervalFreshPrimes n).card + k - 1).choose k * weight (A k) = _
    rw [Pilz.card_freshPrimes]
    rfl
  have h23 : (2 : K) ≠ 0 ∧ (3 : K) ≠ 0 := by
    constructor
    · intro hz
      have hd := (CharP.cast_eq_zero_iff K p 2).mp hz
      have := Nat.le_of_dvd (by decide : 0 < 2) hd
      omega
    · intro hz
      have hd := (CharP.cast_eq_zero_iff K p 3).mp hz
      have := Nat.le_of_dvd (by decide : 0 < 3) hd
      omega
  have hlo := middle_scalar_rows_lower n c hc hn hn' hr h23.1 h23.2 (Finset.range p) A
    (fun j hj => hA.1 j (Finset.mem_range.mp hj)) hne hdiv hcost
  rw [S.aggregate_weight_eq_cost p A hpowers, hmin] at hlo
  apply (le_distance_iff (interval n c) n).mp
  rw [distance_interval_eq_freshData n c hnpos hc hr]
  exact hlo

end WeightedPilz

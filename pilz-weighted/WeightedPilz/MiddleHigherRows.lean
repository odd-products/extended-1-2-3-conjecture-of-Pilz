import WeightedPilz.Arithmetic.MiddleSparseRows
import WeightedPilz.MiddleCore
import WeightedPilz.AggregateLowestRow

/-! Eliminate the six possible higher aggregate output rows by the actual
core power lower bounds. The finite budget argument concerns full expanded weights. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K]

private theorem sum_eq_three_of_vanishing {R : Type*} [AddCommMonoid R]
    (t : Finset ℕ) (f : ℕ → R) (j : ℕ) (h0 : 0 ∈ t) (hj : j ∈ t)
    (hj0 : j ≠ 0) (hj1 : j ≠ 1)
    (hzero : ∀ k ∈ t, k ≠ 0 → k ≠ 1 → k ≠ j → f k = 0) :
    (∑ k ∈ t, f k) = f 0 + (if 1 ∈ t then f 1 else 0) + f j := by
  classical
  let s : Finset ℕ := {0, 1, j}
  have heq : t ∩ s = s.filter (· ∈ t) := by ext k; simp [and_comm]
  calc
    _ = ∑ k ∈ t ∩ s, f k := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro k hk hknot
      have hks : k ∉ s := fun h => hknot (Finset.mem_inter.mpr ⟨hk, h⟩)
      have hkn : k ≠ 0 ∧ k ≠ 1 ∧ k ≠ j := by simpa [s] using hks
      exact hzero k hk hkn.1 hkn.2.1 hkn.2.2
    _ = ∑ k ∈ s, if k ∈ t then f k else 0 := by rw [heq, Finset.sum_filter]
    _ = _ := by
      dsimp only [s]
      rw [Finset.sum_insert (by simp [Ne.symm hj0]),
        Finset.sum_insert (by simp [Ne.symm hj1]), Finset.sum_singleton]
      rw [if_pos h0, if_pos hj]
      exact (add_assoc _ _ _).symm

private theorem weight_pow_neg_mul_of_weight_one (P B : Poly K) (j : ℕ)
    (hB : weight B = 1) : weight ((-P) ^ j * B) = weight (P ^ j) := by
  obtain ⟨e, a, ha, hBa⟩ := Finsupp.card_support_eq_one'.mp hB
  change B = monomial e a at hBa
  rw [hBa, mul_comm, weight_scalar_monomial_mul e ha]
  rcases Nat.even_or_odd j with hj | hj
  · rw [hj.neg_pow]
  · rw [hj.neg_pow]
    simp [weight]

private theorem weight_add_upper (P Q : Poly K) : weight (P + Q) ≤ weight P + weight Q :=
  (Finset.card_le_card (show (P + Q).support ⊆ P.support ∪ Q.support from
    fun _ h => MvPolynomial.support_add h)).trans (Finset.card_union_le _ _)

theorem middle_aggregate_higher_rows_zero (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (hr : (intervalFreshPrimes n).Nonempty)
    (t : Finset ℕ) (A : ℕ → Poly K)
    (hbase : ∀ k ∈ t, (intervalFreshData n c (by omega) hc hr).BaseOnly (A k))
    (hne : (∑ k ∈ t, (intervalFreshData n c (by omega) hc hr).freshSum ^ k * A k) ≠ 0)
    (hdiv : (intervalFreshData n c (by omega) hc hr).F ∣
      ∑ k ∈ t, (intervalFreshData n c (by omega) hc hr).freshSum ^ k * A k)
    (hshort : weight (∑ k ∈ t, (intervalFreshData n c (by omega) hc hr).freshSum ^ k * A k) < n)
    (hcost : ∀ k ∈ t, weight ((intervalFreshData n c (by omega) hc hr).freshSum ^ k * A k) =
      Arithmetic.aggregateCost n k * weight (A k))
    (hcube : n = 26 ∨ n = 27 ∨ n = 28 → 44 ≤ weight (intervalCore n c ^ 3))
    (hquartic : n = 27 ∨ n = 28 → 15 ≤ weight (intervalCore n c ^ 4))
    (hcube40 : n = 40 → 56 ≤ weight (intervalCore n c ^ 3)) :
    ∀ j ∈ t, 3 ≤ j → A j = 0 := by
  let S := intervalFreshData n c (by omega) hc hr
  have hkappa : Arithmetic.endpoint n ≤ distance S.C := middle_core_endpoint_distance n c hc hn hn'
  have hbudget : n ≤ S.vars.card * (Arithmetic.endpoint n + 1) := by
    change n ≤ (intervalFreshPrimes n).card * (Arithmetic.endpoint n + 1)
    rw [Pilz.card_freshPrimes]
    have hb := (Arithmetic.middleBasicBudgets hn hn').2.1
    nlinarith
  obtain ⟨h0, _, hu0⟩ := S.aggregate_lowest_row_zero t A hbase hne hdiv
    (Arithmetic.endpoint n) n hkappa hbudget hshort
  have hsumweight : weight (∑ k ∈ t, S.freshSum ^ k * A k) =
      ∑ k ∈ t, Arithmetic.aggregateCost n k * weight (A k) := by
    rw [S.base_rows_weight t A hbase]
    exact Finset.sum_congr rfl hcost
  have hsmall : (∑ k ∈ t, Arithmetic.aggregateCost n k * weight (A k)) < n := by
    rwa [← hsumweight]
  intro j hj hj3
  by_contra hAj
  obtain ⟨hcases, hAj1, hothers⟩ := Arithmetic.sparse_higher_rows hn hn' t
    (fun k => weight (A k)) h0 hu0 hsmall j hj hj3 (weight_pos hAj)
  have hj0 : j ≠ 0 := by omega
  have hj1 : j ≠ 1 := by omega
  have hzero : ∀ k ∈ t, k ≠ 0 → k ≠ 1 → k ≠ j → A k = 0 := by
    intro k hk hk0 hk1 hkj
    rcases hothers k hk hk0 hkj with hallow | hzero
    · exact (hk1 hallow.2.2.1).elim
    · by_contra hne
      have := weight_pos hne
      omega
  let E := if 1 ∈ t then A 1 else 0
  have hEw : weight E ≤ 1 := by
    by_cases h1 : 1 ∈ t
    · simp only [E, if_pos h1]
      rcases hothers 1 h1 (by decide) hj1.symm with hallow | hz
      · exact hallow.2.2.2
      · omega
    · simp [E, h1, weight]
  have hEzero : ¬(j = 3 ∧ n ≤ 28) → E = 0 := by
    intro hnot
    by_cases h1 : 1 ∈ t
    · simp only [E, if_pos h1]
      rcases hothers 1 h1 (by decide) hj1.symm with hallow | hz
      · exact (hnot ⟨hallow.1, hallow.2.1⟩).elim
      · by_contra hne
        have := weight_pos hne
        omega
    · simp [E, h1]
  have hrelation : A 0 + (-S.C) * E + (-S.C) ^ j * A j = 0 := by
    have hrel := S.aggregate_relation_of_dvd t A hbase hdiv
    have hthree := sum_eq_three_of_vanishing t (fun k => (-S.C) ^ k * A k) j h0 hj hj0 hj1
      (by intro k hk hk0 hk1 hkj; dsimp only; rw [hzero k hk hk0 hk1 hkj, mul_zero])
    rw [hthree] at hrel
    simpa only [pow_zero, one_mul, pow_one, E, mul_ite, mul_zero] using hrel
  have htop : weight (S.C ^ j) ≤ weight (A 0) + weight S.C * weight E := by
    have heq : (-S.C) ^ j * A j = -(A 0 + (-S.C) * E) := eq_neg_of_add_eq_zero_right hrelation
    have hwt : weight (S.C ^ j) = weight (A 0 + (-S.C) * E) := by
      rw [← weight_pow_neg_mul_of_weight_one S.C (A j) j hAj1, heq]
      simp only [weight, MvPolynomial.support_neg]
    rw [hwt]
    apply (weight_add_upper _ _).trans
    apply Nat.add_le_add_left
    have hm := weight_mul_le (-S.C) E
    simpa only [weight, support_neg] using hm
  have hcost0 : Arithmetic.aggregateCost n 0 = 1 := by simp [Arithmetic.aggregateCost]
  have hthree := sum_eq_three_of_vanishing t
    (fun k => Arithmetic.aggregateCost n k * weight (A k)) j h0 hj hj0 hj1
    (by intro k hk hk0 hk1 hkj; dsimp only; rw [hzero k hk hk0 hk1 hkj, weight_zero, mul_zero])
  have hweight : weight (A 0) + Arithmetic.freshCount n * weight E +
      Arithmetic.aggregateCost n j < n := by
    rw [hthree] at hsmall
    dsimp only at hsmall
    rw [hcost0, one_mul, hAj1, mul_one] at hsmall
    rw [Arithmetic.aggregateCost_one] at hsmall
    simpa only [E, apply_ite weight, weight_zero, mul_ite, mul_zero] using hsmall
  have hcore : weight S.C + Arithmetic.freshCount n = n := weight_intervalCore_add_freshCount n c hc
  have hcases' : (n = 26 ∧ j = 3) ∨ (n = 27 ∧ j = 3) ∨ (n = 27 ∧ j = 4) ∨
      (n = 28 ∧ j = 3) ∨ (n = 28 ∧ j = 4) ∨ (n = 40 ∧ j = 3) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] using hcases
  rcases hcases' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hp := hcube (by omega)
    have hd : Arithmetic.freshCount 26 = 3 ∧ Arithmetic.aggregateCost 26 3 = 10 := by
      unfold Arithmetic.aggregateCost; weighted_decide
    rw [hd.1, hd.2] at hweight
    rw [hd.1] at hcore
    change weight (intervalCore 26 c ^ 3) ≤ _ at htop
    nlinarith
  · have hp := hcube (by omega)
    have hd : Arithmetic.freshCount 27 = 3 ∧ Arithmetic.aggregateCost 27 3 = 10 := by
      unfold Arithmetic.aggregateCost; weighted_decide
    rw [hd.1, hd.2] at hweight
    rw [hd.1] at hcore
    change weight (intervalCore 27 c ^ 3) ≤ _ at htop
    nlinarith
  · have hp := hquartic (by omega)
    have hz := hEzero (by omega)
    rw [hz, weight_zero, mul_zero, add_zero] at hweight htop
    have hd : Arithmetic.aggregateCost 27 4 = 15 := by unfold Arithmetic.aggregateCost; weighted_decide
    rw [hd] at hweight
    change weight (intervalCore 27 c ^ 4) ≤ _ at htop
    omega
  · have hp := hcube (by omega)
    have hd : Arithmetic.freshCount 28 = 3 ∧ Arithmetic.aggregateCost 28 3 = 10 := by
      unfold Arithmetic.aggregateCost; weighted_decide
    rw [hd.1, hd.2] at hweight
    rw [hd.1] at hcore
    change weight (intervalCore 28 c ^ 3) ≤ _ at htop
    nlinarith
  · have hp := hquartic (by omega)
    have hz := hEzero (by omega)
    rw [hz, weight_zero, mul_zero, add_zero] at hweight htop
    have hd : Arithmetic.aggregateCost 28 4 = 15 := by unfold Arithmetic.aggregateCost; weighted_decide
    rw [hd] at hweight
    change weight (intervalCore 28 c ^ 4) ≤ _ at htop
    omega
  · have hp := hcube40 rfl
    have hz := hEzero (by omega)
    rw [hz, weight_zero, mul_zero, add_zero] at hweight htop
    change weight (intervalCore 40 c ^ 3) ≤ _ at htop
    omega

end WeightedPilz

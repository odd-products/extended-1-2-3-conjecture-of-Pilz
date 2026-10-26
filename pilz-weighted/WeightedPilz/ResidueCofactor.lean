import WeightedPilz.FiniteResidueFormula

/-! Bounded aggregate cofactors for the chosen finite-residue minimum. -/

noncomputable section

namespace WeightedPilz

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K] [DecidableEq σ]

namespace FreshData

/-- A base-only residue relation has an explicit cofactor with aggregate
exponents strictly below `p-1`, hence cofactor degree at most `p-2`. -/
theorem bounded_cofactor_of_residue_relation (S : FreshData σ K) (p : ℕ)
    (B : ℕ → MvPolynomial σ K) (hbase : ∀ j < p, S.BaseOnly (B j))
    (hrelation : (∑ j ∈ Finset.range p, (-S.C) ^ j * B j) = 0) :
    ∃ D : ℕ → MvPolynomial σ K, (∀ k, S.BaseOnly (D k)) ∧
      (∑ j ∈ Finset.range p, S.freshSum ^ j * B j) =
        S.F * (∑ k ∈ Finset.range (p - 1), S.freshSum ^ k * D k) := by
  classical
  let D := fun k => ∑ j ∈ Finset.range p,
    if k < j then (-S.C) ^ (j - 1 - k) * B j else 0
  have hD : ∀ k, S.BaseOnly (D k) := by
    intro k z hz d hd
    obtain ⟨j, hj, hdj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
    by_cases hkj : k < j
    · simp only [if_pos hkj] at hdj
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hdj)
      have hneg : ∀ a ∈ (-S.C).support, a z = 0 := by
        intro a ha
        rw [support_neg] at ha
        exact S.independent z hz a ha
      have haz := support_pow_zero_at z (-S.C) hneg (j - 1 - k) a ha
      simp [Finsupp.add_apply, haz, hbase j (Finset.mem_range.mp hj) z hz b hb]
    · simp [hkj] at hdj
  have hswap : (∑ k ∈ Finset.range (p - 1), S.freshSum ^ k * D k) =
      ∑ j ∈ Finset.range p,
        (∑ k ∈ Finset.range j, S.freshSum ^ k * (-S.C) ^ (j - 1 - k)) * B j := by
    simp_rw [D, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    have hjle : j ≤ p - 1 := by have := Finset.mem_range.mp hj; omega
    have hsub : Finset.range j ⊆ Finset.range (p - 1) := Finset.range_mono hjle
    calc
      _ = ∑ k ∈ Finset.range j,
          S.freshSum ^ k * (if k < j then (-S.C) ^ (j - 1 - k) * B j else 0) := by
        symm
        apply Finset.sum_subset hsub
        intro k hk hknot
        have hnot : ¬ k < j := fun h => hknot (Finset.mem_range.mpr h)
        simp [hnot]
      _ = (∑ k ∈ Finset.range j, S.freshSum ^ k * (-S.C) ^ (j - 1 - k)) * B j := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        simp [Finset.mem_range.mp hk, mul_assoc]
  refine ⟨D, hD, ?_⟩
  symm
  rw [hswap, Finset.mul_sum]
  calc
    _ = ∑ j ∈ Finset.range p, (S.freshSum ^ j - (-S.C) ^ j) * B j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← mul_assoc]
      congr 1
      simpa only [F, sub_neg_eq_add, add_comm] using
        (Commute.all S.freshSum (-S.C)).mul_geom_sum₂ j
    _ = ∑ j ∈ Finset.range p, S.freshSum ^ j * B j := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, hrelation, sub_zero]

/-- A chosen minimum has both a base-only output expansion below degree `p`
and a base-only cofactor expansion below degree `p-1`. -/
theorem exists_minimum_bounded_aggregate_cofactor (S : FreshData σ K) (p : ℕ)
    [Fact p.Prime] [CharP K p]
    (hcapacity : ∀ j, 0 < j → j < p → residueSigma p (S.C ^ j) ≤
      (S.vars.card + j - 1).choose j) :
    ∃ (B D : ℕ → MvPolynomial σ K),
      S.AdmissibleResidueRows p B ∧ (∀ k, S.BaseOnly (D k)) ∧
      (∑ k ∈ Finset.range (p - 1), S.freshSum ^ k * D k) ≠ 0 ∧
      (∑ j ∈ Finset.range p, S.freshSum ^ j * B j) =
        S.F * (∑ k ∈ Finset.range (p - 1), S.freshSum ^ k * D k) ∧
      weight (S.F * (∑ k ∈ Finset.range (p - 1), S.freshSum ^ k * D k)) = distance S.F := by
  obtain ⟨B, hB, hcost⟩ := S.exists_minimizing_residue_rows p hcapacity
  obtain ⟨D, hD, hfactor⟩ := S.bounded_cofactor_of_residue_relation p B hB.1 hB.2.2
  have hpowers : ∀ j < p, S.PowersInFresh p (B j) :=
    fun j hj => S.baseOnly_powersInFresh p _ (hB.1 j hj)
  have hGne := S.aggregate_nonzero_of_nonzero_row p B hpowers hB.2.1
  refine ⟨B, D, hB, hD, ?_, hfactor, ?_⟩
  · intro hz
    apply hGne
    rw [hfactor, hz, mul_zero]
  · rw [← hfactor, S.aggregate_weight_eq_cost p B hpowers, hcost]

end FreshData

end WeightedPilz

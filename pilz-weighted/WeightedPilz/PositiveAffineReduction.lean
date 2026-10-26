import WeightedPilz.QuadraticAggregate
import WeightedPilz.FiniteResidueFormula

/-! Chosen affine representatives in positive characteristic. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [DecidableEq σ] [Field K]
namespace FreshData

theorem affine_counterexample_of_finite_residue (S : FreshData σ K) (p N : ℕ)
    [Fact p.Prime] [CharP K p]
    (hcapacity : ∀ j, 0 < j → j < p → residueSigma p (S.C ^ j) ≤
      (S.vars.card + j - 1).choose j)
    (hdegree : ∀ j, 3 ≤ j → N ≤ (S.vars.card + j - 1).choose j)
    (hcounter : ∃ H : MvPolynomial σ K, H ≠ 0 ∧ weight (S.F * H) < N) :
    ∃ D B : MvPolynomial σ K, S.BaseOnly D ∧ S.BaseOnly B ∧
      D + S.freshSum * B ≠ 0 ∧ weight (S.F * (D + S.freshSum * B)) < N := by
  obtain ⟨H, hH, hshort⟩ := hcounter
  obtain ⟨A, hA, hmin⟩ := S.exists_minimizing_residue_rows p hcapacity
  have hpowers : ∀ j < p, S.PowersInFresh p (A j) :=
    fun j hj => S.baseOnly_powersInFresh p _ (hA.1 j hj)
  have hne := S.aggregate_nonzero_of_nonzero_row p A hpowers hA.2.1
  have hdiv := aggregate_replacement_dvd (Finset.range p) id A S.C S.freshSum
  simp only [id_eq, hA.2.2, sub_zero] at hdiv
  have hGshort : weight (∑ j ∈ Finset.range p, S.freshSum ^ j * A j) < N := by
    rw [S.aggregate_weight_eq_cost p A hpowers, hmin]
    exact (distance_le_weight_mul S.F H hH).trans_lt hshort
  have hbase : ∀ j ∈ Finset.range p, S.BaseOnly (A j) :=
    fun j hj => hA.1 j (Finset.mem_range.mp hj)
  have hhigh := S.higher_rows_zero_of_short N (Finset.range p) A hbase hGshort (by
    intro j hj hj3 hnonzero
    have hjp := Finset.mem_range.mp hj
    rw [S.weight_freshSum_pow_mul_lt_char p j (A j) hjp (hpowers j hjp)]
    exact (hdegree j hj3).trans (Nat.le_mul_of_pos_right _ (weight_pos hnonzero)))
  obtain ⟨D, B, hDb, hBb, hDB, hfactor⟩ :=
    S.affine_cofactor_of_quadratic_rows (Finset.range p) A hbase hhigh hne hdiv
  exact ⟨D, B, hDb, hBb, hDB, hfactor ▸ hGshort⟩

/-- In characteristic two the chosen finite-residue representative already
has a cofactor independent of all the fresh variables. -/
theorem base_counterexample_charTwo [CharP K 2] (S : FreshData σ K) (N : ℕ)
    (hcapacity : residueSigma 2 S.C ≤ S.vars.card)
    (hcounter : ∃ H : MvPolynomial σ K, H ≠ 0 ∧ weight (S.F * H) < N) :
    ∃ D : MvPolynomial σ K, D ≠ 0 ∧ S.BaseOnly D ∧ weight (S.F * D) < N := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨H, hH, hshort⟩ := hcounter
  have hcap : ∀ j, 0 < j → j < 2 → residueSigma 2 (S.C ^ j) ≤
      (S.vars.card + j - 1).choose j := by
    intro j hj hj2
    have hj1 : j = 1 := by omega
    simpa [hj1] using hcapacity
  obtain ⟨A, hA, hmin⟩ := S.exists_minimizing_residue_rows 2 hcap
  have hpowers : ∀ j < 2, S.PowersInFresh 2 (A j) :=
    fun j hj => S.baseOnly_powersInFresh 2 _ (hA.1 j hj)
  have hne := S.aggregate_nonzero_of_nonzero_row 2 A hpowers hA.2.1
  have hrel : A 0 = S.C * A 1 := by
    have h := hA.2.2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, one_mul, pow_one, neg_mul] at h
    exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)
  have hfactor : (∑ j ∈ Finset.range 2, S.freshSum ^ j * A j) = S.F * A 1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, one_mul, pow_one]
    rw [hrel, F, add_mul]
  refine ⟨A 1, ?_, hA.1 1 (by decide), ?_⟩
  · intro hz
    apply hne
    rw [hfactor, hz, mul_zero]
  · rw [← hfactor, S.aggregate_weight_eq_cost 2 A hpowers, hmin]
    exact (distance_le_weight_mul S.F H hH).trans_lt hshort

end FreshData
end WeightedPilz

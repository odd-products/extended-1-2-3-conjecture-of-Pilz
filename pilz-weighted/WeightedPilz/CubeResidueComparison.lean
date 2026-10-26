import WeightedPilz.FullResidueDescent
import WeightedPilz.QuadraticAggregate

/-! Transfer the ordinary affine lower bound to coefficients containing fresh
cubes, and record the one-correction-class contradiction. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [Field K] [DecidableEq σ]
namespace FreshData

theorem ResidueCapacityWitness.remainder_ne_zero (S : FreshData σ K) {p N : ℕ}
    (W : S.ResidueCapacityWitness p N) : S.F * W.H - S.correction p W.A ≠ 0 := by
  intro hz
  have heq : S.F * W.H = S.correction p W.A := sub_eq_zero.mp hz
  have hU : S.correction p W.A ≠ 0 := heq ▸ mul_ne_zero S.F_ne_zero W.cofactor_ne_zero
  obtain ⟨α, hα⟩ := exists_nonzero_residuePart p (S.correction p W.A) hU
  have hlo := W.correction_class_cost α (mem_residueIndices_of_part_ne_zero p _ hα)
  have hbound := hlo.trans (weight_residuePart_le p (S.correction p W.A) α)
  rw [← heq] at hbound
  exact Nat.not_lt_of_ge hbound W.short

theorem ResidueCapacityWitness.contradiction_of_one_class (S : FreshData σ K) {p N : ℕ}
    (W : S.ResidueCapacityWitness p N)
    (hcard : (residueIndices p (S.correction p W.A)).card ≤ 1)
    (hV : N ≤ weight (S.F * W.H - S.correction p W.A))
    (hVM : 2 * S.comparisonCapacity p W.A ≤ weight (S.F * W.H - S.correction p W.A)) : False := by
  have hcap := W.uniform_capacity_gain
  have hshort := W.short
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with hz | ho
  · rw [hz] at hcap
    simp only [zero_mul, mul_zero, add_zero] at hcap
    omega
  · rw [ho] at hcap
    simp only [one_mul, mul_one] at hcap
    omega

/-- A nonzero three-row residue relation has a nonzero base-only affine
slice whose expanded weight does not increase. -/
theorem three_residue_rows_lower [CharP K 3] (S : FreshData σ K) (N : ℕ)
    (hlower : ∀ D B : MvPolynomial σ K, S.BaseOnly D → S.BaseOnly B →
      D + S.freshSum * B ≠ 0 → N ≤ weight (S.F * (D + S.freshSum * B)))
    (A : ℕ → MvPolynomial σ K) (hA : ∀ j < 3, S.PowersInFresh 3 (A j))
    (hne : (∑ j ∈ Finset.range 3, S.freshSum ^ j * A j) ≠ 0)
    (hrel : (∑ j ∈ Finset.range 3, (-S.C) ^ j * A j) = 0) :
    N ≤ weight (∑ j ∈ Finset.range 3, S.freshSum ^ j * A j) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨B, hB, hBn, hBr, hwt⟩ :=
    S.exists_base_rows_of_zero_correction 3 A (S.exists_nonzero_aggregate_row 3 A hne) hrel
  have hBpow : ∀ j < 3, S.PowersInFresh 3 (B j) :=
    fun j _ => S.baseOnly_powersInFresh 3 _ (hB j)
  have hBne := S.aggregate_nonzero_of_nonzero_row 3 B hBpow hBn
  have hdiv := aggregate_replacement_dvd (Finset.range 3) id B S.C S.freshSum
  simp only [id_eq, hBr, sub_zero] at hdiv
  obtain ⟨D, E, hD, hE, hDE, hfactor⟩ :=
    S.affine_cofactor_of_quadratic_rows (Finset.range 3) B (fun j _ => hB j)
      (by intro j hj hj3; have := Finset.mem_range.mp hj; omega) hBne hdiv
  have hlo := hlower D E hD hE hDE
  rw [← hfactor, S.aggregate_weight_eq_cost 3 B hBpow] at hlo
  rw [S.aggregate_weight_eq_cost 3 A hA]
  apply hlo.trans
  exact Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (hwt j))

def cubeComparisonRows (S : FreshData σ K) (A : ℕ → MvPolynomial σ K)
    (j : ℕ) : MvPolynomial σ K :=
  if j = 0 then S.C * A 1 - S.C ^ 2 * A 2 else if j = 1 then A 1 else if j = 2 then A 2 else 0

theorem cubeComparisonRows_relation (S : FreshData σ K) (A : ℕ → MvPolynomial σ K) :
    (∑ j ∈ Finset.range 3, (-S.C) ^ j * S.cubeComparisonRows A j) = 0 := by
  simp [Finset.sum_range_succ, cubeComparisonRows] <;> ring

theorem ResidueCapacityWitness.cube_remainder_eq (S : FreshData σ K) {N : ℕ}
    (W : S.ResidueCapacityWitness 3 N) :
    S.F * W.H - S.correction 3 W.A =
      ∑ j ∈ Finset.range 3, S.freshSum ^ j * S.cubeComparisonRows W.A j := by
  rw [W.residue_expansion]
  simp only [correction, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, one_mul, pow_one]
  simp [cubeComparisonRows]
  ring

theorem cubeComparisonRows_powers (S : FreshData σ K) (A : ℕ → MvPolynomial σ K)
    (hA : ∀ j < 3, S.PowersInFresh 3 (A j)) :
    ∀ j < 3, S.PowersInFresh 3 (S.cubeComparisonRows A j) := by
  intro j hj
  interval_cases j
  · simp only [cubeComparisonRows, ↓reduceIte, sub_eq_add_neg]
    exact ((S.core_powersInFresh 3).mul (hA 1 (by decide))).add
      (((S.core_powersInFresh 3).pow 2).mul (hA 2 (by decide))).neg
  · simpa only [cubeComparisonRows, ↓reduceIte] using hA 1 (by decide)
  · simpa only [cubeComparisonRows, ↓reduceIte] using hA 2 (by decide)

theorem ResidueCapacityWitness.cube_remainder_lower [CharP K 3]
    (S : FreshData σ K) {N : ℕ} (W : S.ResidueCapacityWitness 3 N)
    (hlower : ∀ D B : MvPolynomial σ K, S.BaseOnly D → S.BaseOnly B →
      D + S.freshSum * B ≠ 0 → N ≤ weight (S.F * (D + S.freshSum * B))) :
    N ≤ weight (S.F * W.H - S.correction 3 W.A) := by
  have hne := W.remainder_ne_zero S
  rw [W.cube_remainder_eq S] at hne ⊢
  exact S.three_residue_rows_lower N hlower _
    (S.cubeComparisonRows_powers W.A W.rows_powers) hne (S.cubeComparisonRows_relation W.A)

end FreshData
end WeightedPilz

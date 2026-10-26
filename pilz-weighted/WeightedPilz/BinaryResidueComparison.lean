import WeightedPilz.CubeResidueComparison

/-! The binary comparison and the capacity gates for a chosen residue witness. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [Field K] [DecidableEq σ]
namespace FreshData

theorem positiveResidueCost_two (S : FreshData σ K) (A : ℕ → MvPolynomial σ K) :
    S.positiveResidueCost 2 A = S.vars.card * weight (A 1) := by
  rw [positiveResidueCost, show (Finset.range 2).erase 0 = {1} by decide]
  simp

theorem comparison_two (S : FreshData σ K) (A : ℕ → MvPolynomial σ K) :
    S.comparison 2 A = S.C * A 1 := by
  rw [comparison, show (Finset.range 2).erase 0 = {1} by decide]
  simp

theorem ResidueCapacityWitness.binary_remainder_eq (S : FreshData σ K) {N : ℕ}
    (W : S.ResidueCapacityWitness 2 N) :
    S.F * W.H - S.correction 2 W.A = S.F * W.A 1 := by
  rw [W.residue_expansion]
  simp only [correction, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, one_mul, pow_one, F]
  ring

theorem ResidueCapacityWitness.binary_input_ne_zero (S : FreshData σ K) {N : ℕ}
    (W : S.ResidueCapacityWitness 2 N) : W.A 1 ≠ 0 := by
  intro hz
  have h := W.remainder_ne_zero S
  rw [W.binary_remainder_eq S, hz, mul_zero] at h
  exact h rfl

/-- Exact capacities admit any proved improvement to the uniform comparison
bound, so the two largest parity classes can replace the crude maximum. -/
theorem ResidueCapacityWitness.refined_capacities (S : FreshData σ K) {p N M : ℕ}
    (W : S.ResidueCapacityWitness p N)
    (hM : ∀α∈residueIndices p (S.correction p W.A), residueWeight p (S.comparison p W.A) α ≤ M) :
    (weight (S.F * W.H - S.correction p W.A) +
      (residueIndices p (S.correction p W.A)).card * N ≤
        weight (S.F * W.H) + 2 * (residueIndices p (S.correction p W.A)).card * M) ∧
    ((residueIndices p (S.correction p W.A)).card * (N - M) +
      S.positiveResidueCost p W.A ≤ weight (S.F * W.H)) := by
  have hsum := Finset.sum_le_sum hM
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hsub := Finset.sum_le_sum (fun α hα => Nat.sub_le_sub_left (hM α hα) N)
  simp only [Finset.sum_const, nsmul_eq_mul] at hsub
  constructor
  · exact W.exact_capacity_gain.trans (Nat.add_le_add_left (by nlinarith) _)
  · exact (Nat.add_le_add_right hsub _).trans W.exact_capacity_cost

theorem ResidueCapacityWitness.at_most_one_correction_class (S : FreshData σ K) {p N M : ℕ}
    (W : S.ResidueCapacityWitness p N)
    (hM : ∀α∈residueIndices p (S.correction p W.A), residueWeight p (S.comparison p W.A) α ≤ M)
    (hbudget : 2 * M ≤ N + S.positiveResidueCost p W.A) :
    (residueIndices p (S.correction p W.A)).card ≤ 1 := by
  have hcap := (W.refined_capacities S hM).2
  have hshort := W.short
  by_contra hcard
  have htwo : 2 ≤ (residueIndices p (S.correction p W.A)).card := by omega
  have hmul := Nat.mul_le_mul_right (N - M) htwo
  omega

theorem ResidueCapacityWitness.contradiction_of_half_capacity (S : FreshData σ K) {p N M : ℕ}
    (W : S.ResidueCapacityWitness p N)
    (hM : ∀α∈residueIndices p (S.correction p W.A), residueWeight p (S.comparison p W.A) α ≤ M)
    (hV : N ≤ weight (S.F * W.H - S.correction p W.A)) (hhalf : 2 * M ≤ N) : False := by
  have hcap := (W.refined_capacities S hM).1
  have hshort := W.short
  have hm := Nat.mul_le_mul_left (residueIndices p (S.correction p W.A)).card hhalf
  nlinarith

theorem ResidueCapacityWitness.contradiction_of_one_refined_class (S : FreshData σ K) {p N M : ℕ}
    (W : S.ResidueCapacityWitness p N)
    (hM : ∀α∈residueIndices p (S.correction p W.A), residueWeight p (S.comparison p W.A) α ≤ M)
    (hcard : (residueIndices p (S.correction p W.A)).card ≤ 1)
    (hV : N ≤ weight (S.F * W.H - S.correction p W.A))
    (hVM : 2 * M ≤ weight (S.F * W.H - S.correction p W.A)) : False := by
  have hcap := (W.refined_capacities S hM).1
  have hshort := W.short
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with hz | ho
  · rw [hz] at hcap
    simp only [zero_mul, mul_zero, add_zero] at hcap
    omega
  · rw [ho] at hcap
    simp only [one_mul, mul_one] at hcap
    omega

end FreshData
end WeightedPilz

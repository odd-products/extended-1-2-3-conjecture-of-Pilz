import WeightedPilz.ResidueCofactor
import WeightedPilz.FreshRows

/-! The characteristic-two specialization of the finite-residue minimum. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [Field K] [DecidableEq σ] [CharP K 2]
namespace FreshData

theorem binary_finite_residue_formula (S : FreshData σ K)
    (hcapacity : residueSigma 2 S.C ≤ S.vars.card) :
    IsLeast {n : ℕ | ∃ D : MvPolynomial σ K, D ≠ 0 ∧ S.BaseOnly D ∧
      weight (S.C * D) + S.vars.card * weight D = n} (distance S.F) := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  constructor
  · have hcap : ∀ j, 0 < j → j < 2 → residueSigma 2 (S.C ^ j) ≤
        (S.vars.card + j - 1).choose j := by
      intro j hj hj2
      have hj1 : j = 1 := by omega
      simpa [hj1] using hcapacity
    obtain ⟨B, D, _, hD, hne, _, hweight⟩ :=
      S.exists_minimum_bounded_aggregate_cofactor 2 hcap
    have hsum : (∑ k ∈ Finset.range (2 - 1), S.freshSum ^ k * D k) = D 0 := by simp
    rw [hsum] at hne hweight
    exact ⟨D 0, hne, hD 0, (S.weight_mul_base (D 0) (hD 0)).symm.trans hweight⟩
  · rintro n ⟨D, hD, hbase, rfl⟩
    rw [← S.weight_mul_base D hbase]
    exact distance_le_weight_mul S.F D hD

end FreshData
end WeightedPilz

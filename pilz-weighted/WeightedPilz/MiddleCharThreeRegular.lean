import WeightedPilz.MiddleResidueCapacities
import WeightedPilz.ResidueCofactor
import WeightedPilz.MiddleAffineAll

/-! All ordinary characteristic-three middle cases, with the residue,
cofactor, and affine estimates completely assembled. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K] [CharP K 3]

theorem intervalBound_middle_charThree_regular (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (h27 : n ≠ 27) (h28 : n ≠ 28) : IntervalBound n c := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hnpos : 0 < n := by omega
  have hr : (intervalFreshPrimes n).Nonempty := by
    apply Finset.card_pos.mp
    rw [Pilz.card_freshPrimes]
    exact lt_of_lt_of_le (by decide : 0 < 3) (Arithmetic.middle_fresh_count hn hn')
  let S := intervalFreshData n c hnpos hc hr
  have hcap : ∀ j, 0 < j → j < 3 → residueSigma 3 (S.C ^ j) ≤
      (S.vars.card + j - 1).choose j := by
    intro j hj hj3
    change residueSigma 3 (intervalCore n c ^ j) ≤
      ((intervalFreshPrimes n).card + j - 1).choose j
    rw [Pilz.card_freshPrimes]
    exact intervalCore_middle_cube_capacity n j c hc hn hn' h27 h28 hj hj3
  obtain ⟨B, D, hB, hD, hne, _, hweight⟩ :=
    S.exists_minimum_bounded_aggregate_cofactor 3 hcap
  have hsum : (∑ k ∈ Finset.range (3 - 1), S.freshSum ^ k * D k) =
      D 0 + S.freshSum * D 1 := by simp [Finset.sum_range_succ]
  rw [hsum] at hne hweight
  have h2 : (2 : K) ≠ 0 := by
    intro hz
    have hd := (CharP.cast_eq_zero_iff K 3 2).mp hz
    norm_num at hd
  have hlo := middle_affine_lower_all n c hc hn hn' hr h2 (D 0) (D 1) (hD 0) (hD 1) hne
  change n ≤ weight (S.F * (D 0 + S.freshSum * D 1)) at hlo
  rw [hweight] at hlo
  apply (le_distance_iff (interval n c) n).mp
  rw [distance_interval_eq_freshData n c hnpos hc hr]
  exact hlo

end WeightedPilz

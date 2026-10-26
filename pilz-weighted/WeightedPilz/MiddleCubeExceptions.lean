import WeightedPilz.CubeResidueComparison
import WeightedPilz.MiddleResidueCapacities
import WeightedPilz.MiddleAffineAll
import WeightedPilz.TwoMissingProducts

/-! The two exceptional characteristic-three middle intervals. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K] [CharP K 3]

theorem intervalBound_middle_charThree_exceptional (n : ℕ) (hn : n = 27 ∨ n = 28)
    (c : ℕ → K) (hc : NonzeroWeights n c) : IntervalBound n c := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hn25 : 25 ≤ n := by omega
  have hn66 : n ≤ 66 := by omega
  have hnpos : 0 < n := by omega
  have hrc : Arithmetic.freshCount n = 3 := by rcases hn with rfl | rfl <;> weighted_decide
  have hrcP : Pilz.freshCount n = 3 := hrc
  have hr : (intervalFreshPrimes n).Nonempty := by
    apply Finset.card_pos.mp
    rw [Pilz.card_freshPrimes, hrcP]
    decide
  let S := intervalFreshData n c hnpos hc hr
  have hvars : S.vars.card = 3 := by change (intervalFreshPrimes n).card = 3; rwa [Pilz.card_freshPrimes]
  have hcore : weight S.C + 3 = n := by
    have h := weight_intervalCore_add_freshCount n c hc
    rwa [hrcP] at h
  have h2 : (2 : K) ≠ 0 := by
    intro hz
    have hd := (CharP.cast_eq_zero_iff K 3 2).mp hz
    norm_num at hd
  have hdist : n ≤ distance S.F := by
    by_contra hnot
    obtain ⟨H, hH, hweight⟩ := exists_weight_eq_distance S.F
    have hcounter : ∃ H : Poly K, H ≠ 0 ∧ weight (S.F * H) < n :=
      ⟨H, hH, by rw [hweight]; omega⟩
    obtain ⟨W⟩ := S.residue_capacities 3 n (by rw [hvars]; omega) hcounter
    let u₁ := weight (W.A 1)
    let u₂ := weight (W.A 2)
    let R := 3 * u₁ + 6 * u₂
    let M := 3 * u₁ + 7 * u₂
    have hrange : (Finset.range 3).erase 0 = {1, 2} := by decide
    have hchoose : Nat.choose 4 2 = 6 := by decide
    have hR : S.positiveResidueCost 3 W.A = R := by
      rw [FreshData.positiveResidueCost, hrange]
      norm_num [Finset.sum_pair, hvars, hchoose, R, u₁, u₂]
    have hκ := middle_core_endpoint_distance n c hc hn25 hn66
    have hκbudget : n ≤ S.vars.card * Arithmetic.endpoint n := by
      rw [hvars, ← hrc]
      exact (Arithmetic.middleBasicBudgets hn25 hn66).2.1.le
    obtain ⟨_, _, hu₀, hRbudget⟩ := W.zero_row_budget (Arithmetic.endpoint n) hκ hκbudget
    rw [hR] at hRbudget
    have hbudget15 : n - 1 - Arithmetic.endpoint n = 15 := by
      rcases hn with rfl | rfl <;> weighted_decide
    rw [hbudget15] at hRbudget
    have hu₂ : u₂ ≤ 2 := by dsimp [R] at hRbudget; omega
    have hM : M = R + u₂ := by dsimp [M, R]; omega
    have hMlt : M < n := by omega
    have hc1 : residueSigma 3 S.C ≤ 3 := by
      have h := intervalCore_middle_cube_first_capacity n c hc hn25 hn66
      rwa [hrc] at h
    have hc2 : residueSigma 3 (S.C ^ 2) ≤ 7 := residueSigma_cube_square_27_28 n hn c hc
    have hcap : S.comparisonCapacity 3 W.A ≤ M := by
      rw [FreshData.comparisonCapacity, hrange]
      simp only [Finset.sum_pair (by decide : (1 : ℕ) ≠ 2), pow_one]
      exact Nat.add_le_add (Nat.mul_le_mul_right u₁ hc1) (Nat.mul_le_mul_right u₂ hc2)
    have hV := W.cube_remainder_lower S (fun D B hD hB hDB =>
      middle_affine_lower_all n c hc hn25 hn66 hr h2 D B hD hB hDB)
    have hVweight : weight (S.F * W.H - S.correction 3 W.A) =
        weight (S.C * W.A 1 - S.C ^ 2 * W.A 2) + R := by
      rw [W.cube_remainder_eq S, S.aggregate_weight_eq_cost 3 _
        (S.cubeComparisonRows_powers W.A W.rows_powers)]
      norm_num [FreshData.residueCost, FreshData.cubeComparisonRows, Finset.sum_range_succ,
        hvars, hchoose, R, u₁, u₂, add_assoc]
    have hshort := W.short
    by_cases hu₂zero : u₂ = 0
    · have hU : S.correction 3 W.A = 0 := by
        by_contra hUne
        obtain ⟨α, hα⟩ := exists_nonzero_residuePart 3 (S.correction 3 W.A) hUne
        apply hα
        apply W.protected_class
        rw [hR]
        have hαcap := W.comparison_class_capacity α
        omega
      rw [hU, sub_zero] at hV
      omega
    have hcard : (residueIndices 3 (S.correction 3 W.A)).card ≤ 1 := by
      by_contra hnotcard
      have hcge : 2 ≤ (residueIndices 3 (S.correction 3 W.A)).card := by omega
      have hcost := W.uniform_capacity_cost
      rw [hR] at hcost
      have hsub : n - M ≤ n - S.comparisonCapacity 3 W.A := Nat.sub_le_sub_left hcap n
      have hmul := Nat.mul_le_mul_left (residueIndices 3 (S.correction 3 W.A)).card hsub
      have htwo := Nat.mul_le_mul_right (n - M) hcge
      have hsubeq := Nat.sub_add_cancel hMlt.le
      nlinarith only [hcost, hmul, htwo, hsubeq, hM, hRbudget, hu₂, hshort, hn25]
    have hVM : 2 * M ≤ weight (S.F * W.H - S.correction 3 W.A) := by
      rcases (show u₂ = 1 ∨ u₂ = 2 by omega) with hu₂one | hu₂two
      · have hu₁ : u₁ ≤ 3 := by dsimp [R] at hRbudget; omega
        have hcover := unique_cover_bound_reverse n hn c hc h2 (W.A 2) (W.A 1) hu₂one
        change (Arithmetic.uniqueProducts n).card ≤
          weight (S.C * W.A 1 - S.C ^ 2 * W.A 2) + (weight S.C - 2) * u₁ at hcover
        rcases hn with rfl | rfl
        · rw [Arithmetic.uniqueProducts_card_27] at hcover
          have hcweight : weight S.C = 24 := by omega
          rw [hcweight] at hcover
          dsimp [R, M] at *
          omega
        · rw [Arithmetic.uniqueProducts_card_28] at hcover
          have hcweight : weight S.C = 25 := by omega
          rw [hcweight] at hcover
          dsimp [R, M] at *
          omega
      · have hu₁ : u₁ ≤ 1 := by dsimp [R] at hRbudget; omega
        have hsquare := finite_binomial_square_bounds n (by omega) c hc h2 (W.A 2) hu₂two
        have hsquare44 : 44 ≤ weight (S.C ^ 2 * W.A 2) := by
          rcases hn with rfl | rfl <;> simpa using hsquare
        have hcancel := weight_le_weight_add_add (S.C ^ 2 * W.A 2) (-(S.C * W.A 1))
        have hneg : S.C ^ 2 * W.A 2 + -(S.C * W.A 1) =
            -(S.C * W.A 1 - S.C ^ 2 * W.A 2) := by ring
        rw [hneg] at hcancel
        simp only [weight, support_neg] at hcancel
        change weight (S.C ^ 2 * W.A 2) ≤
          weight (S.C * W.A 1 - S.C ^ 2 * W.A 2) + weight (S.C * W.A 1) at hcancel
        have hmul := weight_mul_le S.C (W.A 1)
        change weight (S.C * W.A 1) ≤ weight S.C * u₁ at hmul
        rcases hn with rfl | rfl
        · have hcweight : weight S.C = 24 := by omega
          rw [hcweight] at hmul
          dsimp [R, M] at *
          omega
        · have hcweight : weight S.C = 25 := by omega
          rw [hcweight] at hmul
          dsimp [R, M] at *
          omega
    exact W.contradiction_of_one_class S hcard hV ((Nat.mul_le_mul_left 2 hcap).trans hVM)
  apply (le_distance_iff (interval n c) n).mp
  rw [distance_interval_eq_freshData n c hnpos hc hr]
  exact hdist

end WeightedPilz

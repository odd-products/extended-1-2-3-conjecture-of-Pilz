import WeightedPilz.BinarySingletonInterval
import WeightedPilz.BinaryIntervalTransfer
import WeightedPilz.BinaryComparisonAll
import WeightedPilz.ParityIntegerBounds
import WeightedPilz.Arithmetic.ParityBudgets
import Mathlib.Tactic.NormNum.NatSqrt

/-! The complete binary middle-range capacity argument, separated from the
finite smooth-core and exceptional four-term inputs. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K] [CharP K 2]

set_option maxHeartbeats 1600000 in
theorem intervalBound_middle_charTwo_of_capacities (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn25 : 25 ≤ n) (hn66 : n ≤ 66)
    (hκ : Arithmetic.binaryKappa n ≤ distance (intervalCore n c))
    (hfour : ∀ H : Poly K, H ≠ 0 → weight H = 4 →
      2 ≤ (residueIndices 2 H).card →
      n ∈ ({27,28,34,35,36,38,39,40,49,50,51} : Finset ℕ) →
      ∃ M : ℕ, (∀α, residueWeight 2 (intervalCore n c * H) α ≤ M) ∧
        2 * M ≤ n + 4 * Arithmetic.freshCount n ∧
        2 * M ≤ weight (interval n c * H)) : IntervalBound n c := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hnpos : 0 < n := by omega
  have hwidth := Arithmetic.binary_width_budgets hn25 hn66
  have hrpos : 0 < Arithmetic.freshCount n := by
    by_contra hz
    have heq : Arithmetic.freshCount n = 0 := by omega
    rw [heq, zero_mul] at hwidth
    omega
  have hr : (intervalFreshPrimes n).Nonempty := by
    apply Finset.card_pos.mp
    rw [Pilz.card_freshPrimes]
    exact hrpos
  let S := intervalFreshData n c hnpos hc hr
  have hvars : S.vars.card = Arithmetic.freshCount n := by
    change (intervalFreshPrimes n).card = _
    exact Pilz.card_freshPrimes n
  have hcore : weight S.C + S.vars.card = n := by
    rw [hvars]
    exact weight_intervalCore_add_freshCount n c hc
  have hdist : n ≤ distance S.F := by
    by_contra hnot
    obtain ⟨P, hP, hPweight⟩ := exists_weight_eq_distance S.F
    have hcounter : ∃ P : Poly K, P ≠ 0 ∧ weight (S.F * P) < n :=
      ⟨P, hP, by rw [hPweight]; omega⟩
    obtain ⟨W⟩ := S.residue_capacities 2 n hcore.ge hcounter
    let D := W.A 1
    let u := weight D
    let H := intervalUnnormalize n c hc D
    have hD : D ≠ 0 := W.binary_input_ne_zero S
    have hH : H ≠ 0 := intervalUnnormalize_ne_zero n c hc D hD
    have hHweight : weight H = u := weight_intervalUnnormalize n c hc D
    have hcost : S.positiveResidueCost 2 W.A = Arithmetic.freshCount n * u := by
      rw [S.positiveResidueCost_two, hvars]
    have hκbudget : n ≤ S.vars.card * Arithmetic.binaryKappa n := by
      rw [hvars]
      exact hwidth.1
    obtain ⟨_, _, hzero, hbudget⟩ := W.zero_row_budget (Arithmetic.binaryKappa n) hκ hκbudget
    rw [hcost] at hbudget
    have huquot : u ≤ (n - 1 - Arithmetic.binaryKappa n) / Arithmetic.freshCount n :=
      (Nat.le_div_iff_mul_le hrpos).mpr (by simpa only [Nat.mul_comm] using hbudget)
    have hu5 : u ≤ 5 := huquot.trans hwidth.2.2
    have hshort := W.short
    have hsplit := W.weight_split
    rw [hcost] at hsplit
    have hκshort : Arithmetic.binaryKappa n + Arithmetic.freshCount n * u < n := by omega
    have hVweight : weight (S.F * W.H - S.correction 2 W.A) =
        weight (interval n c * H) := by
      rw [W.binary_remainder_eq S]
      exact intervalFreshData_mul_unnormalize n c hnpos hc hr D
    have hV : n ≤ weight (S.F * W.H - S.correction 2 W.A) := by
      rw [hVweight]
      exact middle_six_term_bound n c H hc hn25 hn66 hH (by omega)
    have hhalf (M : ℕ)
        (hcap : ∀α, residueWeight 2 (S.comparison 2 W.A) α ≤ M)
        (hm : 2 * M ≤ n) : False :=
      W.contradiction_of_half_capacity S (fun α _ => hcap α) hV hm
    have hone (M : ℕ)
        (hcap : ∀α, residueWeight 2 (S.comparison 2 W.A) α ≤ M)
        (hgate : 2 * M ≤ n + Arithmetic.freshCount n * u)
        (hcomp : 2 * M ≤ weight (interval n c * H)) : False := by
      have hcard := W.at_most_one_correction_class S (fun α _ => hcap α)
        (by rwa [hcost])
      exact W.contradiction_of_one_refined_class S (fun α _ => hcap α) hcard hV
        (by rwa [hVweight])
    by_cases husmall : u ≤ 2
    · have hsigma : residueSigma 2 S.C ≤ Nat.sqrt n := by
        apply residueSigma_le_of_integerSupported 2 n (Nat.sqrt n) (by decide)
          (intervalCore n c) (integerSupported_intervalCore n c hc)
        simpa only [Nat.succ_eq_add_one, pow_two] using Nat.lt_succ_sqrt n
      apply hhalf (Nat.sqrt n * u)
      · intro α
        rw [S.comparison_two]
        exact (residueWeight_mul_le 2 S.C D α).trans (Nat.mul_le_mul_right u hsigma)
      · have hb := (Arithmetic.binary_capacity hn25 hn66).1
        have hm := Nat.mul_le_mul_left (Nat.sqrt n) husmall
        nlinarith only [hb, hm]
    have hu3 : 3 ≤ u := by omega
    by_cases hsingle : (residueIndices 2 D).card ≤ 1
    · exact intervalFreshData_single_class_impossible n hn25 hn66 c hc hr W hu3 hsingle
    have hclasses : 2 ≤ (residueIndices 2 D).card := by omega
    have hHclasses : 2 ≤ (residueIndices 2 H).card := by
      simpa only [H, residueIndices, support_intervalUnnormalize] using hclasses
    let M := (u - 1) * Nat.sqrt n + Nat.sqrt (n / 2)
    have hcap : ∀α, residueWeight 2 (S.comparison 2 W.A) α ≤ M := by
      intro α
      rw [S.comparison_two]
      exact intervalCore_parity_mixed_capacity n c hc D hclasses α
    have hcases : u = 3 ∨ u = 4 ∨ u = 5 := by omega
    rcases hcases with hu | hu | hu
    · by_cases hn26 : 26 ≤ n
      · apply hhalf M hcap
        have hb := (Arithmetic.binary_capacity hn25 hn66).2.1 hn26
        dsimp [M]
        rw [hu]
        omega
      · have hn : n = 25 := by omega
        have hM : M = 13 := by norm_num [M, hu, hn]
        apply hone M hcap
        · rw [hM, hu]
          omega
        · rw [hM]
          rw [hn]
          have hcomp := binary_comparison_25_all c H (by simpa only [hn] using hc)
            hH (hHweight.trans hu)
          omega
    · by_cases hm : 2 * M ≤ n
      · exact hhalf M hcap hm
      · have hex : n ∈ ({27,28,34,35,36,38,39,40,49,50,51} : Finset ℕ) := by
          rw [← Arithmetic.binary_four_term_exceptions]
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_Icc.mpr ⟨hn25, hn66⟩, ?_, ?_⟩
          · rw [hu] at hκshort
            simpa only [Nat.mul_comm] using hκshort
          · dsimp [M] at hm
            rw [hu] at hm
            omega
        obtain ⟨L, hLcap, hLgate, hLcomp⟩ := hfour H hH (hHweight.trans hu) hHclasses hex
        apply hone L
        · intro α
          rw [S.comparison_two]
          change residueWeight 2 (intervalCore n c * D) α ≤ L
          rw [← residueWeight_core_mul_unnormalize n c hc D 2 α]
          exact hLcap α
        · rw [hu]
          simpa only [Nat.mul_comm] using hLgate
        · exact hLcomp
    · have hn : n = 58 := by
        rcases hwidth.2.1 with hsmall | hn
        · omega
        · exact hn
      have hM : M = 33 := by norm_num [M, hu, hn]
      have hr58 : Arithmetic.freshCount 58 = 6 := congrArg Prod.fst Arithmetic.binary_five_term_data
      apply hone M hcap
      · rw [hM, hu, hn, hr58]
        omega
      · rw [hM, hn]
        have hcomp := binary_comparison_58_all c H (by simpa only [hn] using hc)
          hH (hHweight.trans hu)
        omega
  apply (le_distance_iff (interval n c) n).mp
  rw [distance_interval_eq_freshData n c hnpos hc hr]
  exact hdist

end WeightedPilz

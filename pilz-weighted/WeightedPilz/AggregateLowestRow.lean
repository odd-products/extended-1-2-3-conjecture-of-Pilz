import WeightedPilz.AggregateAlgebra
import WeightedPilz.AggregateResidueGrouping
import WeightedPilz.FreshResidueTheorem
import WeightedPilz.FreshCostsExtra
import WeightedPilz.Arithmetic.FreshPureCost

/-! The lowest occupied aggregate row supplies the constant-row residue budget. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K] [DecidableEq σ]

/-- The first nonzero coefficient of a relation at `-C` is divisible by `C`. -/
theorem lowest_relation_coefficient_dvd (C : MvPolynomial σ K) (hC : C ≠ 0)
    (t : Finset ℕ) (A : ℕ → MvPolynomial σ K) (k : ℕ) (hk : k ∈ t)
    (hlow : ∀ j ∈ t, A j ≠ 0 → k ≤ j)
    (hrel : (∑ j ∈ t, (-C) ^ j * A j) = 0) : C ∣ A k := by
  have hfactor : (-C) ^ k * (∑ j ∈ t, (-C) ^ (j - k) * A j) = 0 := by
    calc
      _ = ∑ j ∈ t, (-C) ^ j * A j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hAj : A j = 0
        · simp [hAj]
        · rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (hlow j hj hAj)]
      _ = 0 := hrel
  have hsum : (∑ j ∈ t, (-C) ^ (j - k) * A j) = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (pow_ne_zero k (neg_ne_zero.mpr hC))
  have hrest : C ∣ ∑ j ∈ t.erase k, (-C) ^ (j - k) * A j := by
    apply Finset.dvd_sum
    intro j hj
    by_cases hAj : A j = 0
    · simp [hAj]
    · have hkj : k < j := lt_of_le_of_ne (hlow j (Finset.mem_erase.mp hj).2 hAj)
        (Ne.symm (Finset.mem_erase.mp hj).1)
      exact dvd_mul_of_dvd_left ((dvd_neg.mpr dvd_rfl).pow (by omega : j - k ≠ 0)) _
  have hsplit := Finset.sum_erase_add t (fun j => (-C) ^ (j - k) * A j) hk
  simp only [Nat.sub_self, pow_zero, one_mul] at hsplit
  have hneg : (∑ j ∈ t.erase k, (-C) ^ (j - k) * A j) = -A k := by
    rw [← hsplit] at hsum
    exact eq_neg_of_add_eq_zero_left hsum
  rw [hneg] at hrest
  exact dvd_neg.mp hrest

namespace FreshData

theorem weight_base_row_le_sum (S : FreshData σ K) (t : Finset ℕ)
    (A : ℕ → MvPolynomial σ K) (hA : ∀ j ∈ t, S.BaseOnly (A j))
    {k : ℕ} (hk : k ∈ t) :
    weight (S.freshSum ^ k * A k) ≤ weight (∑ j ∈ t, S.freshSum ^ j * A j) := by
  rw [S.base_rows_weight t A hA]
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (weight (S.freshSum ^ j * A j))) hk

/-- A counterexample below `r * (κ + 1)` must have a nonzero degree-zero row;
that row itself has at least `κ` terms. -/
theorem aggregate_lowest_row_zero (S : FreshData σ K) (t : Finset ℕ)
    (A : ℕ → MvPolynomial σ K) (hA : ∀ j ∈ t, S.BaseOnly (A j))
    (hG : (∑ j ∈ t, S.freshSum ^ j * A j) ≠ 0)
    (hdiv : S.F ∣ ∑ j ∈ t, S.freshSum ^ j * A j)
    (κ N : ℕ) (hκ : κ ≤ distance S.C) (hbudget : N ≤ S.vars.card * (κ + 1))
    (hw : weight (∑ j ∈ t, S.freshSum ^ j * A j) < N) :
    0 ∈ t ∧ A 0 ≠ 0 ∧ κ ≤ weight (A 0) := by
  classical
  have hex : ∃ k, k ∈ t ∧ A k ≠ 0 := by
    obtain ⟨k, hk, hrow⟩ := Finset.exists_ne_zero_of_sum_ne_zero hG
    exact ⟨k, hk, right_ne_zero_of_mul hrow⟩
  let k := Nat.find hex
  have hk : k ∈ t := (Nat.find_spec hex).1
  have hAk : A k ≠ 0 := (Nat.find_spec hex).2
  have hlow : ∀ j ∈ t, A j ≠ 0 → k ≤ j := by
    intro j hj hAj
    exact Nat.find_min' hex ⟨hj, hAj⟩
  have hdvd : S.C ∣ A k := lowest_relation_coefficient_dvd S.C S.C_ne_zero t A k hk hlow
    (S.aggregate_relation_of_dvd t A hA hdiv)
  have hother : ∃ j ∈ t, j ≠ k ∧ A j ≠ 0 := by
    by_contra hnot
    have hsingle : (∑ j ∈ t, (-S.C) ^ j * A j) = (-S.C) ^ k * A k := by
      apply Finset.sum_eq_single k
      · intro j hj hjk
        have hAj : A j = 0 := by
          by_contra hne
          exact hnot ⟨j, hj, hjk, hne⟩
        simp [hAj]
      · exact fun h => (h hk).elim
    have hrel := S.aggregate_relation_of_dvd t A hA hdiv
    rw [hsingle] at hrel
    exact mul_ne_zero (pow_ne_zero k (neg_ne_zero.mpr S.C_ne_zero)) hAk hrel
  have hweightk : κ ≤ weight (A k) := by
    obtain ⟨D, hD⟩ := hdvd
    have hDn : D ≠ 0 := by intro hz; apply hAk; rw [hD, hz, mul_zero]
    rw [hD]
    exact hκ.trans (distance_le_weight_mul S.C D hDn)
  have hkzero : k = 0 := by
    by_contra hkn
    have hpos : 0 < k := Nat.pos_of_ne_zero hkn
    have hcost : S.vars.card * κ ≤ weight (S.freshSum ^ k * A k) := by
      rw [S.weight_freshSum_pow_mul_baseOnly k (A k) (hA k hk)]
      exact Nat.mul_le_mul (S.fresh_card_le_weight_pow hpos) hweightk
    obtain ⟨j, hj, hjk, hAj⟩ := hother
    have hjpos : 0 < j := hpos.trans_le (hlow j hj hAj)
    have hAjweight : 1 ≤ weight (A j) := by
      simpa [weight, Finset.card_pos, MvPolynomial.support_nonempty] using hAj
    have hjcost : S.vars.card ≤ weight (S.freshSum ^ j * A j) := by
      calc
        S.vars.card = S.vars.card * 1 := (mul_one _).symm
        _ ≤ S.vars.card * weight (A j) := Nat.mul_le_mul_left _ hAjweight
        _ ≤ _ := S.fresh_card_mul_weight_le_weight_row hjpos (A j) (hA j hj)
    have hpair : ({k, j} : Finset ℕ) ⊆ t := by
      intro l hl
      rcases (show l = k ∨ l = j from by simpa only [Finset.mem_insert, Finset.mem_singleton] using hl) with rfl | rfl
      · exact hk
      · exact hj
    have htotal : weight (S.freshSum ^ k * A k) + weight (S.freshSum ^ j * A j) ≤
        weight (∑ n ∈ t, S.freshSum ^ n * A n) := by
      rw [S.base_rows_weight t A hA]
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hpair
        (fun n _ _ => Nat.zero_le (weight (S.freshSum ^ n * A n)))
      simpa only [Finset.sum_pair hjk.symm] using hle
    rw [Nat.mul_add, Nat.mul_one] at hbudget
    omega
  simpa only [hkzero] using And.intro hk (And.intro hAk hweightk)

theorem aggregateResidueRow_zero_eq (S : FreshData σ K) (p : ℕ) (t : Finset ℕ)
    (A : ℕ → MvPolynomial σ K) :
    S.aggregateResidueRow p t A 0 =
      ∑ n ∈ t.filter (fun n => n % p = 0), S.freshSum ^ n * A n := by
  unfold aggregateResidueRow
  apply Finset.sum_congr rfl
  intro n hn
  have hmod := (Finset.mem_filter.mp hn).2
  have heq : p * (n / p) = n := by
    simpa only [hmod, zero_add] using Nat.mod_add_div n p
  rw [heq]

theorem weight_constant_le_aggregateResidueRow_zero (S : FreshData σ K)
    (p : ℕ) (t : Finset ℕ) (A : ℕ → MvPolynomial σ K)
    (hA : ∀ n ∈ t, S.BaseOnly (A n)) (hzero : 0 ∈ t) :
    weight (A 0) ≤ weight (S.aggregateResidueRow p t A 0) := by
  rw [S.aggregateResidueRow_zero_eq]
  have hz : 0 ∈ t.filter (fun n => n % p = 0) := by simp [hzero]
  simpa only [pow_zero, one_mul] using S.weight_base_row_le_sum
    (t.filter (fun n => n % p = 0)) A
    (fun n hn => hA n (Finset.mem_filter.mp hn).1) hz

/-- After grouping by characteristic residues, the positive rows use at most
`N - 1 - κ` terms in a putative counterexample of weight below `N`. -/
theorem aggregate_positive_residue_budget (S : FreshData σ K)
    (p : ℕ) [ExpChar K p] (t : Finset ℕ) (A : ℕ → MvPolynomial σ K)
    (hA : ∀ n ∈ t, S.BaseOnly (A n))
    (hG : (∑ n ∈ t, S.freshSum ^ n * A n) ≠ 0)
    (hdiv : S.F ∣ ∑ n ∈ t, S.freshSum ^ n * A n)
    (κ N : ℕ) (hκ : κ ≤ distance S.C) (hbudget : N ≤ S.vars.card * (κ + 1))
    (hw : weight (∑ n ∈ t, S.freshSum ^ n * A n) < N) :
    κ ≤ weight (S.aggregateResidueRow p t A 0) ∧
      (∑ j ∈ (Finset.range p).erase 0,
        weight (S.freshSum ^ j * S.aggregateResidueRow p t A j)) ≤ N - 1 - κ := by
  obtain ⟨hzero, _, hweight⟩ := S.aggregate_lowest_row_zero t A hA hG hdiv κ N hκ hbudget hw
  have hconstant : κ ≤ weight (S.aggregateResidueRow p t A 0) :=
    hweight.trans (S.weight_constant_le_aggregateResidueRow_zero p t A hA hzero)
  refine ⟨hconstant, ?_⟩
  have hgroup : (∑ n ∈ t, S.freshSum ^ n * A n) =
      ∑ j ∈ Finset.range p, S.freshSum ^ j * S.aggregateResidueRow p t A j := by
    convert S.aggregate_residue_grouping p (expChar_pos K p) t A using 1
    apply Finset.sum_congr rfl
    intro n hn
    exact mul_comm _ _
  have htotal : weight (∑ n ∈ t, S.freshSum ^ n * A n) =
      ∑ j ∈ Finset.range p, weight (S.freshSum ^ j * S.aggregateResidueRow p t A j) := by
    rw [hgroup]
    exact S.aggregate_rows_weight p _
      (fun j _ => S.aggregateResidueRow_powersInFresh p t A hA j)
  have hsplit := Finset.sum_erase_add (Finset.range p)
    (fun j => weight (S.freshSum ^ j * S.aggregateResidueRow p t A j))
    (Finset.mem_range.mpr (expChar_pos K p))
  simp only [pow_zero, one_mul] at hsplit
  omega

theorem aggregate_positiveRows_budget (S : FreshData σ K)
    (p : ℕ) [ExpChar K p] (t : Finset ℕ) (A : ℕ → MvPolynomial σ K)
    (hA : ∀ n ∈ t, S.BaseOnly (A n))
    (hG : (∑ n ∈ t, S.freshSum ^ n * A n) ≠ 0)
    (hdiv : S.F ∣ ∑ n ∈ t, S.freshSum ^ n * A n)
    (κ N : ℕ) (hκ : κ ≤ distance S.C) (hbudget : N ≤ S.vars.card * (κ + 1))
    (hw : weight (∑ n ∈ t, S.freshSum ^ n * A n) < N) :
    κ ≤ weight (S.aggregateResidueRow p t A 0) ∧
      weight (S.positiveRows p (S.aggregateResidueRow p t A)) ≤ N - 1 - κ := by
  obtain ⟨hconstant, hbudget'⟩ :=
    S.aggregate_positive_residue_budget p t A hA hG hdiv κ N hκ hbudget hw
  refine ⟨hconstant, ?_⟩
  have hcost : weight (S.positiveRows p (S.aggregateResidueRow p t A)) =
      ∑ j ∈ (Finset.range p).erase 0,
        weight (S.freshSum ^ j * S.aggregateResidueRow p t A j) := by
    unfold positiveRows
    apply weight_sum_of_pairwise_disjoint
    intro i hi j hj hij
    exact S.aggregate_rows_disjoint p i j _ _
      (Finset.mem_range.mp (Finset.mem_erase.mp hi).2)
      (Finset.mem_range.mp (Finset.mem_erase.mp hj).2) hij
      (S.aggregateResidueRow_powersInFresh p t A hA i)
      (S.aggregateResidueRow_powersInFresh p t A hA j)
  rwa [hcost]

end FreshData
end WeightedPilz

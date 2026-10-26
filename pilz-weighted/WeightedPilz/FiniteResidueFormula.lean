import WeightedPilz.CompressedMinimum
import WeightedPilz.FreshResidueTheorem
import WeightedPilz.FiniteResidueSlices
import WeightedPilz.FreshCosts

/-! The finite-residue minimum formula over an arbitrary field. -/

noncomputable section

namespace WeightedPilz

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K] [DecidableEq σ]

namespace FreshData

def residueCost (S : FreshData σ K) (p : ℕ) (B : ℕ → MvPolynomial σ K) : ℕ :=
  ∑ j ∈ Finset.range p, (S.vars.card + j - 1).choose j * weight (B j)

def AdmissibleResidueRows (S : FreshData σ K) (p : ℕ) (B : ℕ → MvPolynomial σ K) : Prop :=
  (∀ j < p, S.BaseOnly (B j)) ∧ (∃ j < p, B j ≠ 0) ∧
    (∑ j ∈ Finset.range p, (-S.C) ^ j * B j) = 0

theorem aggregate_weight_eq_cost (S : FreshData σ K) (p : ℕ)
    [Fact p.Prime] [CharP K p] (A : ℕ → MvPolynomial σ K)
    (hA : ∀ j < p, S.PowersInFresh p (A j)) :
    weight (∑ j ∈ Finset.range p, S.freshSum ^ j * A j) = S.residueCost p A := by
  rw [S.aggregate_rows_weight p A hA]
  apply Finset.sum_congr rfl
  intro j hj
  exact S.weight_freshSum_pow_mul_lt_char p j (A j) (Finset.mem_range.mp hj)
    (hA j (Finset.mem_range.mp hj))

theorem positiveRows_weight_eq_cost (S : FreshData σ K) (p : ℕ)
    [Fact p.Prime] [CharP K p] (A : ℕ → MvPolynomial σ K)
    (hA : ∀ j < p, S.PowersInFresh p (A j)) :
    weight (S.positiveRows p A) =
      ∑ j ∈ (Finset.range p).erase 0, (S.vars.card + j - 1).choose j * weight (A j) := by
  unfold positiveRows
  rw [weight_sum_of_pairwise_disjoint]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjp := Finset.mem_range.mp (Finset.mem_erase.mp hj).2
    exact S.weight_freshSum_pow_mul_lt_char p j (A j) hjp (hA j hjp)
  · intro i hi j hj hij
    have hip := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
    have hjp := Finset.mem_range.mp (Finset.mem_erase.mp hj).2
    exact S.aggregate_rows_disjoint p i j (A i) (A j) hip hjp hij (hA i hip) (hA j hjp)

/-- Actual existence form of the residue capacities: all minimum-width and
compression premises are discharged from the existence of a short multiple. -/
theorem exists_residue_capacity_counterexample (S : FreshData σ K) (p : ℕ)
    [Fact p.Prime] [CharP K p] (N : ℕ)
    (hN : N ≤ weight S.C + S.vars.card)
    (hcounter : ∃ H : MvPolynomial σ K, H ≠ 0 ∧ weight (S.F * H) < N) :
    ∃ (H : MvPolynomial σ K) (A : ℕ → MvPolynomial σ K),
      H ≠ 0 ∧ weight (S.F * H) < N ∧
      S.F * H = ∑ j ∈ Finset.range p, S.freshSum ^ j * A j ∧
      (∀ j < p, S.PowersInFresh p (A j)) ∧
      weight (S.F * H) = weight (A 0) +
        (∑ j ∈ (Finset.range p).erase 0, (S.vars.card + j - 1).choose j * weight (A j)) ∧
      S.F ^ p ∣ S.correction p A ∧
      (∀ α ∈ residueIndices p (S.correction p A), N ≤ residueWeight p (S.correction p A) α) ∧
      (∀ α, residueWeight p (S.comparison p A) α ≤ S.comparisonCapacity p A) ∧
      (weight (S.F * H - S.correction p A) + (residueIndices p (S.correction p A)).card * N ≤
        weight (S.F * H) + 2 * ∑ α ∈ residueIndices p (S.correction p A),
          residueWeight p (S.comparison p A) α) ∧
      ((∑ α ∈ residueIndices p (S.correction p A), (N - residueWeight p (S.comparison p A) α)) +
        (∑ j ∈ (Finset.range p).erase 0, (S.vars.card + j - 1).choose j * weight (A j)) ≤
        weight (S.F * H)) ∧
      (weight (S.F * H - S.correction p A) + (residueIndices p (S.correction p A)).card * N ≤
        weight (S.F * H) + 2 * (residueIndices p (S.correction p A)).card * S.comparisonCapacity p A) ∧
      ((residueIndices p (S.correction p A)).card * (N - S.comparisonCapacity p A) +
        (∑ j ∈ (Finset.range p).erase 0, (S.vars.card + j - 1).choose j * weight (A j)) ≤
        weight (S.F * H)) ∧
      (∀ α, residueWeight p (S.comparison p A) α ≤
        (∑ j ∈ (Finset.range p).erase 0, (S.vars.card + j - 1).choose j * weight (A j)) →
        residuePart p (S.correction p A) α = 0) := by
  classical
  have hp : Nat.Prime p := Fact.out
  have hdis : Disjoint S.C.vars S.vars := by
    apply Finset.disjoint_left.mpr
    intro z hzC hz
    obtain ⟨d, hd, hdz⟩ := (MvPolynomial.mem_vars z).mp hzC
    exact (Finsupp.mem_support_iff.mp hdz) (S.independent z hz d hd)
  obtain ⟨H, A, hH, hshort, hpos, hmin, hG, hA⟩ :=
    S.exists_positive_compressed_minimum p S.C.vars (fun _ h => h) hdis N hN hcounter
  obtain ⟨hw, hpow, hc, hcap, hexact1, hexact2, hfirst, hsecond⟩ :=
    S.residue_capacities_of_compressed_minimum p hp.one_lt S.C.vars hdis H A N
      hH hpos hmin hG hA
  have hR := S.positiveRows_weight_eq_cost p A hA
  refine ⟨H, A, hH, hshort, hG, hA, ?_, hpow, hc, hcap, hexact1, ?_, hfirst, ?_, ?_⟩
  · rwa [hR] at hw
  · rwa [hR] at hexact2
  · rwa [hR] at hsecond
  · intro α hα
    have hparts := S.aggregate_zero_positive_decomposition p hp.pos A
    have hsplit : S.F * H = S.correction p A + S.comparison p A + S.positiveRows p A := by
      rw [hG, hparts.2, hparts.1]
    obtain ⟨hUT, hBT⟩ := S.aggregate_sector_disjoint p A hA
    apply protected_residue_class p N (S.correction p A) (S.comparison p A)
      (S.positiveRows p A) α hUT hBT
    · intro hne
      exact hc α (mem_residueIndices_of_part_ne_zero p _ hne)
    · rwa [← hsplit]
    · rwa [hR]

theorem distance_le_residueCost (S : FreshData σ K) (p : ℕ)
    [Fact p.Prime] [CharP K p] (B : ℕ → MvPolynomial σ K)
    (hB : S.AdmissibleResidueRows p B) : distance S.F ≤ S.residueCost p B := by
  obtain ⟨hbase, hnonzero, hrelation⟩ := hB
  have hpowers : ∀ j < p, S.PowersInFresh p (B j) :=
    fun j hj => S.baseOnly_powersInFresh p (B j) (hbase j hj)
  have hG := S.aggregate_nonzero_of_nonzero_row p B hpowers hnonzero
  have hd := aggregate_replacement_dvd (Finset.range p) id B S.C S.freshSum
  simp only [id_eq, hrelation, sub_zero] at hd
  obtain ⟨H, hH⟩ := hd
  have hHne : H ≠ 0 := by intro hz; apply hG; simpa [hz] using hH
  have hdist := distance_le_weight_mul S.F H hHne
  change (∑ j ∈ Finset.range p, S.freshSum ^ j * B j) = S.F * H at hH
  rw [← hH, S.aggregate_weight_eq_cost p B hpowers] at hdist
  exact hdist

private def trivialResidueRows (S : FreshData σ K) (j : ℕ) : MvPolynomial σ K :=
  if j = 0 then S.C else if j = 1 then 1 else 0

private theorem trivialResidueRows_properties (S : FreshData σ K) (p : ℕ) (hp : 1 < p) :
    S.AdmissibleResidueRows p S.trivialResidueRows ∧
      (∑ j ∈ Finset.range p, S.freshSum ^ j * S.trivialResidueRows j) = S.F := by
  classical
  have h0 : 0 ∈ Finset.range p := Finset.mem_range.mpr (by omega)
  have h1 : 1 ∈ Finset.range p := Finset.mem_range.mpr hp
  have hbase : ∀ j < p, S.BaseOnly (S.trivialResidueRows j) := by
    intro j hj z hz d hd
    by_cases hj0 : j = 0
    · subst j
      exact S.independent z hz d (by simpa [trivialResidueRows] using hd)
    · by_cases hj1 : j = 1
      · have hd0 : d = 0 := by
          simpa only [trivialResidueRows, if_neg hj0, if_pos hj1, one_def,
            support_monomial, if_neg one_ne_zero, Finset.mem_singleton] using hd
        simp [hd0]
      · simp [trivialResidueRows, hj0, hj1] at hd
  have hnonzero : ∃ j < p, S.trivialResidueRows j ≠ 0 := by
    exact ⟨1, hp, by simp [trivialResidueRows]⟩
  have hrelation : (∑ j ∈ Finset.range p, (-S.C) ^ j * S.trivialResidueRows j) = 0 := by
    simp [trivialResidueRows, Finset.sum_ite, show 0 < p by omega, h1]
  refine ⟨⟨hbase, hnonzero, hrelation⟩, ?_⟩
  simp [trivialResidueRows, Finset.sum_ite, show 0 < p by omega, h1, F]

/-- Under the finite-residue capacities, a minimum multiple has a base-only
coefficient representation with aggregate output degree at most `p-1`.
This is an existence statement about a chosen minimum. -/
theorem exists_minimizing_residue_rows (S : FreshData σ K) (p : ℕ)
    [Fact p.Prime] [CharP K p]
    (hcapacity : ∀ j, 0 < j → j < p → residueSigma p (S.C ^ j) ≤
      (S.vars.card + j - 1).choose j) :
    ∃ B : ℕ → MvPolynomial σ K,
      S.AdmissibleResidueRows p B ∧ S.residueCost p B = distance S.F := by
  classical
  have hp : Nat.Prime p := Fact.out
  by_cases heq : distance S.F = weight S.F
  · obtain ⟨hB, houtput⟩ := S.trivialResidueRows_properties p hp.one_lt
    refine ⟨S.trivialResidueRows, hB, ?_⟩
    have hpowers : ∀ j < p, S.PowersInFresh p (S.trivialResidueRows j) :=
      fun j hj => S.baseOnly_powersInFresh p _ (hB.1 j hj)
    rw [← S.aggregate_weight_eq_cost p S.trivialResidueRows hpowers, houtput, heq]
  · have hlt : distance S.F < weight S.F := by
      have hle := distance_le_weight S.F
      omega
    let N := distance S.F + 1
    have hN : N ≤ weight S.C + S.vars.card := by
      rw [S.weight_F] at hlt
      omega
    obtain ⟨D, hD, hDweight⟩ := exists_weight_eq_distance S.F
    have hcounter : ∃ H : MvPolynomial σ K, H ≠ 0 ∧ weight (S.F * H) < N :=
      ⟨D, hD, by rw [hDweight]; exact Nat.lt_succ_self _⟩
    have hdis : Disjoint S.C.vars S.vars := by
      apply Finset.disjoint_left.mpr
      intro z hzC hz
      obtain ⟨d, hd, hdz⟩ := (MvPolynomial.mem_vars z).mp hzC
      exact (Finsupp.mem_support_iff.mp hdz) (S.independent z hz d hd)
    obtain ⟨H, A, hH, hshort, hpos, hmin, hG, hA⟩ :=
      S.exists_positive_compressed_minimum p S.C.vars (fun _ h => h) hdis N hN hcounter
    have hbudget : S.comparisonCapacity p A ≤ weight (S.positiveRows p A) := by
      rw [S.positiveRows_weight_eq_cost p A hA]
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hj0, hjp⟩ := Finset.mem_erase.mp hj
      exact Nat.mul_le_mul_right (weight (A j))
        (hcapacity j (Nat.pos_of_ne_zero hj0) (Finset.mem_range.mp hjp))
    have hzero := S.correction_vanishes_of_capacity_budget p hp.one_lt S.C.vars hdis
      H A N hH hpos hmin hG hA hshort hbudget
    have hGne : (∑ j ∈ Finset.range p, S.freshSum ^ j * A j) ≠ 0 :=
      hG ▸ mul_ne_zero S.F_ne_zero hH
    obtain ⟨B, hbase, hnonzero, hrelation, hweights⟩ :=
      S.exists_base_rows_of_zero_correction p A (S.exists_nonzero_aggregate_row p A hGne) hzero
    have hB : S.AdmissibleResidueRows p B := ⟨fun j _ => hbase j, hnonzero, hrelation⟩
    refine ⟨B, hB, Nat.le_antisymm ?_ (S.distance_le_residueCost p B hB)⟩
    have hcost : S.residueCost p B ≤ S.residueCost p A := by
      apply Finset.sum_le_sum
      intro j hj
      exact Nat.mul_le_mul_left _ (hweights j)
    have hAw : S.residueCost p A = weight (S.F * H) := by
      rw [hG]
      exact (S.aggregate_weight_eq_cost p A hA).symm
    rw [hAw] at hcost
    omega

/-- The manuscript's finite-residue minimum formula, stated as an attained
least element of the exact set of base-only residue-row costs. -/
theorem finite_residue_formula (S : FreshData σ K) (p : ℕ)
    [Fact p.Prime] [CharP K p]
    (hcapacity : ∀ j, 0 < j → j < p → residueSigma p (S.C ^ j) ≤
      (S.vars.card + j - 1).choose j) :
    IsLeast {n : ℕ | ∃ B : ℕ → MvPolynomial σ K,
      S.AdmissibleResidueRows p B ∧ S.residueCost p B = n} (distance S.F) := by
  constructor
  · exact S.exists_minimizing_residue_rows p hcapacity
  · intro n hn
    obtain ⟨B, hB, rfl⟩ := hn
    exact S.distance_le_residueCost p B hB

end FreshData

end WeightedPilz

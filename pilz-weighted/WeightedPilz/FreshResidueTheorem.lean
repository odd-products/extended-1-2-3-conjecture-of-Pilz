import WeightedPilz.FreshResidueWidth

/-!
# Residue capacities of a compressed minimum-width multiple

The compressed input is the output of the separate compression/selection
step. No class-cost, correction factor, or correction-width premise is
assumed here: those are proved from that input.
-/

noncomputable section

namespace WeightedPilz

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K] [DecidableEq σ]

namespace FreshData

def correction (S : FreshData σ K) (p : ℕ) (A : ℕ → MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ j ∈ Finset.range p, (-S.C) ^ j * A j

def positiveRows (S : FreshData σ K) (p : ℕ) (A : ℕ → MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ j ∈ (Finset.range p).erase 0, S.freshSum ^ j * A j

def comparison (S : FreshData σ K) (p : ℕ) (A : ℕ → MvPolynomial σ K) : MvPolynomial σ K :=
  -(∑ j ∈ (Finset.range p).erase 0, (-S.C) ^ j * A j)

def comparisonCapacity (S : FreshData σ K) (p : ℕ) (A : ℕ → MvPolynomial σ K) : ℕ :=
  ∑ j ∈ (Finset.range p).erase 0, residueSigma p (S.C ^ j) * weight (A j)

theorem aggregate_zero_positive_decomposition (S : FreshData σ K) (p : ℕ) (hp : 0 < p)
    (A : ℕ → MvPolynomial σ K) :
    (∑ j ∈ Finset.range p, S.freshSum ^ j * A j) = A 0 + S.positiveRows p A ∧
      S.correction p A + S.comparison p A = A 0 := by
  have h0 : 0 ∈ Finset.range p := Finset.mem_range.mpr hp
  constructor
  · have heq := Finset.sum_erase_add (Finset.range p)
      (fun j => S.freshSum ^ j * A j) h0
    simpa only [pow_zero, one_mul, add_comm, positiveRows] using heq.symm
  · have heq := Finset.sum_erase_add (Finset.range p)
      (fun j => (-S.C) ^ j * A j) h0
    simp only [pow_zero, one_mul] at heq
    unfold correction comparison
    rw [← heq]
    ring

theorem aggregate_comparison_capacity_bound (S : FreshData σ K) (p : ℕ)
    (A : ℕ → MvPolynomial σ K) (α : σ →₀ ℕ) :
    residueWeight p (S.comparison p A) α ≤ S.comparisonCapacity p A :=
  aggregate_comparison_capacity p ((Finset.range p).erase 0) S.C A α

theorem aggregate_sector_disjoint (S : FreshData σ K) (p : ℕ)
    (A : ℕ → MvPolynomial σ K) (hA : ∀ j < p, S.PowersInFresh p (A j)) :
    Disjoint (S.correction p A).support (S.positiveRows p A).support ∧
      Disjoint (S.comparison p A).support (S.positiveRows p A).support := by
  have hindex : ∀ j ∈ (Finset.range p).erase 0, 0 < j ∧ j < p := by
    intro j hj
    obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
    exact ⟨Nat.pos_of_ne_zero hne, Finset.mem_range.mp hj⟩
  have hApos : ∀ j ∈ (Finset.range p).erase 0, S.PowersInFresh p (A j) := by
    intro j hj
    exact hA j (hindex j hj).2
  have hU := S.aggregate_replacement_powersInFresh p (Finset.range p) A
    (fun j hj => hA j (Finset.mem_range.mp hj))
  have hB := (S.aggregate_replacement_powersInFresh p ((Finset.range p).erase 0) A hApos).neg
  exact ⟨S.disjoint_powers_positive_rows p _ _ A hU hindex hApos,
    S.disjoint_powers_positive_rows p _ _ A hB hindex hApos⟩

theorem aggregate_weight_zero_positive (S : FreshData σ K) (p : ℕ) (hp : 0 < p)
    (A : ℕ → MvPolynomial σ K) (hA : ∀ j < p, S.PowersInFresh p (A j)) :
    weight (∑ j ∈ Finset.range p, S.freshSum ^ j * A j) =
      weight (A 0) + weight (S.positiveRows p A) := by
  have hdecomp := (S.aggregate_zero_positive_decomposition p hp A).1
  rw [hdecomp]
  apply weight_add_of_disjoint
  apply S.disjoint_powers_positive_rows p (A 0) _ A (hA 0 hp)
  · intro j hj
    obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
    exact ⟨Nat.pos_of_ne_zero hne, Finset.mem_range.mp hj⟩
  · intro j hj
    exact hA j (Finset.mem_range.mp (Finset.mem_erase.mp hj).2)

/-- Precise and uniform cancellation capacities for the actual compressed
minimum-width input. Expanded fresh cost is `weight (positiveRows ...)`;
the separate multinomial count identifies it with `∑ w_j weight(A_j)`. -/
theorem residue_capacities_of_compressed_minimum (S : FreshData σ K)
    (p : ℕ) [ExpChar K p] (hp : 1 < p)
    (base : Finset σ) (hbase : Disjoint base S.vars)
    (H : MvPolynomial σ K) (A : ℕ → MvPolynomial σ K) (N : ℕ)
    (hH : H ≠ 0) (hpos : 0 < totalWidth base H)
    (hmin : ∀ J : MvPolynomial σ K, J ≠ 0 → totalWidth base J < totalWidth base H →
      N ≤ weight (S.F * J))
    (hG : S.F * H = ∑ j ∈ Finset.range p, S.freshSum ^ j * A j)
    (hA : ∀ j < p, S.PowersInFresh p (A j)) :
    weight (S.F * H) = weight (A 0) + weight (S.positiveRows p A) ∧
    S.F ^ p ∣ S.correction p A ∧
    (∀ α ∈ residueIndices p (S.correction p A), N ≤ residueWeight p (S.correction p A) α) ∧
    (∀ α, residueWeight p (S.comparison p A) α ≤ S.comparisonCapacity p A) ∧
    (weight (S.F * H - S.correction p A) + (residueIndices p (S.correction p A)).card * N ≤
      weight (S.F * H) + 2 * ∑ α ∈ residueIndices p (S.correction p A),
        residueWeight p (S.comparison p A) α) ∧
    ((∑ α ∈ residueIndices p (S.correction p A), (N - residueWeight p (S.comparison p A) α)) +
      weight (S.positiveRows p A) ≤ weight (S.F * H)) ∧
    (weight (S.F * H - S.correction p A) + (residueIndices p (S.correction p A)).card * N ≤
      weight (S.F * H) + 2 * (residueIndices p (S.correction p A)).card * S.comparisonCapacity p A) ∧
    ((residueIndices p (S.correction p A)).card * (N - S.comparisonCapacity p A) +
      weight (S.positiveRows p A) ≤ weight (S.F * H)) := by
  have hp0 : 0 < p := lt_trans Nat.zero_lt_one hp
  have hw : weight (S.F * H) = weight (A 0) + weight (S.positiveRows p A) := by
    rw [hG]
    exact S.aggregate_weight_zero_positive p hp0 A hA
  have hparts := S.aggregate_zero_positive_decomposition p hp0 A
  have hsplit : S.F * H = S.correction p A + S.comparison p A + S.positiveRows p A := by
    rw [hG, hparts.2, hparts.1]
  have hV : S.F * H - S.correction p A = S.comparison p A + S.positiveRows p A := by
    rw [hsplit]
    ring
  obtain ⟨z, hz⟩ := S.nonempty
  have hdiv : S.F ∣ ∑ j ∈ Finset.range p, S.freshSum ^ j * A j := hG ▸ dvd_mul_right S.F H
  have hpow := S.aggregate_correction_frobenius_dvd p 1 z hz (Finset.range p) id A
    (by simpa only [pow_one] using fun j hj => hA j (Finset.mem_range.mp hj) z hz) hdiv
  simp only [pow_one, id_eq] at hpow
  have hc := S.aggregate_correction_residue_cost p hp base hbase H A N hH hpos hmin hG hA
  have hcap := S.aggregate_comparison_capacity_bound p A
  obtain ⟨hUT, hBT⟩ := S.aggregate_sector_disjoint p A hA
  obtain ⟨he1, he2⟩ := residue_descent_capacity p N (S.correction p A) (S.comparison p A)
    (S.positiveRows p A) hUT hBT hc
  obtain ⟨hu1, hu2⟩ := residue_descent_uniform_capacity p N (S.comparisonCapacity p A)
    (S.correction p A) (S.comparison p A) (S.positiveRows p A) hUT hBT hc (fun α _ => hcap α)
  rw [← hsplit] at he1 he2 hu1 hu2
  rw [← hV] at he1 hu1
  exact ⟨hw, hpow, hc, hcap, he1, he2, hu1, hu2⟩

theorem correction_vanishes_of_capacity_budget (S : FreshData σ K)
    (p : ℕ) [ExpChar K p] (hp : 1 < p)
    (base : Finset σ) (hbase : Disjoint base S.vars)
    (H : MvPolynomial σ K) (A : ℕ → MvPolynomial σ K) (N : ℕ)
    (hH : H ≠ 0) (hpos : 0 < totalWidth base H)
    (hmin : ∀ J : MvPolynomial σ K, J ≠ 0 → totalWidth base J < totalWidth base H →
      N ≤ weight (S.F * J))
    (hG : S.F * H = ∑ j ∈ Finset.range p, S.freshSum ^ j * A j)
    (hA : ∀ j < p, S.PowersInFresh p (A j))
    (hshort : weight (S.F * H) < N)
    (hbudget : S.comparisonCapacity p A ≤ weight (S.positiveRows p A)) : S.correction p A = 0 := by
  have hp0 : 0 < p := lt_trans Nat.zero_lt_one hp
  have hparts := S.aggregate_zero_positive_decomposition p hp0 A
  have hsplit : S.F * H = S.correction p A + S.comparison p A + S.positiveRows p A := by
    rw [hG, hparts.2, hparts.1]
  obtain ⟨hUT, hBT⟩ := S.aggregate_sector_disjoint p A hA
  apply correction_eq_zero_of_capacity p N (S.correction p A) (S.comparison p A)
    (S.positiveRows p A) hUT hBT
    (S.aggregate_correction_residue_cost p hp base hbase H A N hH hpos hmin hG hA)
  · rwa [← hsplit]
  · intro α _
    exact (S.aggregate_comparison_capacity_bound p A α).trans hbudget

end FreshData

end WeightedPilz

import WeightedPilz.FreshResidueSectors
import WeightedPilz.FreshResidueCorrection
import WeightedPilz.ResidueDescent

/-! Base-coordinate bounds for the actual aggregate correction. -/

noncomputable section

namespace WeightedPilz

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K] [DecidableEq σ]

namespace FreshData

theorem freshSum_ne_zero (S : FreshData σ K) : S.freshSum ≠ 0 := by
  obtain ⟨z, hz⟩ := S.nonempty
  intro hzero
  have hc := S.coeff_freshSum z
  simp [hzero, hz] at hc

theorem F_ne_zero (S : FreshData σ K) : S.F ≠ 0 := by
  obtain ⟨z, hz⟩ := S.nonempty
  intro hzero
  have hc := S.coeff_F_fresh hz
  simp [hzero] at hc

theorem support_freshSum_zero_at_base (S : FreshData σ K) (i : σ) (hi : i ∉ S.vars) :
    ∀ d ∈ S.freshSum.support, d i = 0 := by
  classical
  intro d hd
  rw [S.support_freshSum] at hd
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hd
  have hzi : z ≠ i := by intro h; subst z; exact hi hz
  simp [hzi]

theorem base_order_F (S : FreshData σ K) (i : σ) (hi : i ∉ S.vars) : orderOf i S.F = 0 := by
  classical
  obtain ⟨z, hz⟩ := S.nonempty
  have ho := orderOf_le_support i (S.fresh_monomial_mem_support_F hz)
  have hzi : z ≠ i := by intro h; subst z; exact hi hz
  simpa [hzi] using ho

theorem core_degree_le_F (S : FreshData σ K) (i : σ) : S.C.degreeOf i ≤ S.F.degreeOf i := by
  classical
  rw [MvPolynomial.degreeOf_le_iff]
  intro d hd
  apply MvPolynomial.monomial_le_degreeOf
  rw [S.support_F]
  exact Finset.mem_union_left _ hd

theorem aggregate_coefficient_base_bounds (S : FreshData σ K) (q : ℕ)
    (A : ℕ → MvPolynomial σ K) (hA : ∀ j < q, S.PowersInFresh q (A j))
    (i : σ) (hi : i ∉ S.vars) {j : ℕ} (hj : j < q)
    {b : σ →₀ ℕ} (hb : b ∈ (A j).support) :
    orderOf i (∑ k ∈ Finset.range q, S.freshSum ^ k * A k) ≤ b i ∧
      b i ≤ (∑ k ∈ Finset.range q, S.freshSum ^ k * A k).degreeOf i := by
  classical
  have hAj : A j ≠ 0 := by intro hzero; simp [hzero] at hb
  have hW : S.freshSum ^ j ≠ 0 := pow_ne_zero j S.freshSum_ne_zero
  have hrow : S.freshSum ^ j * A j ≠ 0 := mul_ne_zero hW hAj
  have hz : ∀ d ∈ (S.freshSum ^ j).support, d i = 0 :=
    support_pow_zero_at i S.freshSum (S.support_freshSum_zero_at_base i hi) j
  have hdegW : (S.freshSum ^ j).degreeOf i = 0 := by
    apply Nat.eq_zero_of_le_zero
    rw [MvPolynomial.degreeOf_le_iff]
    exact fun d hd => Nat.le_of_eq (hz d hd)
  have hordW : orderOf i (S.freshSum ^ j) = 0 := by
    have h := orderOf_le_degreeOf i (S.freshSum ^ j)
    omega
  have hlo : orderOf i (∑ k ∈ Finset.range q, S.freshSum ^ k * A k) ≤
      orderOf i (S.freshSum ^ j * A j) := by
    obtain ⟨d, hd, heq⟩ := exists_support_orderOf i hrow
    exact heq ▸ orderOf_le_support i (S.aggregate_row_mem_support q A hA hj hd)
  have hhi : (S.freshSum ^ j * A j).degreeOf i ≤
      (∑ k ∈ Finset.range q, S.freshSum ^ k * A k).degreeOf i := by
    rw [MvPolynomial.degreeOf_le_iff]
    exact fun d hd => MvPolynomial.monomial_le_degreeOf i
      (S.aggregate_row_mem_support q A hA hj hd)
  rw [orderOf_mul i hW hAj, hordW, zero_add] at hlo
  rw [WeightedPilz.degreeOf_mul i hW hAj, hdegW, zero_add] at hhi
  exact ⟨hlo.trans (orderOf_le_support i hb), (MvPolynomial.monomial_le_degreeOf i hb).trans hhi⟩

theorem aggregate_correction_width (S : FreshData σ K) (q : ℕ)
    (A : ℕ → MvPolynomial σ K) (hA : ∀ j < q, S.PowersInFresh q (A j))
    (i : σ) (hi : i ∉ S.vars)
    (hU : (∑ j ∈ Finset.range q, (-S.C) ^ j * A j) ≠ 0) :
    widthOf i (∑ j ∈ Finset.range q, (-S.C) ^ j * A j) ≤
      widthOf i (∑ j ∈ Finset.range q, S.freshSum ^ j * A j) + (q - 1) * widthOf i S.F := by
  let G := ∑ j ∈ Finset.range q, S.freshSum ^ j * A j
  let U := ∑ j ∈ Finset.range q, (-S.C) ^ j * A j
  have hbounds : ∀ d ∈ U.support,
      orderOf i G ≤ d i ∧ d i ≤ G.degreeOf i + (q - 1) * S.F.degreeOf i := by
    intro d hd
    obtain ⟨j, hj, hdj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hdj)
    have hcoeff := S.aggregate_coefficient_base_bounds q A hA i hi (Finset.mem_range.mp hj) hb
    have haBound : a i ≤ j * S.C.degreeOf i := by
      apply (MvPolynomial.monomial_le_degreeOf i ha).trans
      simpa only [MvPolynomial.degreeOf_neg] using MvPolynomial.degreeOf_pow_le i (-S.C) j
    have hjBound : j ≤ q - 1 := by have := Finset.mem_range.mp hj; omega
    have hprod : j * S.C.degreeOf i ≤ (q - 1) * S.F.degreeOf i :=
      Nat.mul_le_mul hjBound (S.core_degree_le_F i)
    change orderOf i G ≤ a i + b i ∧ a i + b i ≤ G.degreeOf i + _
    change orderOf i G ≤ b i ∧ b i ≤ G.degreeOf i at hcoeff
    constructor <;> omega
  have hord : orderOf i G ≤ orderOf i U := by
    obtain ⟨d, hd, heq⟩ := exists_support_orderOf i hU
    exact heq ▸ (hbounds d hd).1
  have hdeg : U.degreeOf i ≤ G.degreeOf i + (q - 1) * S.F.degreeOf i := by
    rw [MvPolynomial.degreeOf_le_iff]
    exact fun d hd => (hbounds d hd).2
  exact correction_width_bound_of_exponent_bounds q i S.F G U (S.base_order_F i hi) hord hdeg

/-- The class-cost assertion for a compressed minimum-width multiple,
with both the Frobenius factor and its width bounds proved from the rows. -/
theorem aggregate_correction_residue_cost (S : FreshData σ K) (p : ℕ) [ExpChar K p]
    (hp : 1 < p) (base : Finset σ) (hbase : Disjoint base S.vars)
    (H : MvPolynomial σ K) (A : ℕ → MvPolynomial σ K) (N : ℕ)
    (hH : H ≠ 0) (hpos : 0 < totalWidth base H)
    (hmin : ∀ J : MvPolynomial σ K, J ≠ 0 → totalWidth base J < totalWidth base H →
      N ≤ weight (S.F * J))
    (hG : S.F * H = ∑ j ∈ Finset.range p, S.freshSum ^ j * A j)
    (hA : ∀ j < p, S.PowersInFresh p (A j)) :
    ∀ α ∈ residueIndices p (∑ j ∈ Finset.range p, (-S.C) ^ j * A j),
      N ≤ residueWeight p (∑ j ∈ Finset.range p, (-S.C) ^ j * A j) α := by
  classical
  obtain ⟨z, hz⟩ := S.nonempty
  have hdiv : S.F ∣ ∑ j ∈ Finset.range p, S.freshSum ^ j * A j :=
    hG ▸ dvd_mul_right S.F H
  have hpow := S.aggregate_correction_frobenius_dvd p 1 z hz (Finset.range p) id A
    (by simpa only [pow_one] using fun j hj => hA j (Finset.mem_range.mp hj) z hz) hdiv
  simp only [pow_one, id_eq] at hpow
  obtain ⟨E, hE⟩ := hpow
  intro α hα
  have hclass := residuePart_ne_zero_of_mem_indices p _ hα
  have hU : (∑ j ∈ Finset.range p, (-S.C) ^ j * A j) ≠ 0 := by
    intro hzero
    apply hclass
    apply MvPolynomial.ext
    intro d
    simp [coeff_residuePart, hzero]
  have hwidth : ∀ i ∈ base, widthOf i (S.F ^ p ^ 1 * E) ≤
      widthOf i (S.F * H) + (p ^ 1 - 1) * widthOf i S.F := by
    intro i hi
    have hib : i ∉ S.vars := fun his => Finset.disjoint_left.mp hbase hi his
    simpa only [pow_one, ← hE, hG] using S.aggregate_correction_width p A hA i hib hU
  have hc := correction_residue_bound_of_minimal_width p 1 (by simpa using hp)
    base S.F H E α N S.F_ne_zero hH hpos hmin
    (by simpa only [pow_one, ← hE] using hclass) hwidth
  simpa only [residueWeight, pow_one, ← hE] using hc

end FreshData

end WeightedPilz

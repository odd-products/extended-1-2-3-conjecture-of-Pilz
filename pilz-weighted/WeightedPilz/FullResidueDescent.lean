import WeightedPilz.FiniteResidueFormula
import WeightedPilz.AggregateLowestRow
import WeightedPilz.ScalarFrobeniusCorrection

/-! The full residue-capacity theorem, including selection, scalar quotient,
and the constant-row budget, over arbitrary fields of positive characteristic. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K] [DecidableEq σ]

namespace FreshData

def positiveResidueCost (S : FreshData σ K) (p : ℕ)
    (A : ℕ → MvPolynomial σ K) : ℕ :=
  ∑ j ∈ (Finset.range p).erase 0, (S.vars.card + j - 1).choose j * weight (A j)

/-- All conclusions concern the same chosen positive minimum-width multiple.
The scalar source coefficients and quotient are retained as actual witnesses. -/
structure ResidueCapacityWitness (S : FreshData σ K) (p N : ℕ) where
  H : MvPolynomial σ K
  T : Finset ℕ
  B : ℕ → MvPolynomial σ K
  A : ℕ → MvPolynomial σ K
  Q : Polynomial (MvPolynomial σ K)
  cofactor_ne_zero : H ≠ 0
  short : weight (S.F * H) < N
  width_positive : 0 < totalWidth S.C.vars H
  width_minimal : ∀ J : MvPolynomial σ K, J ≠ 0 →
    totalWidth S.C.vars J < totalWidth S.C.vars H → N ≤ weight (S.F * J)
  coefficients_baseOnly : ∀ n, S.BaseOnly (B n)
  scalar_expansion : S.F * H = ∑ n ∈ T, B n * S.freshSum ^ n
  rows_eq : A = S.aggregateResidueRow p T B
  residue_expansion : S.F * H = ∑ j ∈ Finset.range p, S.freshSum ^ j * A j
  rows_powers : ∀ j < p, S.PowersInFresh p (A j)
  weight_split : weight (S.F * H) = weight (A 0) + S.positiveResidueCost p A
  quotient_baseOnly : ∀ k, S.BaseOnly (Q.coeff k)
  correction_factor : S.correction p A = S.F ^ p * Polynomial.eval (S.freshSum ^ p) Q
  correction_dvd : S.F ∣ S.correction p A
  remainder_dvd : S.F ∣ S.F * H - S.correction p A
  correction_class_cost : ∀ α ∈ residueIndices p (S.correction p A),
    N ≤ residueWeight p (S.correction p A) α
  comparison_class_capacity : ∀ α,
    residueWeight p (S.comparison p A) α ≤ S.comparisonCapacity p A
  exact_capacity_gain : weight (S.F * H - S.correction p A) +
    (residueIndices p (S.correction p A)).card * N ≤ weight (S.F * H) +
      2 * ∑ α ∈ residueIndices p (S.correction p A), residueWeight p (S.comparison p A) α
  exact_capacity_cost :
    (∑ α ∈ residueIndices p (S.correction p A), (N - residueWeight p (S.comparison p A) α)) +
      S.positiveResidueCost p A ≤ weight (S.F * H)
  uniform_capacity_gain : weight (S.F * H - S.correction p A) +
    (residueIndices p (S.correction p A)).card * N ≤ weight (S.F * H) +
      2 * (residueIndices p (S.correction p A)).card * S.comparisonCapacity p A
  uniform_capacity_cost : (residueIndices p (S.correction p A)).card *
    (N - S.comparisonCapacity p A) + S.positiveResidueCost p A ≤ weight (S.F * H)
  protected_class : ∀ α, residueWeight p (S.comparison p A) α ≤ S.positiveResidueCost p A →
    residuePart p (S.correction p A) α = 0
  zero_row_budget : ∀ κ, κ ≤ distance S.C → N ≤ S.vars.card * κ →
    0 ∈ T ∧ B 0 ≠ 0 ∧ κ ≤ weight (A 0) ∧ S.positiveResidueCost p A ≤ N - 1 - κ

/-- The residue capacities theorem with all compression, minimum-width,
Frobenius-width, scalar-quotient, and fresh-row premises discharged. -/
theorem residue_capacities (S : FreshData σ K) (p : ℕ)
    [Fact p.Prime] [CharP K p] (N : ℕ)
    (hN : N ≤ weight S.C + S.vars.card)
    (hcounter : ∃ H : MvPolynomial σ K, H ≠ 0 ∧ weight (S.F * H) < N) :
    Nonempty (S.ResidueCapacityWitness p N) := by
  classical
  have hp : Nat.Prime p := Fact.out
  have hdis : Disjoint S.C.vars S.vars := by
    apply Finset.disjoint_left.mpr
    intro z hzC hz
    obtain ⟨d, hd, hdz⟩ := (MvPolynomial.mem_vars z).mp hzC
    exact (Finsupp.mem_support_iff.mp hdz) (S.independent z hz d hd)
  obtain ⟨H, T, B, hH, hshort, hpos, hmin, hB, hscalar⟩ :=
    S.exists_positive_scalar_minimum S.C.vars (fun _ h => h) hdis N hN hcounter
  let A := S.aggregateResidueRow p T B
  have hA : ∀ j < p, S.PowersInFresh p (A j) :=
    fun j _ => S.aggregateResidueRow_powersInFresh p T B (fun n _ => hB n) j
  have hG : S.F * H = ∑ j ∈ Finset.range p, S.freshSum ^ j * A j :=
    hscalar.trans (S.aggregate_residue_grouping p hp.pos T B)
  have hscalar' : (∑ n ∈ T, S.freshSum ^ n * B n) = S.F * H := by
    simpa only [mul_comm] using hscalar.symm
  have hsne : (∑ n ∈ T, S.freshSum ^ n * B n) ≠ 0 :=
    hscalar'.symm ▸ mul_ne_zero S.F_ne_zero hH
  have hsdiv : S.F ∣ ∑ n ∈ T, S.freshSum ^ n * B n := by
    rw [hscalar']
    exact dvd_mul_right _ _
  obtain ⟨Q, hQ, hfactor⟩ :=
    S.exists_scalar_correction_quotient p T B (fun n _ => hB n) hsdiv
  change S.correction p A = S.F ^ p * Polynomial.eval (S.freshSum ^ p) Q at hfactor
  obtain ⟨hw, hpow, hc, hcap, he1, he2, hu1, hu2⟩ :=
    S.residue_capacities_of_compressed_minimum p hp.one_lt S.C.vars hdis H A N
      hH hpos hmin hG hA
  have hR : weight (S.positiveRows p A) = S.positiveResidueCost p A :=
    S.positiveRows_weight_eq_cost p A hA
  rw [hR] at hw he2 hu2
  have hUdiv : S.F ∣ S.correction p A := (dvd_pow_self _ hp.ne_zero).trans hpow
  refine ⟨{
    H := H, T := T, B := B, A := A, Q := Q
    cofactor_ne_zero := hH, short := hshort, width_positive := hpos, width_minimal := hmin
    coefficients_baseOnly := hB, scalar_expansion := hscalar, rows_eq := rfl
    residue_expansion := hG, rows_powers := hA, weight_split := hw
    quotient_baseOnly := hQ, correction_factor := hfactor, correction_dvd := hUdiv
    remainder_dvd := dvd_sub (dvd_mul_right _ _) hUdiv
    correction_class_cost := hc, comparison_class_capacity := hcap
    exact_capacity_gain := he1, exact_capacity_cost := he2
    uniform_capacity_gain := hu1, uniform_capacity_cost := hu2
    protected_class := ?_, zero_row_budget := ?_ }⟩
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
  · intro κ hκ hbudget
    have hbudget' : N ≤ S.vars.card * (κ + 1) :=
      hbudget.trans (Nat.mul_le_mul_left _ (Nat.le_succ κ))
    have hsw : weight (∑ n ∈ T, S.freshSum ^ n * B n) < N := by rwa [hscalar']
    obtain ⟨hzero, hBzero, _⟩ :=
      S.aggregate_lowest_row_zero T B (fun n _ => hB n) hsne hsdiv κ N hκ hbudget' hsw
    obtain ⟨ha0, hcost⟩ :=
      S.aggregate_positiveRows_budget p T B (fun n _ => hB n) hsne hsdiv κ N hκ hbudget' hsw
    change weight (S.positiveRows p A) ≤ N - 1 - κ at hcost
    rw [hR] at hcost
    exact ⟨hzero, hBzero, ha0, hcost⟩

/-- The grouped coefficients are literal scalar polynomials in `Z^p`. -/
theorem ResidueCapacityWitness.row_scalar (S : FreshData σ K) {p N : ℕ}
    (W : S.ResidueCapacityWitness p N) (j : ℕ) :
    W.A j = ∑ n ∈ W.T.filter (fun n => n % p = j),
      (S.freshSum ^ p) ^ (n / p) * W.B n := by
  rw [W.rows_eq]
  simp only [aggregateResidueRow, pow_mul]

end FreshData
end WeightedPilz

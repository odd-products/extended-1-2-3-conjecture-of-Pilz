import WeightedPilz.FreshCosts
import WeightedPilz.ScalarCompression
import WeightedPilz.FreshRows
import WeightedPilz.FreshResidueWidth

/-! Scalar aggregate evaluation, homogeneous rows, and chosen minimum multiples. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [DecidableEq σ] [Field K]
namespace FreshData

theorem BaseOnly.add {S : FreshData σ K} {P Q : MvPolynomial σ K}
    (hP : S.BaseOnly P) (hQ : S.BaseOnly Q) : S.BaseOnly (P + Q) := by
  intro z hz d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
  · exact hP z hz d hd
  · exact hQ z hz d hd

theorem BaseOnly.neg {S : FreshData σ K} {P : MvPolynomial σ K}
    (hP : S.BaseOnly P) : S.BaseOnly (-P) := by
  intro z hz d hd
  rw [support_neg] at hd
  exact hP z hz d hd

theorem BaseOnly.sub {S : FreshData σ K} {P Q : MvPolynomial σ K}
    (hP : S.BaseOnly P) (hQ : S.BaseOnly Q) : S.BaseOnly (P - Q) := by
  simpa only [sub_eq_add_neg] using hP.add hQ.neg

def aggregateEvaluation (S : FreshData σ K) (z : σ) :
    MvPolynomial σ K →+* MvPolynomial σ K :=
  eval₂Hom MvPolynomial.C (fun i => if i = z then -S.C else if i ∈ S.vars then 0 else X i)

theorem aggregateEvaluation_base (S : FreshData σ K) (z : σ) (hz : z ∈ S.vars)
    (P : MvPolynomial σ K) (hP : S.BaseOnly P) : S.aggregateEvaluation z P = P := by
  change S.aggregateEvaluation z P = (RingHom.id _) P
  apply MvPolynomial.hom_congr_vars
  · ext c
    simp [aggregateEvaluation]
  · intro i hi _
    have his : i ∉ S.vars := by
      intro his
      obtain ⟨d, hd, hdi⟩ := (MvPolynomial.mem_vars i).mp hi
      exact (Finsupp.mem_support_iff.mp hdi) (hP i his d hd)
    have hiz : i ≠ z := fun h => his (h ▸ hz)
    simp [aggregateEvaluation, hiz, his]
  · rfl

theorem aggregateEvaluation_freshSum (S : FreshData σ K) (z : σ) (hz : z ∈ S.vars) :
    S.aggregateEvaluation z S.freshSum = -S.C := by
  rw [freshSum, map_sum]
  calc
    (∑ i ∈ S.vars, S.aggregateEvaluation z (X i)) =
        ∑ i ∈ S.vars, if i = z then -S.C else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [aggregateEvaluation, hi]
    _ = -S.C := by simp [hz]

theorem aggregateEvaluation_F (S : FreshData σ K) (z : σ) (hz : z ∈ S.vars) :
    S.aggregateEvaluation z S.F = 0 := by
  rw [F, map_add, S.aggregateEvaluation_base z hz S.C S.independent,
    S.aggregateEvaluation_freshSum z hz, add_neg_cancel]

theorem aggregate_relation_of_dvd (S : FreshData σ K) (t : Finset ℕ)
    (A : ℕ → MvPolynomial σ K) (hA : ∀ j ∈ t, S.BaseOnly (A j))
    (hdiv : S.F ∣ ∑ j ∈ t, S.freshSum ^ j * A j) :
    (∑ j ∈ t, (-S.C) ^ j * A j) = 0 := by
  obtain ⟨z, hz⟩ := S.nonempty
  obtain ⟨H, hH⟩ := hdiv
  have heq := congrArg (S.aggregateEvaluation z) hH
  rw [map_mul, S.aggregateEvaluation_F z hz, zero_mul, map_sum] at heq
  convert heq using 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul, map_pow, S.aggregateEvaluation_freshSum z hz,
    S.aggregateEvaluation_base z hz (A j) (hA j hj)]

theorem base_row_degree (S : FreshData σ K) (j : ℕ) (A : MvPolynomial σ K)
    (hA : S.BaseOnly A) :
    ∀ d ∈ (S.freshSum ^ j * A).support, freshExponentDegree S.vars d = j := by
  have hb : ∀ d ∈ A.support, freshExponentDegree S.vars d = 0 := by
    intro d hd
    exact Finset.sum_eq_zero (fun i hi => hA i hi d hd)
  simpa only [add_zero] using support_mul_fresh_degree S.vars (S.freshSum ^ j) A j 0
    (S.support_freshSum_pow_degree j) hb

theorem base_rows_disjoint (S : FreshData σ K) (i j : ℕ) (A B : MvPolynomial σ K)
    (hij : i ≠ j) (hA : S.BaseOnly A) (hB : S.BaseOnly B) :
    Disjoint (S.freshSum ^ i * A).support (S.freshSum ^ j * B).support := by
  apply Finset.disjoint_left.mpr
  intro d hd he
  exact hij ((S.base_row_degree i A hA d hd).symm.trans (S.base_row_degree j B hB d he))

theorem base_rows_weight (S : FreshData σ K) (t : Finset ℕ)
    (A : ℕ → MvPolynomial σ K) (hA : ∀ j ∈ t, S.BaseOnly (A j)) :
    weight (∑ j ∈ t, S.freshSum ^ j * A j) =
      ∑ j ∈ t, weight (S.freshSum ^ j * A j) := by
  apply weight_sum_of_pairwise_disjoint
  intro i hi j hj hij
  exact S.base_rows_disjoint i j _ _ hij (hA i hi) (hA j hj)

theorem weight_base_row_charZero [CharZero K] (S : FreshData σ K) (j : ℕ)
    (A : MvPolynomial σ K) (hA : S.BaseOnly A) :
    weight (S.freshSum ^ j * A) = (S.vars.card + j - 1).choose j * weight A := by
  apply S.weight_freshSum_pow_mul_of_factorial_ne_zero (j + 1) j A (by omega)
  · exact_mod_cast Nat.factorial_ne_zero j
  · intro z hz d hd
    rw [hA z hz d hd]
    exact dvd_zero _

theorem exists_scalar_minimum (S : FreshData σ K) :
    ∃ (t : Finset ℕ) (A : ℕ → MvPolynomial σ K),
      (∀ j ∈ t, S.BaseOnly (A j)) ∧
      (∑ j ∈ t, S.freshSum ^ j * A j) ≠ 0 ∧
      S.F ∣ (∑ j ∈ t, S.freshSum ^ j * A j) ∧
      weight (∑ j ∈ t, S.freshSum ^ j * A j) = distance S.F := by
  obtain ⟨H, hH, hweight⟩ := exists_weight_eq_distance S.F
  have hind : ∀ i ∈ S.vars, i ∉ S.C.vars := by
    intro i hi hmem
    obtain ⟨d, hd, hdi⟩ := (MvPolynomial.mem_vars i).mp hmem
    exact (Finsupp.mem_support_iff.mp hdi) (S.independent i hi d hd)
  obtain ⟨G, hG, hdiv, hw, _, _, t, A, hA, hGA⟩ :=
    Compression.scalar_support_compression S.vars S.nonempty S.C hind (S.F * H)
      (mul_ne_zero S.F_ne_zero hH) (dvd_mul_right S.F H)
  have hGArev : G = ∑ j ∈ t, S.freshSum ^ j * A j := by
    simpa only [freshSum, mul_comm] using hGA
  have hbase : ∀ j ∈ t, S.BaseOnly (A j) := by
    intro j hj z hz d hd
    exact MvPolynomial.mem_support_notMem_vars_zero hd (hA j z hz)
  refine ⟨t, A, hbase, hGArev ▸ hG, hGArev ▸ hdiv, ?_⟩
  rw [← hGArev]
  apply Nat.le_antisymm (hw.trans_eq hweight)
  obtain ⟨J, hJ⟩ := hdiv
  have hJn : J ≠ 0 := by intro hz; apply hG; rw [hJ, hz, mul_zero]
  rw [hJ]
  exact distance_le_weight_mul S.F J hJn

end FreshData
end WeightedPilz

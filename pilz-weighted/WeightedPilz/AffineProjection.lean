import WeightedPilz.VariableSlices
import WeightedPilz.FreshRows

/-! Removal of extra variables from an affine fresh-sum cofactor. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [DecidableEq σ] [Field K]

theorem vars_subset_monomial_mul (a : σ →₀ ℕ) (P : MvPolynomial σ K) :
    P.vars ⊆ (monomial a 1 * P).vars := by
  intro i hi
  obtain ⟨d, hd, hdi⟩ := (MvPolynomial.mem_vars i).mp hi
  apply (MvPolynomial.mem_vars i).mpr
  refine ⟨a + d, ?_, ?_⟩
  · have hs : (monomial a 1 * P).support = P.support.map (addLeftEmbedding a) :=
      AddMonoidAlgebra.support_single_mul P 1 (by simp) a
    rw [hs]
    exact Finset.mem_map.mpr ⟨d, hd, rfl⟩
  · apply Finsupp.mem_support_iff.mpr
    have hdpos : 0 < d i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hdi)
    simp only [Finsupp.add_apply]
    omega

theorem outsideSlice_add (T : Set σ) (a : σ →₀ ℕ) (P Q : MvPolynomial σ K) :
    outsideSlice T a (P + Q) = outsideSlice T a P + outsideSlice T a Q := by
  ext d
  simp only [coeff_outsideSlice, coeff_add]
  split_ifs <;> simp

theorem vars_outsideSlice_subset (T : Set σ) (a : σ →₀ ℕ) (P : MvPolynomial σ K) :
    (outsideSlice T a P).vars ⊆ P.vars := by
  intro i hi
  obtain ⟨d, hd, hdi⟩ := (MvPolynomial.mem_vars i).mp hi
  exact (MvPolynomial.mem_vars i).mpr ⟨d, (Finset.mem_filter.mp hd).1, hdi⟩

namespace FreshData

theorem baseOnly_iff_vars_disjoint (S : FreshData σ K) (P : MvPolynomial σ K) :
    S.BaseOnly P ↔ Disjoint P.vars S.vars := by
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro i hi his
    obtain ⟨d, hd, hdi⟩ := (MvPolynomial.mem_vars i).mp hi
    exact (Finsupp.mem_support_iff.mp hdi) (h i his d hd)
  · intro h i hi d hd
    apply MvPolynomial.mem_support_notMem_vars_zero hd
    intro him
    exact Finset.disjoint_left.mp h him hi

theorem vars_freshSum_subset (S : FreshData σ K) : S.freshSum.vars ⊆ S.vars := by
  intro i hi
  obtain ⟨d, hd, hdi⟩ := (MvPolynomial.mem_vars i).mp hi
  rw [S.support_freshSum] at hd
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
  have hij : i = j := by
    by_contra hij
    have hz : (Finsupp.single j 1 : σ →₀ ℕ) i = 0 := Finsupp.single_eq_of_ne hij
    exact (Finsupp.mem_support_iff.mp hdi) hz
  exact hij ▸ hj

/-- Every affine cofactor has a nonzero affine fiber in the chosen variables.
Both base coefficients remain independent of the fresh variables. -/
theorem exists_affine_projection (S : FreshData σ K) (T : Set σ)
    (hCT : (S.C.vars : Set σ) ⊆ T) (hVT : (S.vars : Set σ) ⊆ T)
    (D B : MvPolynomial σ K) (hD : S.BaseOnly D) (hB : S.BaseOnly B)
    (hne : D + S.freshSum * B ≠ 0) :
    ∃ D' B' : MvPolynomial σ K,
      D' + S.freshSum * B' ≠ 0 ∧ (D'.vars : Set σ) ⊆ T ∧
      (B'.vars : Set σ) ⊆ T ∧ S.BaseOnly D' ∧ S.BaseOnly B' ∧
      weight (S.F * (D' + S.freshSum * B')) ≤ weight (S.F * (D + S.freshSum * B)) := by
  have hZT : (S.freshSum.vars : Set σ) ⊆ T := fun _ hi => hVT (S.vars_freshSum_subset hi)
  have hFT : (S.F.vars : Set σ) ⊆ T := by
    intro i hi
    rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset S.C S.freshSum hi) with hi | hi
    · exact hCT hi
    · exact hZT hi
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hne
  let a := outsideExponent T d
  have ha : outsideExponent T a = a := outsideExponent_idempotent T d
  obtain ⟨D', hDf, hDT⟩ := outsideSlice_division T a ha D
  obtain ⟨B', hBf, hBT⟩ := outsideSlice_division T a ha B
  have hDsub : D'.vars ⊆ D.vars := by
    have h := vars_subset_monomial_mul a D'
    rw [← hDf] at h
    exact h.trans (vars_outsideSlice_subset T a D)
  have hBsub : B'.vars ⊆ B.vars := by
    have h := vars_subset_monomial_mul a B'
    rw [← hBf] at h
    exact h.trans (vars_outsideSlice_subset T a B)
  have hDb : S.BaseOnly D' := (S.baseOnly_iff_vars_disjoint D').mpr
    (Disjoint.mono_left hDsub ((S.baseOnly_iff_vars_disjoint D).mp hD))
  have hBb : S.BaseOnly B' := (S.baseOnly_iff_vars_disjoint B').mpr
    (Disjoint.mono_left hBsub ((S.baseOnly_iff_vars_disjoint B).mp hB))
  have hfactor : outsideSlice T a (D + S.freshSum * B) =
      monomial a 1 * (D' + S.freshSum * B') := by
    rw [outsideSlice_add, outsideSlice_mul T a S.freshSum B hZT, hDf, hBf]
    ring
  have hslice : outsideSlice T a (D + S.freshSum * B) ≠ 0 := by
    apply MvPolynomial.support_nonempty.mp
    exact ⟨d, Finset.mem_filter.mpr ⟨hd, rfl⟩⟩
  refine ⟨D', B', ?_, hDT, hBT, hDb, hBb, ?_⟩
  · intro hz
    apply hslice
    rw [hfactor, hz, mul_zero]
  · have h := weight_outsideSlice_le T a (S.F * (D + S.freshSum * B))
    rw [outsideSlice_mul T a S.F _ hFT, hfactor, mul_left_comm,
      weight_monomial_mul] at h
    exact h

end FreshData
end WeightedPilz

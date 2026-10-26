import WeightedPilz.Fresh
import WeightedPilz.Endpoints
import WeightedPilz.VariableSlices

/-! The zero-base-width case of weighted fresh-variable descent. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K] [DecidableEq σ]

private theorem weight_sum_disjoint {ι : Type*} (A : Finset ι)
    (f : ι → MvPolynomial σ K)
    (hdis : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (f i).support (f j).support) :
    weight (∑ i ∈ A, f i) = ∑ i ∈ A, weight (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [weight]
  | @insert i A hi ih =>
    have hdisA : ∀ k ∈ A, ∀ j ∈ A, k ≠ j → Disjoint (f k).support (f j).support :=
      fun k hk j hj hkj => hdis k (Finset.mem_insert_of_mem hk) j
        (Finset.mem_insert_of_mem hj) hkj
    have hdi : Disjoint (f i).support (∑ j ∈ A, f j).support := by
      apply Finset.disjoint_left.mpr
      intro d hdi hds
      obtain ⟨j, hj, hdj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hds)
      exact Finset.disjoint_left.mp (hdis i (Finset.mem_insert_self i A) j
        (Finset.mem_insert_of_mem hj) (fun heq => hi (heq ▸ hj))) hdi hdj
    rw [Finset.sum_insert hi, weight_add_of_disjoint _ _ hdi, ih hdisA,
      Finset.sum_insert hi]

/-- Zero width forces one common exponent in every designated base coordinate. -/
theorem exists_factor_of_totalWidth_zero (B : Finset σ) (H : MvPolynomial σ K)
    (hH : H ≠ 0) (hwidth : totalWidth B H = 0) :
    ∃ (α : σ →₀ ℕ) (D : MvPolynomial σ K), D ≠ 0 ∧
      H = monomial α 1 * D ∧ (∀ i ∈ B, i ∉ D.vars) := by
  let T : Set σ := {i | i ∉ B}
  have hcoord : ∀ i ∈ B, widthOf i H = 0 := by
    intro i hi
    have hle : widthOf i H ≤ totalWidth B H :=
      Finset.single_le_sum (fun k hk => Nat.zero_le (widthOf k H)) hi
    omega
  have hequal : ∀ d ∈ H.support, ∀ e ∈ H.support,
      outsideExponent T d = outsideExponent T e := by
    intro d hd e he
    ext i
    by_cases hi : i ∈ B
    · have hw := hcoord i hi
      have hod := orderOf_le_support i hd
      have hoe := orderOf_le_support i he
      have hdd := monomial_le_degreeOf i hd
      have hed := monomial_le_degreeOf i he
      have horder := orderOf_le_degreeOf i H
      simp only [widthOf] at hw
      simp only [outsideExponent_apply, T, Set.mem_setOf_eq, not_not, if_pos hi]
      omega
    · simp [outsideExponent_apply, T, hi]
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
  let α := outsideExponent T d
  have hα : outsideExponent T α = α := outsideExponent_idempotent T d
  have hslice : outsideSlice T α H = H := by
    ext e
    rw [coeff_outsideSlice]
    by_cases he : e ∈ H.support
    · rw [if_pos (hequal e he d hd)]
    · simp [MvPolynomial.notMem_support_iff.mp he]
  obtain ⟨D, hfactor, hDvars⟩ := outsideSlice_division T α hα H
  have hfactor' : H = monomial α 1 * D := hslice.symm.trans hfactor
  refine ⟨α, D, ?_, hfactor', ?_⟩
  · intro hz
    apply hH
    rw [hfactor', hz, mul_zero]
  · intro i hi himem
    exact hDvars himem hi

namespace FreshData

/-- A multiplier independent of the base variables meets the full weight
bound, by separating its nonconstant core rows from the fresh affine row. -/
theorem weight_mul_base_independent (S : FreshData σ K) (B : Finset σ)
    (hCB : S.C.vars ⊆ B) (hBV : Disjoint B S.vars)
    (H : MvPolynomial σ K) (hH : H ≠ 0) (hHB : ∀ i ∈ B, i ∉ H.vars) :
    weight S.C + S.vars.card ≤ weight (S.F * H) := by
  classical
  let T : Set σ := {i | i ∉ B}
  let A := S.C.support.erase 0
  let L : MvPolynomial σ K := MvPolynomial.C (coeff 0 S.C) + S.freshSum
  let row (d : σ →₀ ℕ) := monomial d (coeff d S.C) * H
  have hHout : ∀ d ∈ H.support, outsideExponent T d = 0 := by
    intro d hd
    ext i
    by_cases hi : i ∈ B
    · simp [outsideExponent_apply, T, hi,
        MvPolynomial.mem_support_notMem_vars_zero hd (hHB i hi)]
    · simp [outsideExponent_apply, T, hi]
  have hCout : ∀ d ∈ S.C.support, outsideExponent T d = d := by
    intro d hd
    ext i
    by_cases hi : i ∈ B
    · simp [outsideExponent_apply, T, hi]
    · have hin : i ∉ S.C.vars := fun hm => hi (hCB hm)
      simp [outsideExponent_apply, T, hi, MvPolynomial.mem_support_notMem_vars_zero hd hin]
  have hrowout : ∀ d ∈ A, ∀ e ∈ (row d).support, outsideExponent T e = d := by
    intro d hd e he
    have hdc := Finset.mem_of_mem_erase hd
    have hc : coeff d S.C ≠ 0 := MvPolynomial.mem_support_iff.mp hdc
    have hs : (row d).support = H.support.map (addLeftEmbedding d) :=
      AddMonoidAlgebra.support_single_mul H (coeff d S.C) (by simp [hc]) d
    rw [hs] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
    change outsideExponent T (d + a) = d
    rw [outsideExponent_add, hCout d hdc, hHout a ha, add_zero]
  have hLind : ∀ i ∈ B, i ∉ L.vars := by
    intro i hi himem
    have hLvars : L.vars ⊆ S.vars := by
      apply (MvPolynomial.vars_add_subset _ _).trans
      intro k hk
      rcases Finset.mem_union.mp hk with hk | hk
      · simpa using hk
      · obtain ⟨d, hd, hkd⟩ := (MvPolynomial.mem_vars k).mp hk
        rw [S.support_freshSum] at hd
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
        have hkj : k = j := by
          by_contra hne
          exact Finsupp.mem_support_iff.mp hkd (by simp [Finsupp.single_apply, hne, Ne.symm hne])
        exact hkj ▸ hj
    exact Finset.disjoint_left.mp hBV hi (hLvars himem)
  have hLHout : ∀ e ∈ (L * H).support, outsideExponent T e = 0 := by
    intro e he
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul L H he)
    rw [outsideExponent_add, hHout b hb, add_zero]
    ext i
    by_cases hi : i ∈ B
    · simp [outsideExponent_apply, T, hi,
        MvPolynomial.mem_support_notMem_vars_zero ha (hLind i hi)]
    · simp [outsideExponent_apply, T, hi]
  have hrows : ∀ d ∈ A, ∀ e ∈ A, d ≠ e → Disjoint (row d).support (row e).support := by
    intro d hd e he hde
    apply Finset.disjoint_left.mpr
    intro a had hae
    exact hde ((hrowout d hd a had).symm.trans (hrowout e he a hae))
  have hrowL : Disjoint (∑ d ∈ A, row d).support (L * H).support := by
    apply Finset.disjoint_left.mpr
    intro e her heL
    obtain ⟨d, hd, hed⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum her)
    exact (Finset.mem_erase.mp hd).1 ((hrowout d hd e hed).symm.trans (hLHout e heL))
  have hcore : S.C = (∑ d ∈ A, monomial d (coeff d S.C)) + MvPolynomial.C (coeff 0 S.C) := by
    calc
      S.C = ∑ d ∈ S.C.support, monomial d (coeff d S.C) := MvPolynomial.as_sum S.C
      _ = _ := by
        by_cases hzero : 0 ∈ S.C.support
        · have hh := Finset.sum_erase_add S.C.support (fun d => monomial d (coeff d S.C)) hzero
          simpa [A] using hh.symm
        · have hc0 : coeff 0 S.C = 0 := MvPolynomial.notMem_support_iff.mp hzero
          simp [A, hzero, hc0]
  have hdecomp : S.F * H = (∑ d ∈ A, row d) + L * H := by
    change (S.C + S.freshSum) * H = _
    conv_lhs => rw [hcore]
    rw [add_assoc, add_mul, Finset.sum_mul]
  have hweight : weight (S.F * H) = A.card * weight H + weight (L * H) := by
    rw [hdecomp, weight_add_of_disjoint _ _ hrowL, weight_sum_disjoint A row hrows]
    congr 1
    calc
      (∑ d ∈ A, weight (row d)) = ∑ d ∈ A, weight H := by
        apply Finset.sum_congr rfl
        intro d hd
        exact weight_scalar_monomial_mul d
          (MvPolynomial.mem_support_iff.mp (Finset.mem_of_mem_erase hd)) H
      _ = A.card * weight H := by simp
  have hHpos : 0 < weight H := by simpa [weight, Finset.card_pos, support_nonempty] using hH
  have hpure : ∀ i ∈ S.vars, ∃ k : ℕ, 0 < k ∧ coeff (Finsupp.single i k) L ≠ 0 := by
    intro i hi
    refine ⟨1, by omega, ?_⟩
    have hzero : Finsupp.single i 1 ≠ (0 : σ →₀ ℕ) := by simp
    simp [L, coeff_add, coeff_C, hzero.symm, S.coeff_freshSum, hi]
  by_cases hc0 : coeff 0 S.C = 0
  · have hrowbound : S.vars.card ≤ weight (L * H) := pure_powers_weight_mul S.vars L H hpure hH
    have hcount : A.card = weight S.C := by
      have hz : 0 ∉ S.C.support := MvPolynomial.notMem_support_iff.mpr hc0
      simp [A, hz, weight]
    rw [hweight, hcount]
    have hm : weight S.C ≤ weight S.C * weight H := Nat.le_mul_of_pos_right _ hHpos
    omega
  · have hLzero : coeff 0 L ≠ 0 := by
      have hsum0 : coeff 0 S.freshSum = 0 := by
        simp [freshSum, coeff_sum, coeff_X]
      simpa [L, coeff_add, hsum0] using hc0
    have hrowbound : S.vars.card + 1 ≤ weight (L * H) :=
      pure_endpoints_weight_mul S.vars L H hLzero hpure hH
    have hcount : A.card + 1 = weight S.C := by
      exact Finset.card_erase_add_one (MvPolynomial.mem_support_iff.mpr hc0)
    rw [hweight]
    have hm : A.card ≤ A.card * weight H := Nat.le_mul_of_pos_right _ hHpos
    omega

/-- The zero-width base case needed to choose a positive-width counterexample. -/
theorem weight_mul_of_totalWidth_zero (S : FreshData σ K) (B : Finset σ)
    (hCB : S.C.vars ⊆ B) (hBV : Disjoint B S.vars)
    (H : MvPolynomial σ K) (hH : H ≠ 0) (hwidth : totalWidth B H = 0) :
    weight S.C + S.vars.card ≤ weight (S.F * H) := by
  obtain ⟨α, D, hD, hfactor, hind⟩ := exists_factor_of_totalWidth_zero B H hH hwidth
  have h := S.weight_mul_base_independent B hCB hBV D hD hind
  rw [hfactor, mul_left_comm, weight_monomial_mul]
  exact h

end FreshData
end WeightedPilz

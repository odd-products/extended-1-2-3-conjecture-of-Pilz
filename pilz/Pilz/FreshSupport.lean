import Pilz.FreshAlgebra

/-!
# Exact support of the fresh-linear polynomial

Fresh variables give distinct singleton monomials and cannot occur in the core.
Consequently the core and fresh supports are disjoint, and their weights add.
-/

noncomputable section

namespace Pilz

open scoped BigOperators

private theorem support_sum_variables (V : Finset ℕ) :
    (∑ z ∈ V, (MvPolynomial.X z : Poly)).support =
      V.image (fun z => Finsupp.single z 1) := by
  classical
  induction V using Finset.induction_on with
  | empty => simp
  | @insert z V hz ih =>
    rw [Finset.sum_insert hz]
    have hd : Disjoint (MvPolynomial.X z : Poly).support
        (∑ i ∈ V, (MvPolynomial.X i : Poly)).support := by
      rw [MvPolynomial.support_X, ih, Finset.disjoint_singleton_left]
      intro hm
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hm
      have hiz : i = z := Finsupp.single_left_injective
        (one_ne_zero : (1 : ℕ) ≠ 0) heq
      exact hz (hiz ▸ hi)
    have hadd : (MvPolynomial.X z + ∑ i ∈ V, (MvPolynomial.X i : Poly)).support =
        (MvPolynomial.X z : Poly).support ∪
          (∑ i ∈ V, (MvPolynomial.X i : Poly)).support :=
      Finsupp.support_add_eq hd
    rw [hadd, MvPolynomial.support_X, ih]
    simp

namespace FreshData

theorem support_freshSum (S : FreshData) :
    S.freshSum.support = S.vars.image (fun z => Finsupp.single z 1) :=
  support_sum_variables S.vars

/-- The core coefficient at each fresh variable is zero. -/
theorem coeff_C_fresh (S : FreshData) {z : ℕ} (hz : z ∈ S.vars) :
    MvPolynomial.coeff (Finsupp.single z 1) S.C = 0 := by
  apply MvPolynomial.notMem_support_iff.mp
  intro hm
  have hzero := S.independent z hz (Finsupp.single z 1) hm
  simp at hzero

/-- Every fresh variable has coefficient one in the sum of fresh variables. -/
theorem coeff_freshSum (S : FreshData) (z : ℕ) :
    MvPolynomial.coeff (Finsupp.single z 1) S.freshSum =
      if z ∈ S.vars then 1 else 0 := by
  classical
  simp [freshSum, MvPolynomial.coeff_sum, MvPolynomial.coeff_X',
    Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]

theorem disjoint_C_freshSum (S : FreshData) :
    Disjoint S.C.support S.freshSum.support := by
  classical
  apply Finset.disjoint_left.mpr
  intro d hdC hdfresh
  rw [support_freshSum] at hdfresh
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hdfresh
  have hzero := S.independent z hz (Finsupp.single z 1) hdC
  simp at hzero

theorem support_F (S : FreshData) :
    S.F.support = S.C.support ∪ S.freshSum.support := by
  exact Finsupp.support_add_eq S.disjoint_C_freshSum

theorem weight_freshSum (S : FreshData) : weight S.freshSum = S.vars.card := by
  classical
  rw [weight, support_freshSum]
  exact Finset.card_image_of_injective _
    (Finsupp.single_left_injective (one_ne_zero : (1 : ℕ) ≠ 0))

theorem weight_F (S : FreshData) : weight S.F = weight S.C + S.vars.card := by
  classical
  rw [weight, support_F, Finset.card_union_of_disjoint S.disjoint_C_freshSum]
  exact congrArg (S.C.support.card + ·) S.weight_freshSum

/-- Every designated fresh monomial really belongs to `F`'s support. -/
theorem fresh_monomial_mem_support_F (S : FreshData) {z : ℕ} (hz : z ∈ S.vars) :
    Finsupp.single z 1 ∈ S.F.support := by
  rw [support_F]
  apply Finset.mem_union_right
  rw [support_freshSum]
  exact Finset.mem_image_of_mem _ hz

theorem coeff_F_fresh (S : FreshData) {z : ℕ} (hz : z ∈ S.vars) :
    MvPolynomial.coeff (Finsupp.single z 1) S.F = 1 := by
  rw [F, MvPolynomial.coeff_add, S.coeff_C_fresh hz, S.coeff_freshSum]
  simp [hz]

end FreshData
end Pilz

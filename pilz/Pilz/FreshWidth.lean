import Pilz.FreshSupport
import Pilz.Width

/-!
# Widths of a fresh-linear polynomial

The finite base-variable set is the set of variables occurring in the core.
At every non-fresh variable, the fresh terms supply exponent zero while the
core determines the largest exponent. Thus the paper's identity
`width_x F = degree_x C` is exact.
-/

noncomputable section

namespace Pilz
namespace FreshData

open scoped BigOperators

/-- The finite set of base variables that occur in the core. -/
def base (S : FreshData) : Finset ℕ := S.C.vars

theorem base_disjoint_fresh (S : FreshData) : Disjoint S.base S.vars := by
  apply Finset.disjoint_left.mpr
  intro p hp hfresh
  exact notMem_vars_of_independent (S.independent p hfresh) hp

theorem not_mem_fresh_of_mem_base (S : FreshData) {p : ℕ} (hp : p ∈ S.base) :
    p ∉ S.vars := by
  exact Finset.disjoint_left.mp S.base_disjoint_fresh hp

theorem degreeOf_C_le_degreeOf_F (S : FreshData) (p : ℕ) :
    S.C.degreeOf p ≤ S.F.degreeOf p := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro d hd
  apply MvPolynomial.monomial_le_degreeOf p
  rw [S.support_F]
  exact Finset.mem_union_left _ hd

/-- At a non-fresh variable, the core determines the greatest exponent. -/
theorem degreeOf_F (S : FreshData) {p : ℕ} (hp : p ∉ S.vars) :
    S.F.degreeOf p = S.C.degreeOf p := by
  apply le_antisymm
  · rw [MvPolynomial.degreeOf_le_iff]
    intro d hd
    rw [S.support_F] at hd
    rcases Finset.mem_union.mp hd with hc | hf
    · exact MvPolynomial.monomial_le_degreeOf p hc
    · rw [S.support_freshSum] at hf
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hf
      have hzp : z ≠ p := by
        intro heq
        exact hp (heq ▸ hz)
      simp [hzp.symm]
  · exact S.degreeOf_C_le_degreeOf_F p

/-- A fresh term witnesses exponent zero in every non-fresh variable. -/
theorem orderOf_F (S : FreshData) {p : ℕ} (hp : p ∉ S.vars) :
    orderOf p S.F = 0 := by
  obtain ⟨z, hz⟩ := S.nonempty
  have hzp : z ≠ p := by
    intro heq
    exact hp (heq ▸ hz)
  have hord := orderOf_le_support p (S.fresh_monomial_mem_support_F hz)
  have hzero : (Finsupp.single z 1 : ℕ →₀ ℕ) p = 0 := by
    simp [hzp.symm]
  exact Nat.eq_zero_of_le_zero (hzero ▸ hord)

/-- The exact width identity in the fresh-variable descent. -/
theorem width_F (S : FreshData) {p : ℕ} (hp : p ∉ S.vars) :
    widthOf p S.F = S.C.degreeOf p := by
  rw [widthOf, S.degreeOf_F hp, S.orderOf_F hp, Nat.sub_zero]

theorem width_F_base (S : FreshData) {p : ℕ} (hp : p ∈ S.base) :
    widthOf p S.F = S.C.degreeOf p :=
  S.width_F (S.not_mem_fresh_of_mem_base hp)

theorem totalWidth_F (S : FreshData) :
    totalWidth S.base S.F = ∑ p ∈ S.base, S.C.degreeOf p := by
  apply Finset.sum_congr rfl
  intro p hp
  exact S.width_F_base hp

theorem degreeOf_C_pos_of_mem_base (S : FreshData) {p : ℕ} (hp : p ∈ S.base) :
    0 < S.C.degreeOf p := by
  obtain ⟨d, hd, hpd⟩ := (MvPolynomial.mem_vars p).mp hp
  exact (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hpd)).trans_le
    (MvPolynomial.monomial_le_degreeOf p hd)

theorem totalWidth_F_pos_of_base_nonempty (S : FreshData) (hbase : S.base.Nonempty) :
    0 < totalWidth S.base S.F := by
  obtain ⟨p, hp⟩ := hbase
  have hpos : 0 < widthOf p S.F := by
    rw [S.width_F_base hp]
    exact S.degreeOf_C_pos_of_mem_base hp
  have hle : widthOf p S.F ≤ totalWidth S.base S.F :=
    Finset.single_le_sum (f := fun q => widthOf q S.F) (fun _ _ => Nat.zero_le _) hp
  exact hpos.trans_le hle

theorem base_nonempty_of_weight (S : FreshData) (hC : 2 ≤ weight S.C) :
    S.base.Nonempty := by
  by_contra hbase
  have hvars : S.C.vars = ∅ := Finset.not_nonempty_iff_eq_empty.mp hbase
  have hsub : S.C.support ⊆ {0} := by
    intro d hd
    apply Finset.mem_singleton.mpr
    ext p
    exact MvPolynomial.mem_support_notMem_vars_zero hd (by simp [hvars])
  have hcard := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hcard
  change 2 ≤ S.C.support.card at hC
  omega

/-- A core with at least two terms forces positive base width. -/
theorem totalWidth_F_pos (S : FreshData) (hC : 2 ≤ weight S.C) :
    0 < totalWidth S.base S.F :=
  S.totalWidth_F_pos_of_base_nonempty (S.base_nonempty_of_weight hC)

/-- Every nonzero multiple has at least the base width of F. -/
theorem totalWidth_F_le_multiple (S : FreshData) {G : Poly} (hG : G ≠ 0)
    (hdiv : S.F ∣ G) : totalWidth S.base S.F ≤ totalWidth S.base G := by
  obtain ⟨H, rfl⟩ := hdiv
  have hH : H ≠ 0 := by
    intro hz
    simp [hz] at hG
  rw [totalWidth_mul S.base S.prime_F.ne_zero hH]
  exact Nat.le_add_right _ _

end FreshData
end Pilz

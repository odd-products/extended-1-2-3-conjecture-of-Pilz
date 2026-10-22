import Pilz.FreshWidth
import Pilz.FreshRows

/-! The coordinate envelope and width estimate for the residual. -/

namespace Pilz
namespace FreshData

theorem residual_exponent_bounds (S : FreshData) (G₀ D : Poly)
    (hG₀ : S.EvenInFresh G₀) (hD : S.EvenInFresh D)
    (p : ℕ) (hp : p ∉ S.vars) {d : ℕ →₀ ℕ}
    (hd : d ∈ (G₀ + S.C * D).support) :
    orderOf p (G₀ + S.freshSum * D) ≤ d p ∧
      d p ≤ (G₀ + S.freshSum * D).degreeOf p + S.C.degreeOf p := by
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd0 | hcd
  · have hdG := S.support_evenPart_subset_normalForm G₀ D hG₀ hD hd0
    exact ⟨orderOf_le_support p hdG,
      (MvPolynomial.monomial_le_degreeOf p hdG).trans (Nat.le_add_right _ _)⟩
  · obtain ⟨c, hc, e, he, hce⟩ :=
      Finset.mem_add.mp (MvPolynomial.support_mul S.C D hcd)
    obtain ⟨g, hg, hgp⟩ := S.base_exponents_D_normalForm G₀ D hG₀ hD he
    have hord := orderOf_le_support p hg
    have hdeg := MvPolynomial.monomial_le_degreeOf p hg
    have hcdeg := MvPolynomial.monomial_le_degreeOf p hc
    have heq := hgp p hp
    rw [← hce, Finsupp.add_apply]
    omega

theorem residual_width_coordinate (S : FreshData) (G₀ D : Poly)
    (hG₀ : S.EvenInFresh G₀) (hD : S.EvenInFresh D)
    (p : ℕ) (hp : p ∉ S.vars) (hR : G₀ + S.C * D ≠ 0) :
    widthOf p (G₀ + S.C * D) ≤
      widthOf p (G₀ + S.freshSum * D) + S.C.degreeOf p := by
  obtain ⟨d, hd, horder⟩ := exists_support_orderOf p hR
  have hord := (S.residual_exponent_bounds G₀ D hG₀ hD p hp hd).1
  rw [horder] at hord
  have hdeg : (G₀ + S.C * D).degreeOf p ≤
      (G₀ + S.freshSum * D).degreeOf p + S.C.degreeOf p := by
    rw [MvPolynomial.degreeOf_le_iff]
    intro e he
    exact (S.residual_exponent_bounds G₀ D hG₀ hD p hp he).2
  have hle := orderOf_le_degreeOf p (G₀ + S.freshSum * D)
  unfold widthOf
  omega

/-- Equation `eq:residual-width`, with natural subtraction moved to the
left so that the estimate can be summed without truncation issues. -/
theorem residual_width_with_cofactor (S : FreshData) (G₀ D H : Poly)
    (hG₀ : S.EvenInFresh G₀) (hD : S.EvenInFresh D) (hH : H ≠ 0)
    (hfactor : G₀ + S.freshSum * D = S.F * H)
    (hR : G₀ + S.C * D ≠ 0) :
    totalWidth S.base (G₀ + S.C * D) + totalWidth S.base H ≤
      2 * totalWidth S.base (G₀ + S.freshSum * D) := by
  unfold totalWidth
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hbound := S.residual_width_coordinate G₀ D hG₀ hD p
    (S.not_mem_fresh_of_mem_base hp) hR
  have hproduct : widthOf p (G₀ + S.freshSum * D) =
      S.C.degreeOf p + widthOf p H := by
    rw [hfactor, widthOf_mul p S.prime_F.ne_zero hH, S.width_F_base hp]
  omega

end FreshData
end Pilz

import Pilz.Balanced
import Pilz.CofactorWidth
import Pilz.FreshRows
import Pilz.ResidualWidth
import Pilz.ResidualCost

/-! The synchronized normal form and the full cost of residual classes. -/

noncomputable section

namespace Pilz

structure NormalFormData (S : FreshData) (N : ℕ) where
  G : Poly
  G₀ : Poly
  D : Poly
  extremal : Extremal S.F S.base N G
  eq_form : G = G₀ + S.freshSum * D
  common : ∀ z ∈ S.vars, MvPolynomial.pderiv z G = D
  even₀ : S.EvenInFresh G₀
  evenD : S.EvenInFresh D
  D_ne_zero : D ≠ 0
  G₀_ne_zero : G₀ ≠ 0
  half : 2 * weight D ≤ weight G

theorem exists_normalForm (S : FreshData) (N : ℕ) (hC : 2 ≤ weight S.C)
    (hex : ∃ G : Poly, ShortMultiple S.F N G) : Nonempty (NormalFormData S N) := by
  obtain ⟨G, D, hG, hcommon, hhalf⟩ :=
    exists_extremal_common_derivative S S.base N S.base_disjoint_fresh hex
  let G₀ := G + S.freshSum * D
  have hevenD := S.evenInFresh_of_common_derivative G D hcommon
  have heven₀ : S.EvenInFresh G₀ :=
    S.evenInFresh_remainder_of_common_derivative G D hcommon
  have hform : G = G₀ + S.freshSum * D := by
    change G = (G + S.freshSum * D) + S.freshSum * D
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hpositive : 0 < totalWidth S.base G :=
    (S.totalWidth_F_pos hC).trans_le (S.totalWidth_F_le_multiple hG.1.1 hG.1.2.1)
  have hD : D ≠ 0 := by
    intro hz
    have hsq := S.square_dvd_residual hG.1.2.1 hcommon
    rw [hz, mul_zero, add_zero] at hsq
    obtain ⟨J, hJ⟩ := hsq
    exact extremal_not_square_multiple S.F G J S.base N hG hpositive hJ
  have hG₀ : G₀ ≠ 0 := by
    intro hz
    have hdiv : S.F ∣ S.freshSum * D := by
      have := hG.1.2.1
      rw [hform, hz, zero_add] at this
      exact this
    have hdivD : S.F ∣ D :=
      (S.prime_F.dvd_mul.mp hdiv).resolve_left S.not_dvd_freshSum
    have hwt : weight D < weight G := by
      have hm := weight_pos hG.1.1
      omega
    have hwidth : D ≠ 0 → ∀ p ∈ S.base, widthOf p D ≤ widthOf p G := by
      intro hD' p hp
      apply widthOf_mono_exponents p hD'
      intro e he
      obtain ⟨d, hd, hcoord⟩ := S.base_exponents_D_normalForm G₀ D heven₀ hevenD he
      rw [← hform] at hd
      exact ⟨d, hd, (hcoord p (S.not_mem_fresh_of_mem_base hp)).symm⟩
    exact hD (extremal_eq_zero_of_weight_lt S.F S.base N G D hG hdivD hwt hwidth)
  exact ⟨⟨G, G₀, D, hG, hform, hcommon, heven₀, hevenD, hD, hG₀, hhalf⟩⟩

theorem normalForm_weight (S : FreshData) (N : ℕ) (nf : NormalFormData S N) :
    weight nf.G₀ + S.vars.card * weight nf.D = weight nf.G := by
  rw [nf.eq_form, S.weight_normalForm nf.G₀ nf.D nf.even₀ nf.evenD]

/-- Proposition `prop:residual`: every nonzero full residual class costs N. -/
theorem normalForm_residual_cost (S : FreshData) (N : ℕ) (nf : NormalFormData S N)
    (hN : N ≤ weight S.C + S.vars.card) :
    ∀ ε : ℕ → ℕ, 0 < classWeight (nf.G₀ + S.C * nf.D) ε →
      N ≤ classWeight (nf.G₀ + S.C * nf.D) ε := by
  obtain ⟨H, hGH⟩ := nf.extremal.1.2.1
  have hH : H ≠ 0 := by
    intro hz
    apply nf.extremal.1.1
    rw [hGH, hz, mul_zero]
  have hshort : weight (S.F * H) < N := by
    rw [← hGH]
    exact nf.extremal.1.2.2
  have hpositive := S.totalWidth_cofactor_pos N H hH hN hshort
  have hres : nf.G + S.F * nf.D = nf.G₀ + S.C * nf.D := by
    rw [nf.eq_form, FreshData.F, add_mul]
    calc
      (nf.G₀ + S.freshSum * nf.D) + (S.C * nf.D + S.freshSum * nf.D) =
          (nf.G₀ + S.C * nf.D) + (S.freshSum * nf.D + S.freshSum * nf.D) := by ac_rfl
      _ = nf.G₀ + S.C * nf.D := by rw [CharTwo.add_self_eq_zero, add_zero]
  have hsq := S.square_dvd_residual nf.extremal.1.2.1 nf.common
  rw [hres] at hsq
  obtain ⟨J, hJ⟩ := hsq
  intro ε hclass
  have hR : nf.G₀ + S.C * nf.D ≠ 0 := by
    intro hz
    have hc := hclass.trans_le (classWeight_le_weight (nf.G₀ + S.C * nf.D) ε)
    rw [hz, weight_zero] at hc
    omega
  have hwidth := S.residual_width_with_cofactor nf.G₀ nf.D H nf.even₀ nf.evenD hH
    (nf.eq_form.symm.trans hGH) hR
  rw [hJ, ← nf.eq_form] at hwidth
  rw [hJ] at hclass ⊢
  exact residual_class_cost_all S.F nf.G J H S.base N nf.extremal hpositive hwidth ε hclass

end Pilz

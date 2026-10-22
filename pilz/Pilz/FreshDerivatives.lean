import Pilz.FreshAlgebra
import Pilz.Derivatives

/-!
# Derivatives in the fresh-linear setting

This file supplies the algebraic implications of synchronized fresh
derivatives. Existence of an extremal synchronized multiple and the width
descent remain separate statements.
-/

noncomputable section

namespace Pilz
namespace FreshData

open MvPolynomial

/-- Every occurring exponent of every designated fresh variable is even. -/
def EvenInFresh (S : FreshData) (P : Poly) : Prop :=
  ∀ z ∈ S.vars, ∀ d ∈ P.support, Even (d z)

theorem evenInFresh_iff_pderiv_eq_zero (S : FreshData) (P : Poly) :
    S.EvenInFresh P ↔ ∀ z ∈ S.vars, pderiv z P = 0 := by
  constructor
  · intro h z hz
    exact (pderiv_eq_zero_iff_even_exponents P z).mpr (h z hz)
  · intro h z hz
    exact (pderiv_eq_zero_iff_even_exponents P z).mp (h z hz)

theorem pderiv_freshSum (S : FreshData) {z : ℕ} (hz : z ∈ S.vars) :
    pderiv z S.freshSum = 1 := by
  classical
  rw [freshSum, map_sum]
  rw [Finset.sum_eq_single z]
  · exact pderiv_X_self z
  · intro j _ hjz
    exact pderiv_X_of_ne hjz
  · intro hnot
    exact False.elim (hnot hz)

theorem pderiv_F (S : FreshData) {z : ℕ} (hz : z ∈ S.vars) :
    pderiv z S.F = 1 := by
  rw [F, map_add, pderiv_eq_zero_of_exponent_zero S.C z (S.independent z hz),
    S.pderiv_freshSum hz, zero_add]

theorem dvd_pair_pderiv (S : FreshData) {G : Poly} {i j : ℕ}
    (hi : i ∈ S.vars) (hj : j ∈ S.vars) (hG : S.F ∣ G) :
    S.F ∣ pderiv i G + pderiv j G := by
  apply Pilz.dvd_pair_pderiv i j _ hG
  rw [S.pderiv_F hi, S.pderiv_F hj]

/-- The common value of all fresh derivatives is even in every fresh variable. -/
theorem evenInFresh_of_common_derivative (S : FreshData) (G D : Poly)
    (hD : ∀ z ∈ S.vars, pderiv z G = D) : S.EvenInFresh D := by
  intro z hz d hd
  rw [← hD z hz] at hd
  exact even_exponent_of_mem_support_pderiv hd

/-- Once fresh derivatives agree, removing the synchronized odd rows leaves
an even polynomial in all fresh variables. -/
theorem evenInFresh_remainder_of_common_derivative (S : FreshData) (G D : Poly)
    (hD : ∀ z ∈ S.vars, pderiv z G = D) :
    S.EvenInFresh (G + S.freshSum * D) := by
  apply (S.evenInFresh_iff_pderiv_eq_zero _).mpr
  intro z hz
  have hDzero : pderiv z D = 0 :=
    (S.evenInFresh_iff_pderiv_eq_zero D).mp (S.evenInFresh_of_common_derivative G D hD) z hz
  rw [map_add, pderiv_mul, hD z hz, S.pderiv_freshSum hz, hDzero]
  simp [CharTwo.add_self_eq_zero]

/-- The residual identity in Proposition `prop:residual`, before its width
and parity-class analysis. It proves divisibility by the square of `F`. -/
theorem residual_eq_square_mul_pderiv (S : FreshData) (H : Poly) {z : ℕ}
    (hz : z ∈ S.vars) :
    S.F * H + S.F * pderiv z (S.F * H) = S.F ^ 2 * pderiv z H := by
  rw [pderiv_mul, S.pderiv_F hz, one_mul, mul_add]
  calc
    S.F * H + (S.F * H + S.F * (S.F * pderiv z H)) =
        (S.F * H + S.F * H) + S.F * (S.F * pderiv z H) := by ac_rfl
    _ = S.F ^ 2 * pderiv z H := by
      rw [CharTwo.add_self_eq_zero, zero_add, pow_two, mul_assoc]

theorem square_dvd_residual (S : FreshData) {G D : Poly}
    (hG : S.F ∣ G) (hD : ∀ z ∈ S.vars, pderiv z G = D) :
    S.F ^ 2 ∣ G + S.F * D := by
  obtain ⟨z, hz⟩ := S.nonempty
  obtain ⟨H, rfl⟩ := hG
  rw [← hD z hz, S.residual_eq_square_mul_pderiv H hz]
  exact dvd_mul_right _ _

/-- The fresh-even cofactor conclusion used after square divisibility. -/
theorem evenInFresh_of_square_mul (S : FreshData) (J : Poly)
    (hR : S.EvenInFresh (S.F ^ 2 * J)) : S.EvenInFresh J := by
  apply (S.evenInFresh_iff_pderiv_eq_zero J).mpr
  intro z hz
  have hzR := (S.evenInFresh_iff_pderiv_eq_zero _).mp hR z hz
  rw [pderiv_mul, pderiv_square, zero_mul, zero_add] at hzR
  exact (mul_eq_zero.mp hzR).resolve_left (pow_ne_zero _ S.prime_F.ne_zero)

end FreshData
end Pilz

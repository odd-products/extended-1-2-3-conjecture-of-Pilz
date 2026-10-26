import WeightedPilz.AffineRows
import WeightedPilz.Support
import Mathlib.Tactic.Linarith

/-! Cancellation and integer budgets for affine cofactors. The algebraic
inequality is valid for arbitrary coefficient fields and arbitrary variables. -/

noncomputable section
namespace WeightedPilz

open MvPolynomial
variable {σ K : Type*} [Field K]

/-- The square contribution can lose at most `weight C` terms for each term
in the middle row. This is the algebra behind equation `fin-affine-budget`. -/
theorem affine_square_cancellation (C D B : MvPolynomial σ K) :
    weight (C ^ 2 * B) ≤ weight (C * D) + weight C * weight (D + C * B) := by
  classical
  have heq : C ^ 2 * B = C * (D + C * B) - C * D := by ring
  have hsub := Finset.card_le_card (MvPolynomial.support_sub σ (C * (D + C * B)) (C * D))
  have hunion := Finset.card_union_le (C * (D + C * B)).support (C * D).support
  have hmul := weight_mul_le C (D + C * B)
  rw [heq]
  change (C * (D + C * B) - C * D).support.card ≤ _
  change (C * (D + C * B)).support.card ≤ _ at hmul
  unfold weight at *
  omega

/-- A square lower bound and an upper bound for the middle row force the
desired affine lower bound, with the cancellation cost made explicit. -/
theorem affine_row_budget (C D B : MvPolynomial σ K) (n r R k : ℕ)
    (hC : weight C + r = n) (hr : 2 * r ≤ n)
    (hE : weight (D + C * B) ≤ k)
    (hbudget : n + (n - 2 * r) * k ≤ weight (C ^ 2 * B) + R * weight B) :
    n ≤ weight (C * D) + r * weight (D + C * B) + R * weight B := by
  have hc := affine_square_cancellation C D B
  have hdiff : n - 2 * r + r = weight C := by omega
  have hmono := Nat.mul_le_mul_left (n - 2 * r) hE
  nlinarith

/-- The two integer bounds obtained from a strict affine counterexample. -/
theorem affine_counterexample_budgets (n d r R a e t : ℕ)
    (hr : 0 < r) (hR : 0 < R) (ha : d ≤ a)
    (hsmall : a + r * e + R * t < n) :
    t ≤ (n - 1 - d) / R ∧ e ≤ (n - 1 - d - R * t) / r := by
  constructor
  · apply (Nat.le_div_iff_mul_le hR).mpr
    have hRt : R * t ≤ n - 1 - d := by omega
    simpa only [Nat.mul_comm] using hRt
  · apply (Nat.le_div_iff_mul_le hr).mpr
    have hre : r * e ≤ n - 1 - d - R * t := by omega
    simpa only [Nat.mul_comm] using hre

namespace FreshData

variable [DecidableEq σ]

/-- Apply the cancellation budget to the exact fresh-variable row identity. -/
theorem affine_lower_of_square_budget (S : FreshData σ K)
    (D B : MvPolynomial σ K) (hD : S.BaseOnly D) (hB : S.BaseOnly B)
    (h2 : (2 : K) ≠ 0) (n k : ℕ)
    (hC : weight S.C + S.vars.card = n) (hr : 2 * S.vars.card ≤ n)
    (hE : weight (D + S.C * B) ≤ k)
    (hbudget : n + (n - 2 * S.vars.card) * k ≤
      weight (S.C ^ 2 * B) + (S.vars.card * (S.vars.card + 1) / 2) * weight B) :
    n ≤ weight (S.F * (D + S.freshSum * B)) := by
  rw [S.weight_mul_affine D B hD hB h2]
  exact affine_row_budget S.C D B n S.vars.card _ k hC hr hE hbudget

end FreshData
end WeightedPilz

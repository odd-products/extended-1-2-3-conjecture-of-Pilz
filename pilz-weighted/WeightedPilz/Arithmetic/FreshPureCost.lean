import WeightedPilz.Fresh
import Mathlib.Data.Finsupp.Order

/-! Every positive power of the fresh-variable sum retains all pure powers,
over every field and in every characteristic. -/

noncomputable section

namespace WeightedPilz.FreshData

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [DecidableEq σ] [Field K]

theorem coeff_pure_freshSum_pow (S : FreshData σ K) {z : σ} (hz : z ∈ S.vars)
    (d : ℕ) : coeff (Finsupp.single z d) (S.freshSum ^ d) = 1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, freshSum, Finset.mul_sum, coeff_sum]
    rw [Finset.sum_eq_single z]
    · rw [coeff_mul_X']
      simp only [Finsupp.support_single_ne_zero z (by omega : d + 1 ≠ 0),
        Finset.mem_singleton, if_pos rfl, ← Finsupp.single_tsub, Nat.add_sub_cancel]
      exact ih
    · intro i hi hiz
      rw [coeff_mul_X']
      simp [Finsupp.support_single_ne_zero z (by omega : d + 1 ≠ 0), hiz]
    · exact fun h => (h hz).elim

theorem pure_fresh_powers_subset (S : FreshData σ K) {d : ℕ} (hd : 0 < d) :
    S.vars.image (fun z => Finsupp.single z d) ⊆ (S.freshSum ^ d).support := by
  intro e he
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
  exact mem_support_iff.mpr (by rw [S.coeff_pure_freshSum_pow hz]; exact one_ne_zero)

/-- The all-characteristic lower bound in equation (digitcost), for every positive degree. -/
theorem fresh_card_le_weight_pow (S : FreshData σ K) {d : ℕ} (hd : 0 < d) :
    S.vars.card ≤ weight (S.freshSum ^ d) := by
  have hi : Function.Injective (fun z : σ => Finsupp.single z d) :=
    Finsupp.single_left_injective (Nat.ne_of_gt hd)
  calc
    S.vars.card = (S.vars.image (fun z => Finsupp.single z d)).card :=
      (Finset.card_image_of_injective S.vars hi).symm
    _ ≤ (S.freshSum ^ d).support.card := Finset.card_le_card (S.pure_fresh_powers_subset hd)
    _ = weight (S.freshSum ^ d) := rfl

end WeightedPilz.FreshData

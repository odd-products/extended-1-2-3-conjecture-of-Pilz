import WeightedPilz.AggregateLowestRow
import WeightedPilz.FreshDegreeBounds

/-! The positive aggregate-row alternatives in the short fresh-row test. -/
noncomputable section
namespace WeightedPilz.FreshData
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [DecidableEq σ] [Field K]

/-- A positive degree has the minimal fresh cost only if it is distinguished. -/
theorem distinguished_of_fresh_cost_le (S : FreshData σ K) (p : ℕ) [ExpChar K p]
    (hr : 2 ≤ S.vars.card) {j : ℕ} (hj : 0 < j)
    (hw : weight (S.freshSum ^ j) ≤ S.vars.card) : ∃ e, j = p ^ e := by
  by_contra h
  have hnd : ∀ e, j ≠ p ^ e := by simpa only [not_exists] using h
  have hcost := S.fresh_nondistinguished_degree_cost p hj hnd
  have hquad : S.vars.card + 1 ≤ S.vars.card * (S.vars.card + 1) / 2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    nlinarith
  omega

private theorem coefficient_weight_pos {A : MvPolynomial σ K} (hA : A ≠ 0) :
    1 ≤ weight A := by
  simpa [weight, Finset.card_pos, MvPolynomial.support_nonempty] using hA

/-- At most `2r` fresh terms allow one monomial row, one distinguished
binomial row, or two distinguished monomial rows. -/
theorem short_positive_rows (S : FreshData σ K) (p : ℕ) [ExpChar K p]
    (t : Finset ℕ) (A : ℕ → MvPolynomial σ K) (hr : 2 ≤ S.vars.card)
    (ht : t.Nonempty) (hj : ∀ j ∈ t, 0 < j)
    (hA : ∀ j ∈ t, A j ≠ 0) (hbase : ∀ j ∈ t, S.BaseOnly (A j))
    (hw : (∑ j ∈ t, weight (S.freshSum ^ j * A j)) ≤ 2 * S.vars.card) :
    (∃ j, t = {j} ∧ weight (A j) = 1) ∨
    (∃ j e, t = {j} ∧ weight (A j) = 2 ∧ j = p ^ e) ∨
    (∃ i j e f, i ≠ j ∧ t = {i, j} ∧ weight (A i) = 1 ∧
      weight (A j) = 1 ∧ i = p ^ e ∧ j = p ^ f) := by
  have hmul : ∀ j ∈ t, weight (S.freshSum ^ j * A j) =
      weight (S.freshSum ^ j) * weight (A j) :=
    fun j hj => S.weight_freshSum_pow_mul_baseOnly j (A j) (hbase j hj)
  have hW : ∀ j ∈ t, S.vars.card ≤ weight (S.freshSum ^ j) :=
    fun j h => S.fresh_card_le_weight_pow (hj j h)
  have hB : ∀ j ∈ t, 1 ≤ weight (A j) := fun j h => coefficient_weight_pos (hA j h)
  have hsum : (∑ j ∈ t, weight (A j)) ≤ 2 := by
    have hle : S.vars.card * (∑ j ∈ t, weight (A j)) ≤ 2 * S.vars.card := by
      apply le_trans _ hw
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun j h => by
        rw [hmul j h]
        exact Nat.mul_le_mul_right _ (hW j h))
    nlinarith
  have hcard : t.card ≤ 2 := by
    have hle : t.card ≤ ∑ j ∈ t, weight (A j) := by
      simpa only [Finset.sum_const, smul_eq_mul, mul_one] using
        (Finset.sum_le_sum hB : (∑ j ∈ t, 1) ≤ ∑ j ∈ t, weight (A j))
    omega
  have hcardpos := Finset.card_pos.mpr ht
  rcases (show t.card = 1 ∨ t.card = 2 by omega) with hcard | hcard
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
    have hB' := hB j (by simp)
    simp only [Finset.sum_singleton] at hsum hw
    rcases (show weight (A j) = 1 ∨ weight (A j) = 2 by omega) with h | h
    · exact Or.inl ⟨j, rfl, h⟩
    · have hWle : weight (S.freshSum ^ j) ≤ S.vars.card := by
        rw [hmul j (by simp), h] at hw
        omega
      obtain ⟨e, he⟩ := S.distinguished_of_fresh_cost_le p hr (hj j (by simp)) hWle
      exact Or.inr (Or.inl ⟨j, e, rfl, h, he⟩)
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hcard
    have hi : i ∈ ({i, j} : Finset ℕ) := by simp
    have hj' : j ∈ ({i, j} : Finset ℕ) := by simp
    have hBi := hB i hi
    have hBj := hB j hj'
    simp only [Finset.sum_pair hij] at hsum hw
    have hai : weight (A i) = 1 := by omega
    have haj : weight (A j) = 1 := by omega
    rw [hmul i hi, hmul j hj', hai, haj, mul_one, mul_one] at hw
    have hWi := hW i hi
    have hWj := hW j hj'
    obtain ⟨e, he⟩ := S.distinguished_of_fresh_cost_le p hr (hj i hi) (by omega)
    obtain ⟨f, hf⟩ := S.distinguished_of_fresh_cost_le p hr (hj j hj') (by omega)
    exact Or.inr (Or.inr ⟨i, j, e, f, hij, rfl, hai, haj, he, hf⟩)

end WeightedPilz.FreshData

import WeightedPilz.ShortFreshTest
import WeightedPilz.Arithmetic.DigitCostsExtra

/-! The exceptional two-fresh-variable budget of five. -/
noncomputable section
namespace WeightedPilz.FreshData
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [DecidableEq σ] [Field K]

/-- A three-term power of a two-variable fresh sum is twice a distinguished degree. -/
theorem two_fresh_cost_three (S : FreshData σ K) (p : ℕ) [hpK : ExpChar K p]
    (hr : S.vars.card = 2) {j : ℕ} (hw : weight (S.freshSum ^ j) = 3) :
    p ≠ 2 ∧ ∃ e, j = 2 * p ^ e := by
  cases hpK with
  | zero =>
    rw [S.weight_freshSum_pow_charZero, hr,
      show 2 + j - 1 = j + 1 by omega, Nat.choose_succ_self_right] at hw
    exact ⟨by decide, 0, by simp; omega⟩
  | prime hp =>
    letI : Fact p.Prime := ⟨hp⟩
    rw [S.weight_freshSum_pow_digits p, hr] at hw
    have hcost : Arithmetic.digitCost 2 p j = 3 := hw
    obtain ⟨hp3, e, he⟩ := Arithmetic.digitCost_two_eq_three hp.one_lt hcost
    exact ⟨by omega, e, he⟩

theorem two_fresh_twice_distinguished_cost (S : FreshData σ K) (p e : ℕ)
    [hpK : ExpChar K p] (hr : S.vars.card = 2) (hp2 : p ≠ 2) :
    weight (S.freshSum ^ (2 * p ^ e)) = 3 := by
  rw [pow_mul, weight_pow_expChar p e]
  cases hpK with
  | zero =>
    rw [S.weight_freshSum_pow_charZero, hr]
    decide
  | prime hp =>
    letI : Fact p.Prime := ⟨hp⟩
    have hp3 : 2 < p := by have := hp.two_le; omega
    rw [S.weight_freshSum_pow_lt_char p 2 hp3, hr]
    decide

/-- Budget five adds only a distinguished monomial row paired with a
twice-distinguished monomial row, in characteristic different from two. -/
theorem five_positive_rows (S : FreshData σ K) (p : ℕ) [ExpChar K p]
    (t : Finset ℕ) (A : ℕ → MvPolynomial σ K) (hr : S.vars.card = 2)
    (ht : t.Nonempty) (hj : ∀ j ∈ t, 0 < j)
    (hA : ∀ j ∈ t, A j ≠ 0) (hbase : ∀ j ∈ t, S.BaseOnly (A j))
    (hw : (∑ j ∈ t, weight (S.freshSum ^ j * A j)) ≤ 5) :
    ((∃ j, t = {j} ∧ weight (A j) = 1) ∨
      (∃ j e, t = {j} ∧ weight (A j) = 2 ∧ j = p ^ e) ∨
      (∃ i j e f, i ≠ j ∧ t = {i, j} ∧ weight (A i) = 1 ∧
        weight (A j) = 1 ∧ i = p ^ e ∧ j = p ^ f)) ∨
    (∃ i j e f, i ≠ j ∧ t = {i, j} ∧ weight (A i) = 1 ∧
      weight (A j) = 1 ∧ i = p ^ e ∧ j = 2 * p ^ f ∧ p ≠ 2) := by
  by_cases hsmall : (∑ j ∈ t, weight (S.freshSum ^ j * A j)) ≤ 4
  · exact Or.inl (S.short_positive_rows p t A (by omega) ht hj hA hbase (by omega))
  have hmul : ∀ j ∈ t, weight (S.freshSum ^ j * A j) =
      weight (S.freshSum ^ j) * weight (A j) :=
    fun j hj => S.weight_freshSum_pow_mul_baseOnly j (A j) (hbase j hj)
  have hW : ∀ j ∈ t, 2 ≤ weight (S.freshSum ^ j) := by
    intro j h
    simpa only [hr] using S.fresh_card_le_weight_pow (hj j h)
  have hB : ∀ j ∈ t, 1 ≤ weight (A j) := by
    intro j h
    simpa [weight, Finset.card_pos, MvPolynomial.support_nonempty] using hA j h
  have hsum : (∑ j ∈ t, weight (A j)) ≤ 2 := by
    have hle : 2 * (∑ j ∈ t, weight (A j)) ≤ 5 := by
      apply le_trans _ hw
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun j h => by
        rw [hmul j h]
        exact Nat.mul_le_mul_right _ (hW j h))
    omega
  have hcard : t.card ≤ 2 := by
    have hle : t.card ≤ ∑ j ∈ t, weight (A j) := by
      simpa only [Finset.sum_const, smul_eq_mul, mul_one] using
        (Finset.sum_le_sum hB : (∑ j ∈ t, 1) ≤ ∑ j ∈ t, weight (A j))
    omega
  have hcardpos := Finset.card_pos.mpr ht
  rcases (show t.card = 1 ∨ t.card = 2 by omega) with hcard | hcard
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
    have hB' := hB j (by simp)
    simp only [Finset.sum_singleton] at hsum hw hsmall
    have hAj : weight (A j) = 1 := by
      by_contra hn
      have heq : weight (A j) = 2 := by omega
      rw [hmul j (by simp), heq] at hw hsmall
      omega
    exact Or.inl (Or.inl ⟨j, rfl, hAj⟩)
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hcard
    have hi : i ∈ ({i, j} : Finset ℕ) := by simp
    have hj' : j ∈ ({i, j} : Finset ℕ) := by simp
    have hBi := hB i hi
    have hBj := hB j hj'
    simp only [Finset.sum_pair hij] at hsum hw hsmall
    have hai : weight (A i) = 1 := by omega
    have haj : weight (A j) = 1 := by omega
    rw [hmul i hi, hmul j hj', hai, haj, mul_one, mul_one] at hw hsmall
    have hWi := hW i hi
    have hWj := hW j hj'
    rcases (show (weight (S.freshSum ^ i) = 2 ∧ weight (S.freshSum ^ j) = 3) ∨
        (weight (S.freshSum ^ j) = 2 ∧ weight (S.freshSum ^ i) = 3) by omega) with h | h
    · obtain ⟨e, he⟩ := S.distinguished_of_fresh_cost_le p (by omega) (hj i hi) (by omega)
      obtain ⟨hp, f, hf⟩ := S.two_fresh_cost_three p hr h.2
      exact Or.inr ⟨i, j, e, f, hij, rfl, hai, haj, he, hf, hp⟩
    · obtain ⟨e, he⟩ := S.distinguished_of_fresh_cost_le p (by omega) (hj j hj') (by omega)
      obtain ⟨hp, f, hf⟩ := S.two_fresh_cost_three p hr h.2
      exact Or.inr ⟨j, i, e, f, hij.symm, Finset.pair_comm _ _, haj, hai, he, hf, hp⟩

/-- The exceptional budget-five version of the short fresh-row test. -/
theorem short_fresh_test_five (S : FreshData σ K) (p κ : ℕ) [ExpChar K p]
    (hr : S.vars.card = 2) (hκ : κ ≤ distance S.C)
    (hstart : weight S.C + S.vars.card ≤ S.vars.card * (κ + 1))
    (hbudget : weight S.C + S.vars.card - 1 - κ ≤ 5)
    (hpower : ∀ j, 0 < j → (∀ e : ℕ, j ≠ p ^ e) →
      weight (S.freshSum ^ j) ≤ weight S.C + S.vars.card - 1 - κ →
      weight S.C + S.vars.card ≤ weight (S.C ^ j) + weight (S.freshSum ^ j))
    (hbinomial : ∀ e (H : MvPolynomial σ K), weight H = 2 →
      weight S.C + S.vars.card - 2 * S.vars.card ≤ weight (S.C ^ p ^ e * H))
    (htwo : ∀ e f (M L : MvPolynomial σ K), p ^ e ≠ p ^ f →
      weight M = 1 → weight L = 1 →
      M * S.C ^ p ^ e + L * S.C ^ p ^ f ≠ 0 →
      weight S.C + S.vars.card - 2 * S.vars.card ≤
        weight (M * S.C ^ p ^ e + L * S.C ^ p ^ f))
    (hmixed : p ≠ 2 → ∀ e f (M L : MvPolynomial σ K),
      weight M = 1 → weight L = 1 →
      M * S.C ^ p ^ e + L * S.C ^ (2 * p ^ f) ≠ 0 →
      weight S.C + S.vars.card - 5 ≤ weight (M * S.C ^ p ^ e + L * S.C ^ (2 * p ^ f))) :
    weight S.C + S.vars.card ≤ distance S.F := by
  classical
  by_contra hn
  have hdist : distance S.F < weight S.C + S.vars.card := Nat.lt_of_not_ge hn
  obtain ⟨t, A, hbase, hG, hdiv, hweight⟩ := S.exists_scalar_minimum
  have hw : weight (∑ j ∈ t, S.freshSum ^ j * A j) < weight S.C + S.vars.card := by
    rwa [hweight]
  obtain ⟨hzero, hA0, hκA⟩ := S.aggregate_lowest_row_zero t A hbase hG hdiv κ
    (weight S.C + S.vars.card) hκ hstart hw
  obtain ⟨ht, htotal, hrel⟩ := S.aggregate_positive_data t A hbase hdiv hzero hA0
  let u := occupiedPositiveRows t A
  have huj : ∀ j ∈ u, 0 < j := fun j hj => (Finset.mem_filter.mp hj).2.1
  have huA : ∀ j ∈ u, A j ≠ 0 := fun j hj => (Finset.mem_filter.mp hj).2.2
  have hubase : ∀ j ∈ u, S.BaseOnly (A j) :=
    fun j hj => hbase j (Finset.mem_filter.mp hj).1
  change weight (∑ j ∈ t, S.freshSum ^ j * A j) =
    weight (A 0) + ∑ j ∈ u, weight (S.freshSum ^ j * A j) at htotal
  have hposbudget : (∑ j ∈ u, weight (S.freshSum ^ j * A j)) ≤
      weight S.C + S.vars.card - 1 - κ := by omega
  have hshort := S.five_positive_rows p u A hr ht huj huA hubase (hposbudget.trans hbudget)
  change A 0 + (∑ j ∈ u, (-S.C) ^ j * A j) = 0 at hrel
  rcases hshort with (⟨j, hu, hAj⟩ | ⟨j, e, hu, hAj, he⟩ | ⟨i, j, e, f, hij, hu, hAi, hAj, he, hf⟩) | ⟨i, j, e, f, hij, hu, hAi, hAj, he, hf, hp2⟩
  · have hj : j ∈ u := by rw [hu]; simp
    rw [hu, Finset.sum_singleton] at hrel htotal hposbudget
    have hAeq : A 0 = -((-S.C) ^ j * A j) := eq_neg_of_add_eq_zero_left hrel
    have hAweight : weight (A 0) = weight (S.C ^ j) := by
      rw [hAeq]
      simp only [weight, support_neg]
      change weight ((-S.C) ^ j * A j) = weight (S.C ^ j)
      rw [weight_mul_of_weight_one _ _ hAj, weight_negative_power]
    rw [S.weight_freshSum_pow_mul_baseOnly j (A j) (hubase j hj), hAj, mul_one] at htotal hposbudget
    rw [hAweight] at htotal
    by_cases hdistj : ∃ e, j = p ^ e
    · obtain ⟨e, rfl⟩ := hdistj
      rw [weight_pow_expChar p e S.C, S.fresh_distinguished_degree_cost p e] at htotal
      omega
    · have hnd : ∀ e, j ≠ p ^ e := by simpa only [not_exists] using hdistj
      have := hpower j (huj j hj) hnd hposbudget
      omega
  · have hj : j ∈ u := by rw [hu]; simp
    rw [hu, Finset.sum_singleton, he, negative_distinguished_power,
      neg_mul] at hrel
    have hAeq : A 0 = S.C ^ p ^ e * A j := eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, he] using hrel)
    have hbound := hbinomial e (A j) hAj
    rw [← hAeq] at hbound
    rw [hu, Finset.sum_singleton, S.weight_freshSum_pow_mul_baseOnly j (A j) (hubase j hj),
      hAj, he, S.fresh_distinguished_degree_cost] at htotal
    omega
  · have hi : i ∈ u := by rw [hu]; simp
    have hj : j ∈ u := by rw [hu]; simp
    rw [hu, Finset.sum_pair hij, he, hf, negative_distinguished_power,
      negative_distinguished_power, neg_mul, neg_mul] at hrel
    have hAeq : A 0 = A i * S.C ^ p ^ e + A j * S.C ^ p ^ f := by
      rw [he, hf]
      linear_combination hrel
    have hbound := htwo e f (A i) (A j) (by simpa only [← he, ← hf] using hij) hAi hAj
      (by simpa only [← hAeq] using hA0)
    rw [← hAeq] at hbound
    rw [hu, Finset.sum_pair hij, S.weight_freshSum_pow_mul_baseOnly i (A i) (hubase i hi),
      S.weight_freshSum_pow_mul_baseOnly j (A j) (hubase j hj), hAi, hAj,
      mul_one, mul_one, he, hf, S.fresh_distinguished_degree_cost,
      S.fresh_distinguished_degree_cost] at htotal
    omega
  · have hi : i ∈ u := by rw [hu]; simp
    have hj : j ∈ u := by rw [hu]; simp
    have heven : Even (2 * p ^ f) := ⟨p ^ f, by omega⟩
    rw [hu, Finset.sum_pair hij, he, hf, negative_distinguished_power,
      heven.neg_pow, neg_mul] at hrel
    have hAeq : A 0 = A i * S.C ^ p ^ e + (-A j) * S.C ^ (2 * p ^ f) := by
      rw [he, hf]
      linear_combination hrel
    have hnegweight : weight (-A j) = 1 := by simpa only [weight, support_neg] using hAj
    have hbound := hmixed hp2 e f (A i) (-A j) hAi hnegweight (by simpa only [← hAeq] using hA0)
    rw [← hAeq] at hbound
    rw [hu, Finset.sum_pair hij, S.weight_freshSum_pow_mul_baseOnly i (A i) (hubase i hi),
      S.weight_freshSum_pow_mul_baseOnly j (A j) (hubase j hj), hAi, hAj,
      mul_one, mul_one, he, hf, S.fresh_distinguished_degree_cost,
      S.two_fresh_twice_distinguished_cost p f hr hp2, hr] at htotal
    omega

end WeightedPilz.FreshData

import WeightedPilz.ShortFreshFive
import WeightedPilz.Arithmetic.DigitCostsThreeExtra

/-! Equality cases for the fresh-row costs used before the short fresh-row test. -/
noncomputable section
namespace WeightedPilz.FreshData
variable {σ K : Type*} [DecidableEq σ] [Field K]

theorem fresh_cost_eq_card_iff (S : FreshData σ K) (p : ℕ) [ExpChar K p]
    (hr : 2 ≤ S.vars.card) {j : ℕ} (hj : 0 < j) :
    weight (S.freshSum ^ j) = S.vars.card ↔ ∃ e, j = p ^ e := by
  constructor
  · intro hw
    exact S.distinguished_of_fresh_cost_le p hr hj hw.le
  · rintro ⟨e, rfl⟩
    exact S.fresh_distinguished_degree_cost p e

theorem two_fresh_cost_three_iff (S : FreshData σ K) (p : ℕ) [ExpChar K p]
    (hr : S.vars.card = 2) (j : ℕ) :
    weight (S.freshSum ^ j) = 3 ↔ p ≠ 2 ∧ ∃ e, j = 2 * p ^ e := by
  constructor
  · exact S.two_fresh_cost_three p hr
  · rintro ⟨hp, e, rfl⟩
    exact S.two_fresh_twice_distinguished_cost p e hr hp

theorem three_fresh_cost_six (S : FreshData σ K) (p : ℕ) [hpK : ExpChar K p]
    (hr : S.vars.card = 3) {j : ℕ} (hw : weight (S.freshSum ^ j) = 6) :
    p ≠ 2 ∧ ∃ e, j = 2 * p ^ e := by
  cases hpK with
  | zero =>
    rw [S.weight_freshSum_pow_charZero, hr] at hw
    have hjle : j ≤ 2 := by
      by_contra hn
      have hle := Arithmetic.choose_cost_mono (r := 3) (a := 3) (b := j)
        (by decide) (by omega)
      change 10 ≤ (3 + j - 1).choose j at hle
      omega
    have hj2 : j = 2 := by
      have hj0 : j ≠ 0 := by intro hz; simp [hz] at hw
      have hj1 : j ≠ 1 := by intro hz; simp [hz] at hw
      omega
    exact ⟨by decide, 0, by simpa using hj2⟩
  | prime hp =>
    letI : Fact p.Prime := ⟨hp⟩
    rw [S.weight_freshSum_pow_digits p, hr] at hw
    have hcost : Arithmetic.digitCost 3 p j = 6 := hw
    obtain ⟨hp3, e, he⟩ := Arithmetic.digitCost_three_eq_six hp.one_lt hcost
    exact ⟨by omega, e, he⟩

theorem three_fresh_twice_distinguished_cost (S : FreshData σ K) (p e : ℕ)
    [hpK : ExpChar K p] (hr : S.vars.card = 3) (hp2 : p ≠ 2) :
    weight (S.freshSum ^ (2 * p ^ e)) = 6 := by
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

theorem three_fresh_cost_six_iff (S : FreshData σ K) (p : ℕ) [ExpChar K p]
    (hr : S.vars.card = 3) (j : ℕ) :
    weight (S.freshSum ^ j) = 6 ↔ p ≠ 2 ∧ ∃ e, j = 2 * p ^ e := by
  constructor
  · exact S.three_fresh_cost_six p hr
  · rintro ⟨hp, e, rfl⟩
    exact S.three_fresh_twice_distinguished_cost p e hr hp

end WeightedPilz.FreshData

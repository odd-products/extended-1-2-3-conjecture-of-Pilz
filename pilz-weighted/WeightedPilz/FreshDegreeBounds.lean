import WeightedPilz.FreshCostsExtra
import WeightedPilz.Arithmetic.DigitCosts

/-! The linear and quadratic aggregate-degree costs of equation (digitcost). -/
noncomputable section
namespace WeightedPilz.FreshData
variable {σ K : Type*} [DecidableEq σ] [Field K]

/-- Every distinguished degree has exactly the original fresh cost. -/
theorem fresh_distinguished_degree_cost (S : FreshData σ K) (p e : ℕ) [ExpChar K p] :
    weight (S.freshSum ^ p ^ e) = S.vars.card := by
  rw [weight_pow_expChar, S.weight_freshSum]

/-- In characteristic zero, every degree at least two costs at least the quadratic row. -/
theorem fresh_square_le_weight_pow_charZero [CharZero K] (S : FreshData σ K)
    {d : ℕ} (hd : 2 ≤ d) :
    S.vars.card * (S.vars.card + 1) / 2 ≤ weight (S.freshSum ^ d) := by
  rw [S.weight_freshSum_pow_charZero]
  exact Arithmetic.half_succ_le_choose_cost (Finset.card_pos.mpr S.nonempty) hd

/-- In prime characteristic, every nondistinguished positive degree has quadratic cost. -/
theorem fresh_square_le_weight_pow_of_not_charPower (S : FreshData σ K) (p : ℕ)
    [Fact p.Prime] [CharP K p] {d : ℕ} (hd : 0 < d) (hnd : ∀ e : ℕ, d ≠ p ^ e) :
    S.vars.card * (S.vars.card + 1) / 2 ≤ weight (S.freshSum ^ d) := by
  rw [S.weight_freshSum_pow_digits p]
  exact Arithmetic.half_succ_le_digitCost (Finset.card_pos.mpr S.nonempty)
    (show 1 < p from (Fact.out : Nat.Prime p).one_lt) hd hnd

/-- The quadratic half of equation (digitcost), unified by exponential characteristic. -/
theorem fresh_nondistinguished_degree_cost (S : FreshData σ K) (p : ℕ) [hpK : ExpChar K p]
    {d : ℕ} (hd : 0 < d) (hnd : ∀ e : ℕ, d ≠ p ^ e) :
    S.vars.card * (S.vars.card + 1) / 2 ≤ weight (S.freshSum ^ d) := by
  cases hpK with
  | zero =>
    have hd1 : d ≠ 1 := by simpa using hnd 0
    exact S.fresh_square_le_weight_pow_charZero (by omega)
  | prime hp =>
    letI : Fact p.Prime := ⟨hp⟩
    exact S.fresh_square_le_weight_pow_of_not_charPower p hd hnd

/-- The same quadratic cost applies to every base-only coefficient polynomial. -/
theorem fresh_nondistinguished_row_cost (S : FreshData σ K) (p : ℕ) [ExpChar K p]
    {d : ℕ} (hd : 0 < d) (hnd : ∀ e : ℕ, d ≠ p ^ e)
    (B : MvPolynomial σ K) (hB : S.BaseOnly B) :
    (S.vars.card * (S.vars.card + 1) / 2) * weight B ≤ weight (S.freshSum ^ d * B) := by
  rw [S.weight_freshSum_pow_mul_baseOnly d B hB]
  exact Nat.mul_le_mul_right _ (S.fresh_nondistinguished_degree_cost p hd hnd)

end WeightedPilz.FreshData

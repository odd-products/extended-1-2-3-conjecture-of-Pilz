import WeightedPilz.FreshCosts
import WeightedPilz.SupportProduct
import WeightedPilz.Arithmetic.FreshPureCost

/-! Multiplicative costs for aggregate rows with base-only coefficients. -/
noncomputable section
namespace WeightedPilz.FreshData
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [DecidableEq σ] [Field K]

/-- A fresh aggregate power has no exponent outside the chosen fresh variables. -/
theorem support_freshSum_pow_outside (S : FreshData σ K) (n : ℕ)
    {z : σ} (hz : z ∉ S.vars) {d : σ →₀ ℕ} (hd : d ∈ (S.freshSum ^ n).support) :
    d z = 0 := by
  have hbase : ∀ e ∈ S.freshSum.support, freshExponentDegree {z} e = 0 := by
    intro e he
    rw [S.support_freshSum] at he
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp he
    have hyz : y ≠ z := by intro h; exact hz (h ▸ hy)
    simp [freshExponentDegree, Finsupp.single_apply, hyz]
  have h := support_pow_fresh_degree {z} S.freshSum 0 n hbase d hd
  simpa [freshExponentDegree] using h

/-- Fresh and base coordinates separate every pair of terms, in every degree and characteristic. -/
theorem weight_freshSum_pow_mul_baseOnly (S : FreshData σ K) (n : ℕ)
    (B : MvPolynomial σ K) (hB : S.BaseOnly B) :
    weight (S.freshSum ^ n * B) = weight (S.freshSum ^ n) * weight B := by
  apply weight_mul_of_injective_support_add
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  obtain ⟨hc, hd⟩ := Finset.mem_product.mp hcd
  have hac : a = c := by
    ext z
    by_cases hz : z ∈ S.vars
    · have hzEq := congrArg (fun e : σ →₀ ℕ => e z) heq
      simpa only [Finsupp.add_apply, hB z hz b hb, hB z hz d hd, add_zero] using hzEq
    · rw [S.support_freshSum_pow_outside n hz ha, S.support_freshSum_pow_outside n hz hc]
  have hbd : b = d := by
    apply add_left_cancel (a := a)
    simpa only [← hac] using heq
  exact Prod.ext hac hbd

/-- The elementary positive-degree lower cost, including arbitrary base-only coefficients. -/
theorem fresh_card_mul_weight_le_weight_row (S : FreshData σ K) {n : ℕ}
    (hn : 0 < n) (B : MvPolynomial σ K) (hB : S.BaseOnly B) :
    S.vars.card * weight B ≤ weight (S.freshSum ^ n * B) := by
  rw [S.weight_freshSum_pow_mul_baseOnly n B hB]
  exact Nat.mul_le_mul_right _ (S.fresh_card_le_weight_pow hn)

end WeightedPilz.FreshData

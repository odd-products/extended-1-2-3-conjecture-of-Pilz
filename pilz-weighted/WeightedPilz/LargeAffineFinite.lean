import WeightedPilz.LargeAffine
import WeightedPilz.CoreBudgets

/-! Finite endpoint-and-square argument for all affine cofactors from 67 to 228. -/

noncomputable section
namespace WeightedPilz

open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K]

private theorem exists_scalar_monomial_of_weight_one (B : Poly K) (hB : weight B = 1) :
    ∃ (d : ℕ →₀ ℕ) (b : K), b ≠ 0 ∧ B = monomial d b := by
  classical
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hB
  have hc : coeff d B ≠ 0 := mem_support_iff.mp (by rw [hd]; simp)
  refine ⟨d, coeff d B, hc, ?_⟩
  conv_lhs => rw [MvPolynomial.as_sum B, hd]
  simp

/-- The κ+R+r and κ+R+h+1 budgets leave only a cancelled middle row and
one monomial in B; the pure-square row bound excludes that case. -/
theorem large_affine_budget_finite (n : ℕ) (c : ℕ → K) (D B : Poly K)
    (hc : NonzeroWeights n c) (hn : 67 ≤ n) (hn228 : n ≤ 228)
    (hne : D ≠ 0 ∨ B ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsmall : ∀ j ≤ Nat.sqrt n, ∀ w : ℕ → K, NonzeroWeights j w → IntervalBound j w) :
    n ≤ weight (intervalCore n c * D) + Pilz.freshCount n * weight (D + intervalCore n c * B) +
      Arithmetic.squareCost n * weight B := by
  classical
  have hr := Arithmetic.fresh_count_eight n hn
  have hR := Arithmetic.fresh_le_squareCost n
  change Pilz.freshCount n ≤ Arithmetic.squareCost n at hR
  by_cases hB : B = 0
  · have hD : D ≠ 0 := by simpa [hB] using hne
    simpa [hB, weight] using large_base_unrestricted n c D hc hn hD
  by_cases hD : D = 0
  · have hbase := large_base_unrestricted n c B hc hn hB
    have hfirst : weight (intervalCore n c * B) ≤
        Pilz.freshCount n * weight (intervalCore n c * B) := by nlinarith
    have hsecond := Nat.mul_le_mul_right (weight B) hR
    simp only [hD, mul_zero, weight_zero, zero_add]
    omega
  have hk := (intervalCore_endpoint_distance n c hc (by omega) hsmall).trans
    (distance_le_weight_mul _ D hD)
  obtain ⟨hbudget1, hbudget2⟩ := Arithmetic.endpointBudgets hn hn228
  change n ≤ Arithmetic.endpoint n + Arithmetic.squareCost n + Pilz.freshCount n at hbudget1
  have hbpos : 1 ≤ weight B := weight_pos hB
  by_contra hnot
  have hshort : weight (intervalCore n c * D) +
      Pilz.freshCount n * weight (D + intervalCore n c * B) +
      Arithmetic.squareCost n * weight B < n := by omega
  have hbwt : weight B = 1 := by
    by_contra hne1
    have hb2 : 2 ≤ weight B := by omega
    have hmul : Arithmetic.squareCost n + Pilz.freshCount n ≤
        Arithmetic.squareCost n * weight B := by nlinarith
    omega
  have hmiddle : D + intervalCore n c * B = 0 := by
    by_contra hmid
    have hmpos : 1 ≤ weight (D + intervalCore n c * B) := weight_pos hmid
    have hmul := Nat.mul_le_mul_left (Pilz.freshCount n) hmpos
    rw [hbwt, mul_one] at hshort
    omega
  have hDexact : D = -(intervalCore n c * B) := eq_neg_of_add_eq_zero_left hmiddle
  obtain ⟨d, b, hb, hBexact⟩ := exists_scalar_monomial_of_weight_one B hbwt
  have hsquare : weight (intervalCore n c * D) = weight (intervalCore n c ^ 2) := by
    rw [hDexact, mul_neg]
    simp only [weight, support_neg]
    change weight (intervalCore n c * (intervalCore n c * B)) = _
    rw [← mul_assoc, ← pow_two, hBexact, mul_comm, weight_scalar_monomial_mul d hb]
    rfl
  have hs := intervalCore_square_weight n c hc (by omega) h2 hsmall
  rw [hsquare, hmiddle, weight_zero, mul_zero, add_zero, hbwt, mul_one] at hshort
  omega

/-- The full arithmetic affine bound from 67 onward. The finite component
induction asks only for the weighted theorem through 15. -/
theorem large_affine_budget_all (n : ℕ) (c : ℕ → K) (D B : Poly K)
    (hc : NonzeroWeights n c) (hn : 67 ≤ n)
    (hne : D ≠ 0 ∨ B ≠ 0) (h2 : (2 : K) ≠ 0)
    (hinitial : ∀ j ≤ 15, ∀ w : ℕ → K, NonzeroWeights j w → IntervalBound j w) :
    n ≤ weight (intervalCore n c * D) + Pilz.freshCount n * weight (D + intervalCore n c * B) +
      Arithmetic.squareCost n * weight B := by
  by_cases hn228 : n ≤ 228
  · have hs : Nat.sqrt n ≤ 15 := by
      have hh : Nat.sqrt n < 16 := Nat.sqrt_lt.mpr (by omega)
      omega
    exact large_affine_budget_finite n c D B hc hn hn228 hne h2
      (fun j hj w hw => hinitial j (hj.trans hs) w hw)
  · exact large_affine_budget n c D B hc (by omega) hne

theorem large_affine_all (n : ℕ) (c : ℕ → K) (D B : Poly K)
    (hc : NonzeroWeights n c) (hn : 67 ≤ n)
    (hDb : ∀p∈intervalFreshPrimes n, ∀d∈D.support, d p = 0)
    (hBb : ∀p∈intervalFreshPrimes n, ∀d∈B.support, d p = 0)
    (hne : D ≠ 0 ∨ B ≠ 0) (h2 : (2 : K) ≠ 0)
    (hinitial : ∀ j ≤ 15, ∀ w : ℕ → K, NonzeroWeights j w → IntervalBound j w) :
    n ≤ weight ((intervalCore n c + ∑p∈intervalFreshPrimes n, X p) *
      (D + (∑p∈intervalFreshPrimes n, X p) * B)) := by
  have hr : (intervalFreshPrimes n).Nonempty := by
    apply Finset.card_pos.mp
    rw [Pilz.card_freshPrimes]
    have h := Arithmetic.fresh_count_eight n hn
    omega
  let S := intervalFreshData n c (show 0 < n by omega) hc hr
  have heq := S.weight_mul_affine D B hDb hBb h2
  change weight ((intervalCore n c + ∑p∈intervalFreshPrimes n, X p) *
    (D + (∑p∈intervalFreshPrimes n, X p) * B)) =
    weight (intervalCore n c * D) + (intervalFreshPrimes n).card *
      weight (D + intervalCore n c * B) +
      ((intervalFreshPrimes n).card * ((intervalFreshPrimes n).card + 1) / 2) * weight B at heq
  rw [Pilz.card_freshPrimes] at heq
  rw [heq]
  exact large_affine_budget_all n c D B hc hn hne h2 hinitial

end WeightedPilz

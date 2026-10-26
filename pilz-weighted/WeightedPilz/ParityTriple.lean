import WeightedPilz.Initial
import WeightedPilz.PrimeRigidity

/-! The sharp three-term input costs used by parity pairing. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K] [ExpChar K 2]

/-- Five output terms force a prime-index rigid cofactor, which cannot have
three terms. This argument works over imperfect fields as well. -/
theorem interval_five_three_term (c : ℕ → K) (hc : NonzeroWeights 5 c)
    (F : Poly K) (hFwt : weight F = 3) : 6 ≤ weight (interval 5 c * F) := by
  classical
  have hF : F ≠ 0 := by intro h; simp [h] at hFwt
  have hlow := intervalBound_le_eight 5 (by decide) c hc F hF
  by_contra hnot
  have heq : weight (interval 5 c * F) = 5 := by omega
  have hc4 : NonzeroWeights 4 c := by
    intro a ha
    exact hc a (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1,
      (Finset.mem_Icc.mp ha).2.trans (by decide)⟩)
  obtain ⟨e, d, a, ha, _, hform⟩ :=
    prime_index_multiplier_rigidity_of_predecessor_bound 2 5 (by decide) (by decide)
      c hc (intervalBound_le_eight 4 (by decide) c hc4) F hF heq
  have hwt : weight (interval 5 c ^ (2 ^ e - 1)) = 3 := by
    rwa [hform, weight_scalar_monomial_mul d ha] at hFwt
  by_cases he : e = 0
  · simp only [he, pow_zero, Nat.sub_self] at hwt
    change (monomial (0 : ℕ →₀ ℕ) (1 : K)).support.card = 3 at hwt
    rw [support_monomial, if_neg one_ne_zero, Finset.card_singleton] at hwt
    omega
  · have hexp : 2 ≤ 2 ^ e := by
      have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 1 ≤ e by omega)
      simpa using h
    have hsplit : 2 ^ e - 1 = (2 ^ e - 2) + 1 := by omega
    have hP : interval 5 c ≠ 0 := interval_ne_zero c (by decide) hc
    have h := intervalBound_le_eight 5 (by decide) c hc
      (interval 5 c ^ (2 ^ e - 2)) (pow_ne_zero _ hP)
    rw [hsplit, pow_succ, mul_comm] at hwt
    omega

/-- The literal cost function from Lemma `fin-parity-pair`. -/
def tripleIntervalCost (k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then 3 else if k = 5 then 6 else k

theorem interval_three_term_cost (k : ℕ) (hk : k ≤ 6) (c : ℕ → K)
    (hc : NonzeroWeights k c) (F : Poly K) (hFwt : weight F = 3) :
    tripleIntervalCost k ≤ weight (interval k c * F) := by
  have hF : F ≠ 0 := by intro h; simp [h] at hFwt
  by_cases hk0 : k = 0
  · simp [tripleIntervalCost, hk0]
  by_cases hk1 : k = 1
  · subst k
    have hc1 : c 1 ≠ 0 := hc 1 (by simp)
    have hI : interval 1 c = monomial 0 (c 1) := by
      simp [interval, polynomialOf, monomialOf]
    rw [hI, weight_scalar_monomial_mul 0 hc1, hFwt]
    decide
  by_cases hk5 : k = 5
  · subst k
    exact interval_five_three_term c hc F hFwt
  · simpa only [tripleIntervalCost, if_neg hk0, if_neg hk1, if_neg hk5] using
      intervalBound_le_eight k (by omega) c hc F hF

end WeightedPilz

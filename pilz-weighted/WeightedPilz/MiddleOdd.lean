import WeightedPilz.MiddleOddRegular
import WeightedPilz.MiddleCharThreeRegular
import WeightedPilz.MiddleCubeExceptions

/-! The frozen middle-interval theorem in every characteristic other than two. -/
noncomputable section
namespace WeightedPilz
variable {K : Type*} [Field K]

theorem intervalBound_middle_charThree [CharP K 3] (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66) : IntervalBound n c := by
  by_cases h27 : n = 27
  · exact intervalBound_middle_charThree_exceptional n (Or.inl h27) c hc
  by_cases h28 : n = 28
  · exact intervalBound_middle_charThree_exceptional n (Or.inr h28) c hc
  exact intervalBound_middle_charThree_regular n c hc hn hn' h27 h28

theorem intervalBound_middle_odd (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hn : 25 ≤ n) (hn' : n ≤ 66)
    (h2 : (2 : K) ≠ 0) : IntervalBound n c := by
  obtain ⟨p, hpchar⟩ := CharP.exists K
  letI : CharP K p := hpchar
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · by_cases hp3 : p = 3
    · subst p
      exact intervalBound_middle_charThree n c hc hn hn'
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      exact h2 ((CharP.cast_eq_zero_iff K 2 2).mpr dvd_rfl)
    have hp4 : p ≠ 4 := by
      intro heq
      subst p
      exact (by decide : ¬ Nat.Prime 4) hp
    have hp5 : 5 ≤ p := by have := hp.two_le; omega
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    exact intervalBound_middle_charLarge p hp5 n c hc hn hn'
  · letI : CharZero K := CharP.charP_to_charZero K
    exact intervalBound_middle_charZero n c hc hn hn'

end WeightedPilz

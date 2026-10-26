import WeightedPilz.MiddleOdd
import WeightedPilz.BinaryMiddle

/-! The weighted interval theorem throughout the middle range, in every field. -/

noncomputable section
namespace WeightedPilz
variable {K : Type*} [Field K]

theorem intervalBound_middle (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c)
    (hn25 : 25 ≤ n) (hn66 : n ≤ 66) : IntervalBound n c := by
  obtain ⟨p, hpchar⟩ := CharP.exists K
  letI : CharP K p := hpchar
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · by_cases hp2 : p = 2
    · subst p
      exact intervalBound_middle_charTwo n c hc hn25 hn66
    have h2 : (2 : K) ≠ 0 := by
      intro hz
      have hdiv := (CharP.cast_eq_zero_iff K p 2).mp hz
      rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | htwo
      · exact hp.ne_one h1
      · exact hp2 htwo
    exact intervalBound_middle_odd n c hc hn25 hn66 h2
  · letI : CharZero K := CharP.charP_to_charZero K
    exact intervalBound_middle_odd n c hc hn25 hn66 (by norm_num)

end WeightedPilz

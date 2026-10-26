import WeightedPilz.Arithmetic.DigitCosts
import Mathlib.Data.Nat.Prime.Basic

/-! The exact three-term digit cost needed by the initial interval argument. -/

namespace WeightedPilz.Arithmetic

/-- A two-variable digit product equal to three has exactly one nonzero digit,
and that digit is two. The base need not be prime. -/
theorem digitCost_two_eq_three {p d : ℕ} (hp : 1 < p)
    (hd : digitCost 2 p d = 3) : 2 < p ∧ ∃ e : ℕ, d = 2 * p ^ e := by
  revert hd
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    have hd0 : d ≠ 0 := by
      intro h
      subst d
      simp [digitCost] at hd
    have hq : d / p < d := Nat.div_lt_self (Nat.pos_of_ne_zero hd0) hp
    have hdiv := Nat.mod_add_div d p
    rw [digitCost_step hp hd0,
      show 2 + d % p - 1 = d % p + 1 by omega,
      Nat.choose_succ_self_right] at hd
    have hfactor : d % p + 1 ∣ 3 := ⟨digitCost 2 p (d / p), hd.symm⟩
    rcases (by decide : Nat.Prime 3).eq_one_or_self_of_dvd (d % p + 1) hfactor
      with hm | hm
    · have hm0 : d % p = 0 := by omega
      have htail : digitCost 2 p (d / p) = 3 := by simpa [hm0] using hd
      obtain ⟨hp2, e, he⟩ := ih (d / p) hq htail
      refine ⟨hp2, e + 1, ?_⟩
      calc
        d = p * (d / p) := by simpa [hm0] using hdiv.symm
        _ = p * (2 * p ^ e) := by rw [he]
        _ = 2 * p ^ (e + 1) := by
          simp only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    · have hm2 : d % p = 2 := by omega
      have htail : digitCost 2 p (d / p) = 1 := by
        rw [hm] at hd
        omega
      have hq0 : d / p = 0 := by
        by_contra h
        have hcost := le_digitCost (by decide : 1 ≤ 2) hp (Nat.pos_of_ne_zero h)
        omega
      have hp2 : 2 < p := by
        have := Nat.mod_lt d (by omega : 0 < p)
        omega
      refine ⟨hp2, 0, ?_⟩
      simpa [hm2, hq0] using hdiv.symm

end WeightedPilz.Arithmetic

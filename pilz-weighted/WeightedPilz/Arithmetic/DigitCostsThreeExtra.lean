import WeightedPilz.Arithmetic.DigitCosts

/-! Equality in the three-variable quadratic digit cost. -/
namespace WeightedPilz.Arithmetic

theorem digitCost_three_eq_six {p d : ℕ} (hp : 1 < p)
    (hd : digitCost 3 p d = 6) : 2 < p ∧ ∃ e : ℕ, d = 2 * p ^ e := by
  revert hd
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    have hd0 : d ≠ 0 := by
      intro hz
      subst d
      simp [digitCost] at hd
    have hq : d / p < d := Nat.div_lt_self (Nat.pos_of_ne_zero hd0) hp
    have hdiv := Nat.mod_add_div d p
    rw [digitCost_step hp hd0] at hd
    by_cases hm0 : d % p = 0
    · have htail : digitCost 3 p (d / p) = 6 := by simpa [hm0] using hd
      obtain ⟨hp2, e, he⟩ := ih (d / p) hq htail
      refine ⟨hp2, e + 1, ?_⟩
      calc
        d = p * (d / p) := by simpa [hm0] using hdiv.symm
        _ = p * (2 * p ^ e) := by rw [he]
        _ = 2 * p ^ (e + 1) := by simp only [pow_succ, Nat.mul_assoc, Nat.mul_comm]
    · have hfactor : (3 + d % p - 1).choose (d % p) ≤ 6 := by
        have hpos := digitCost_pos (r := 3) (p := p) (d := d / p) (by decide)
        have hle := Nat.le_mul_of_pos_right ((3 + d % p - 1).choose (d % p)) hpos
        omega
      have hmle : d % p ≤ 2 := by
        by_contra hn
        have hle := choose_cost_mono (r := 3) (a := 3) (b := d % p)
          (by decide) (by omega)
        change 10 ≤ (3 + d % p - 1).choose (d % p) at hle
        omega
      have hm2 : d % p = 2 := by
        by_contra hn
        have hm1 : d % p = 1 := by omega
        have htail : digitCost 3 p (d / p) = 2 := by
          simp only [hm1] at hd
          change 3 * digitCost 3 p (d / p) = 6 at hd
          omega
        by_cases hq0 : d / p = 0
        · simp [hq0, digitCost] at htail
        · have hlarge := le_digitCost (r := 3) (by decide) hp (Nat.pos_of_ne_zero hq0)
          omega
      have htail : digitCost 3 p (d / p) = 1 := by
        simp only [hm2] at hd
        change 6 * digitCost 3 p (d / p) = 6 at hd
        omega
      have hq0 : d / p = 0 := by
        by_contra hn
        have hlarge := le_digitCost (r := 3) (by decide) hp (Nat.pos_of_ne_zero hn)
        omega
      have hp2 : 2 < p := by
        have := Nat.mod_lt d (by omega : 0 < p)
        omega
      refine ⟨hp2, 0, ?_⟩
      simpa [hm2, hq0] using hdiv.symm

end WeightedPilz.Arithmetic

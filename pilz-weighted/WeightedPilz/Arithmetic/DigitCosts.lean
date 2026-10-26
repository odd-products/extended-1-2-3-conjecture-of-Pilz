import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Lean.Elab.Tactic.Omega

/-! Numerical lower bounds for the multinomial digit product. -/

namespace WeightedPilz.Arithmetic

def digitCost (r p d : ℕ) : ℕ :=
  ((Nat.digits p d).map (fun j => (r + j - 1).choose j)).prod

theorem choose_cost_mono {r a b : ℕ} (hr : 1 ≤ r) (hab : a ≤ b) :
    (r + a - 1).choose a ≤ (r + b - 1).choose b := by
  rw [Nat.choose_symm_of_eq_add (show r + a - 1 = a + (r - 1) by omega),
    Nat.choose_symm_of_eq_add (show r + b - 1 = b + (r - 1) by omega)]
  exact Nat.choose_le_choose _ (by omega)

theorem le_choose_cost {r j : ℕ} (hr : 1 ≤ r) (hj : 1 ≤ j) :
    r ≤ (r + j - 1).choose j := by
  simpa using choose_cost_mono hr hj

theorem half_succ_le_choose_cost {r j : ℕ} (hr : 1 ≤ r) (hj : 2 ≤ j) :
    r * (r + 1) / 2 ≤ (r + j - 1).choose j := by
  have h := choose_cost_mono hr hj
  rw [show r + 2 - 1 = r + 1 by omega, Nat.choose_two_right] at h
  simpa [Nat.mul_comm] using h

theorem digitCost_pos {r p d : ℕ} (hr : 1 ≤ r) : 0 < digitCost r p d := by
  suffices h : ∀ l : List ℕ, 0 < (l.map (fun j => (r + j - 1).choose j)).prod by
    exact h (Nat.digits p d)
  intro l
  induction l with
  | nil => simp
  | cons j l ih =>
    simpa only [List.map_cons, List.prod_cons] using
      Nat.mul_pos (Nat.choose_pos (by omega : j ≤ r + j - 1)) ih

theorem digitCost_step {r p d : ℕ} (hp : 1 < p) (hd : d ≠ 0) :
    digitCost r p d = (r + d % p - 1).choose (d % p) * digitCost r p (d / p) := by
  unfold digitCost
  rw [Nat.digits_eq_cons_digits_div hp hd]
  rfl

theorem le_digitCost {r p d : ℕ} (hr : 1 ≤ r) (hp : 1 < p) (hd : 0 < d) :
    r ≤ digitCost r p d := by
  revert hd
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    have hq : d / p < d := Nat.div_lt_self hd hp
    have hdiv := Nat.mod_add_div d p
    rw [digitCost_step hp (Nat.ne_of_gt hd)]
    by_cases hm : d % p = 0
    · have hqp : 0 < d / p := by
        apply Nat.pos_of_ne_zero
        intro hz
        simp only [hm, hz, Nat.mul_zero, Nat.add_zero] at hdiv
        omega
      simpa [hm] using ih (d / p) hq hqp
    · have hj : 1 ≤ d % p := by omega
      exact (le_choose_cost hr hj).trans
        (Nat.le_mul_of_pos_right _ (digitCost_pos hr))

private theorem half_succ_le_square {r : ℕ} (hr : 1 ≤ r) :
    r * (r + 1) / 2 ≤ r * r := by
  have h : r * (r + 1) ≤ (r * r) * 2 := by
    have h' := Nat.mul_le_mul_left r (show r + 1 ≤ r * 2 by omega)
    simpa [Nat.mul_assoc] using h'
  have h' := Nat.div_le_div_right (c := 2) h
  simpa using h'

/-- A degree which is not a characteristic power costs at least the square row. -/
theorem half_succ_le_digitCost {r p d : ℕ} (hr : 1 ≤ r) (hp : 1 < p)
    (hd : 0 < d) (hnd : ∀ e : ℕ, d ≠ p ^ e) :
    r * (r + 1) / 2 ≤ digitCost r p d := by
  revert hd hnd
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd hnd
    have hq : d / p < d := Nat.div_lt_self hd hp
    have hdiv := Nat.mod_add_div d p
    rw [digitCost_step hp (Nat.ne_of_gt hd)]
    by_cases hm0 : d % p = 0
    · have hqp : 0 < d / p := by
        apply Nat.pos_of_ne_zero
        intro hz
        simp only [hm0, hz, Nat.mul_zero, Nat.add_zero] at hdiv
        omega
      have hnp : ∀ e : ℕ, d / p ≠ p ^ e := by
        intro e he
        apply hnd (e + 1)
        calc
          d = (d / p) * p := by simpa [hm0, Nat.mul_comm] using hdiv.symm
          _ = p ^ e * p := by rw [he]
          _ = p ^ (e + 1) := (pow_succ p e).symm
      simpa [hm0] using ih (d / p) hq hqp hnp
    · by_cases hm1 : d % p = 1
      · have hqp : 0 < d / p := by
          apply Nat.pos_of_ne_zero
          intro hz
          have hn1 := hnd 0
          simp only [pow_zero] at hn1
          simp only [hm1, hz, Nat.mul_zero, Nat.add_zero] at hdiv
          omega
        have hmul := Nat.mul_le_mul_left r (le_digitCost hr hp hqp)
        simpa [hm1] using (half_succ_le_square hr).trans hmul
      · have hj : 2 ≤ d % p := by omega
        exact (half_succ_le_choose_cost hr hj).trans
          (Nat.le_mul_of_pos_right _ (digitCost_pos hr))

end WeightedPilz.Arithmetic

import Pilz.SievePrimes
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! The odd-integer product estimate from the paper, proved by adding the
successive odd cutoffs. Composite factors can only decrease the product. -/
noncomputable section
namespace Pilz
open scoped BigOperators

theorem sieveDensity_pos (q : ℕ) : 0 < sieveDensity q := by
  unfold sieveDensity
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (primesUpTo_prime q p hp).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hdiv : (1 : ℝ) / p < 1 := (div_lt_iff₀ hp0).mpr (by linarith)
  linarith

theorem sieveDensity_succ (n : ℕ) :
    sieveDensity (n + 1) = sieveDensity n *
      (if Nat.Prime (n + 1) then 1 - 1 / (n + 1 : ℝ) else 1) := by
  unfold sieveDensity primesUpTo
  rw [Finset.range_add_one]
  by_cases hp : Nat.Prime (n + 1)
  · simp [Finset.filter_insert, hp, Finset.mem_filter, mul_comm]
  · simp [Finset.filter_insert, hp]

theorem sieveDensity_odd_step (k : ℕ) :
    sieveDensity (2 * k + 3) * (1 - 1 / (2 * k + 5 : ℝ)) ≤ sieveDensity (2 * k + 5) := by
  have hnot : ¬Nat.Prime (2 * k + 4) := by
    intro hp
    rcases hp.eq_two_or_odd with h | h <;> omega
  have hfirst := sieveDensity_succ (2 * k + 3)
  have hsecond := sieveDensity_succ (2 * k + 4)
  have heq : sieveDensity (2 * k + 4) = sieveDensity (2 * k + 3) := by
    simpa [hnot] using hfirst
  rw [show 2 * k + 4 + 1 = 2 * k + 5 by omega, heq] at hsecond
  by_cases hp : Nat.Prime (2 * k + 5)
  · norm_num [hp, add_assoc] at hsecond ⊢
    exact hsecond.ge
  · simp only [hp, if_false, mul_one] at hsecond
    rw [hsecond]
    have hfactor : (1 : ℝ) - 1 / (2 * k + 5) ≤ 1 := by
      have hnonneg : (0 : ℝ) ≤ 1 / (2 * k + 5) := by positivity
      linarith
    exact mul_le_of_le_one_right (sieveDensity_pos _).le hfactor

theorem sieveDensity_odd_square_lower (k : ℕ) :
    (1 / 4 : ℝ) < (2 * k + 3) * (sieveDensity (2 * k + 3)) ^ 2 := by
  induction k with
  | zero =>
      norm_num [sieveDensity, primesUpTo, Finset.prod_filter, Finset.prod_range_succ,
        show Nat.Prime 3 by decide, show Nat.Prime 2 by decide, show ¬Nat.Prime 1 by decide]
  | succ k ih =>
      let a : ℝ := 2 * k + 3
      let r : ℝ := sieveDensity (2 * k + 3)
      let f : ℝ := 1 - 1 / (a + 2)
      have ha : 0 < a := by dsimp [a]; positivity
      have hr : 0 < r := sieveDensity_pos _
      have hf : 0 < f := by
        dsimp [f]
        have hdiv : (1 : ℝ) / (a + 2) < 1 := (div_lt_iff₀ (by linarith)).mpr (by linarith)
        linarith
      have hstep : r * f ≤ sieveDensity (2 * k + 5) := by
        convert sieveDensity_odd_step k using 1 <;>
          norm_num [r, f, a, Nat.cast_add, Nat.cast_mul, add_assoc]
      have hsq := (sq_le_sq₀ (mul_pos hr hf).le (sieveDensity_pos _).le).mpr hstep
      have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ a + 2 by linarith)
      have hid : (a + 2) * (r * f) ^ 2 = a * r ^ 2 + r ^ 2 / (a + 2) := by
        dsimp [f]
        field_simp
        <;> ring
      have hpos : 0 < r ^ 2 / (a + 2) := div_pos (sq_pos_of_pos hr) (by linarith)
      have hih : (1 / 4 : ℝ) < a * r ^ 2 := by simpa [a, r] using ih
      have hres : (1 / 4 : ℝ) < (a + 2) * (sieveDensity (2 * k + 5)) ^ 2 := by
        rw [hid] at hm
        linarith
      convert hres using 1 <;>
        norm_num [a, Nat.cast_add, Nat.cast_mul, mul_add, add_assoc]

/-- The manuscript's odd-integer telescoping bound, for every odd prime. -/
theorem sieveDensity_sqrt_lower {q : ℕ} (hq : Nat.Prime q) (hq3 : 3 ≤ q) :
    1 / (2 * Real.sqrt (q : ℝ)) < sieveDensity q := by
  obtain ⟨j, hj⟩ := hq.odd_of_ne_two (by omega)
  have hj1 : 1 ≤ j := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj1
  have hqeq : q = 2 * k + 3 := by omega
  have hinv : (1 / 4 : ℝ) < (q : ℝ) * sieveDensity q ^ 2 := by
    simpa [hqeq, Nat.cast_add, Nat.cast_mul] using sieveDensity_odd_square_lower k
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hspos := Real.sqrt_pos.mpr hqpos
  have hsquare := Real.sq_sqrt hqpos.le
  have hr := sieveDensity_pos q
  apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hspos)).mpr
  have hprod := mul_pos hr hspos
  have hinv' : (1 / 4 : ℝ) < (sieveDensity q * Real.sqrt q) ^ 2 := by
    calc
      _ < (q : ℝ) * sieveDensity q ^ 2 := hinv
      _ = (Real.sqrt q) ^ 2 * sieveDensity q ^ 2 := by rw [hsquare]
      _ = _ := by ring
  have hhalf : (1 / 2 : ℝ) < sieveDensity q * Real.sqrt q :=
    (sq_lt_sq₀ (by norm_num) hprod.le).mp (by nlinarith [hinv'])
  nlinarith

end Pilz

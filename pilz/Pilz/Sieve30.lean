import Pilz.Sieve

/-! Exact initial sieve formulas and discrepancy constants for 2, 3, and 5. -/

namespace Pilz

theorem roughCount_two_three_formula (n : ℕ) :
    roughCount {2, 3} n = (n - n / 2) - (n / 3 - n / 3 / 2) := by
  have hset : ({2, 3} : Finset ℕ) = insert 3 {2} := by decide
  rw [hset, roughCount_insert {2} 3 n]
  · rw [roughCount_singleton 2 n (by decide),
      roughCount_singleton 2 (n / 3) (by decide)]
  · intro q hq
    have : q = 2 := Finset.mem_singleton.mp hq
    subst q
    decide
  · decide
  · decide

def sieve30Formula (n : ℕ) : ℕ :=
  ((n - n / 2) - (n / 3 - n / 3 / 2)) -
    ((n / 5 - n / 5 / 2) - (n / 5 / 3 - n / 5 / 3 / 2))

theorem roughCount_two_three_five_formula (n : ℕ) :
    roughCount {2, 3, 5} n = sieve30Formula n := by
  have hset : ({2, 3, 5} : Finset ℕ) = insert 5 {2, 3} := by decide
  rw [hset, roughCount_insert {2, 3} 5 n]
  · rw [roughCount_two_three_formula n, roughCount_two_three_formula (n / 5)]
    rfl
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> decide
  · decide
  · decide

private theorem sieve_inclusion_algebra
    {a b c d e f g n n2 n3 n5 n6 n10 n15 n30 : ℕ}
    (h3 : b + d = a) (h35 : g + f = e) (h5 : c + g = b)
    (h2 : a + n2 = n) (h23 : d + n6 = n3)
    (h25 : e + n10 = n5) (h253 : f + n30 = n15) :
    c + n2 + n3 + n5 + n30 = n + n6 + n10 + n15 := by omega

/-- Inclusion-exclusion with subtraction eliminated. -/
theorem roughCount_five_inclusion_exclusion (n : ℕ) :
    roughCount {2, 3, 5} n + n / 2 + n / 3 + n / 5 + n / 30 =
      n + n / 6 + n / 10 + n / 15 := by
  have hT : ∀ q ∈ ({2, 3} : Finset ℕ), Nat.Prime q := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> decide
  have hT2 : ∀ q ∈ ({2} : Finset ℕ), Nat.Prime q := by
    intro q hq
    have : q = 2 := Finset.mem_singleton.mp hq
    subst q
    decide
  have hs3 : (insert 3 {2} : Finset ℕ) = {2, 3} := by decide
  have hs5 : (insert 5 {2, 3} : Finset ℕ) = {2, 3, 5} := by decide
  have h3 := roughCount_insert_add {2} 3 n hT2 (by decide) (by decide)
  have h35 := roughCount_insert_add {2} 3 (n / 5) hT2 (by decide) (by decide)
  have h5 := roughCount_insert_add {2, 3} 5 n hT (by decide) (by decide)
  rw [hs3] at h3 h35
  rw [hs5] at h5
  have h2 (k : ℕ) : roughCount {2} k + k / 2 = k := by
    rw [roughCount_singleton 2 k (by decide)]
    exact Nat.sub_add_cancel (Nat.div_le_self k 2)
  have h2n := h2 n
  have h23 := h2 (n / 3)
  have h25 := h2 (n / 5)
  have h253 := h2 (n / 5 / 3)
  simp only [Nat.div_div_eq_div_mul] at h23 h25 h253 h35
  exact sieve_inclusion_algebra h3 h35 h5 h2n h23 h25 h253

private theorem sieve_period_algebra {w w0 a b c d e f g n : ℕ}
    (h : w + (a + 15) + (b + 10) + (c + 6) + (d + 1) =
      (n + 30) + (e + 5) + (f + 3) + (g + 2))
    (h0 : w0 + a + b + c + d = n + e + f + g) : w = w0 + 8 := by omega

theorem roughCount_five_add_thirty (n : ℕ) :
    roughCount {2, 3, 5} (n + 30) = roughCount {2, 3, 5} n + 8 := by
  have h := roughCount_five_inclusion_exclusion (n + 30)
  have h0 := roughCount_five_inclusion_exclusion n
  have h2 : (n + 30) / 2 = n / 2 + 15 := Nat.add_mul_div_left n 15 (by decide : 0 < 2)
  have h3 : (n + 30) / 3 = n / 3 + 10 := Nat.add_mul_div_left n 10 (by decide : 0 < 3)
  have h5 : (n + 30) / 5 = n / 5 + 6 := Nat.add_mul_div_left n 6 (by decide : 0 < 5)
  have h6 : (n + 30) / 6 = n / 6 + 5 := Nat.add_mul_div_left n 5 (by decide : 0 < 6)
  have h10 : (n + 30) / 10 = n / 10 + 3 := Nat.add_mul_div_left n 3 (by decide : 0 < 10)
  have h15 : (n + 30) / 15 = n / 15 + 2 := Nat.add_mul_div_left n 2 (by decide : 0 < 15)
  have h30 : (n + 30) / 30 = n / 30 + 1 := Nat.add_div_right n (by decide : 0 < 30)
  rw [h2, h3, h5, h6, h10, h15, h30] at h
  exact sieve_period_algebra h h0

theorem roughCount_five_add_multiple (r k : ℕ) :
    roughCount {2, 3, 5} (r + 30 * k) = roughCount {2, 3, 5} r + 8 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have heq : r + 30 * (k + 1) = (r + 30 * k) + 30 := by omega
    rw [heq, roughCount_five_add_thirty, ih]
    simp only [Nat.mul_succ, Nat.add_assoc]

private theorem small_count_discrepancy : ∀ r : Fin 30,
    15 * sieve30Formula r.val ≤ 4 * r.val + 14 ∧
      4 * r.val ≤ 15 * sieve30Formula r.val + 14 := by decide

private theorem sieve_discrepancy_lift {n r k v vr : ℕ}
    (hn : r + 30 * k = n) (hw : v = vr + 8 * k)
    (hs : 15 * vr ≤ 4 * r + 14 ∧ 4 * r ≤ 15 * vr + 14) :
    15 * v ≤ 4 * n + 14 ∧ 4 * n ≤ 15 * v + 14 := by omega

/-- Integer form of the manuscript's `14/15` discrepancy bound. -/
theorem roughCount_five_discrepancy (n : ℕ) :
    15 * roughCount {2, 3, 5} n ≤ 4 * n + 14 ∧
      4 * n ≤ 15 * roughCount {2, 3, 5} n + 14 := by
  have hs := small_count_discrepancy ⟨n % 30, Nat.mod_lt n (by decide)⟩
  change 15 * sieve30Formula (n % 30) ≤ 4 * (n % 30) + 14 ∧
    4 * (n % 30) ≤ 15 * sieve30Formula (n % 30) + 14 at hs
  rw [← roughCount_two_three_five_formula] at hs
  have hw := roughCount_five_add_multiple (n % 30) (n / 30)
  rw [Nat.mod_add_div] at hw
  have hn := Nat.mod_add_div n 30
  exact sieve_discrepancy_lift hn hw hs

private theorem sieve_interval_period_algebra {a b : ℕ} (h : b ≤ a) :
    (a + 8 + 8) - (b + 8) = a - b + 8 := by omega

theorem roughIntervalCount_five_add_sixty (n : ℕ) :
    roughIntervalCount {2, 3, 5} (n + 60) = roughIntervalCount {2, 3, 5} n + 8 := by
  have hdouble : n + 60 = (n + 30) + 30 := by omega
  have hhalf : (n + 60) / 2 = n / 2 + 30 := Nat.add_mul_div_left n 30 (by decide : 0 < 2)
  unfold roughIntervalCount
  rw [hdouble, roughCount_five_add_thirty, roughCount_five_add_thirty]
  rw [← hdouble, hhalf, roughCount_five_add_thirty]
  have hmono := roughCount_mono {2, 3, 5} (Nat.div_le_self n 2)
  exact sieve_interval_period_algebra hmono

theorem roughIntervalCount_five_add_multiple (r k : ℕ) :
    roughIntervalCount {2, 3, 5} (r + 60 * k) =
      roughIntervalCount {2, 3, 5} r + 8 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have heq : r + 60 * (k + 1) = (r + 60 * k) + 60 := by omega
    rw [heq, roughIntervalCount_five_add_sixty, ih]
    simp only [Nat.mul_succ, Nat.add_assoc]

private theorem small_interval_discrepancy : ∀ r : Fin 60,
    15 * (sieve30Formula r.val - sieve30Formula (r.val / 2)) ≤ 2 * r.val + 22 ∧
      2 * r.val ≤ 15 * (sieve30Formula r.val - sieve30Formula (r.val / 2)) + 22 := by decide

private theorem sieve_interval_discrepancy_lift {n r k v vr : ℕ}
    (hn : r + 60 * k = n) (hw : v = vr + 8 * k)
    (hs : 15 * vr ≤ 2 * r + 22 ∧ 2 * r ≤ 15 * vr + 22) :
    15 * v ≤ 2 * n + 22 ∧ 2 * n ≤ 15 * v + 22 := by omega

/-- Integer form of the manuscript's sharper half-interval discrepancy. -/
theorem roughIntervalCount_five_discrepancy (n : ℕ) :
    15 * roughIntervalCount {2, 3, 5} n ≤ 2 * n + 22 ∧
      2 * n ≤ 15 * roughIntervalCount {2, 3, 5} n + 22 := by
  have hs := small_interval_discrepancy ⟨n % 60, Nat.mod_lt n (by decide)⟩
  change 15 * (sieve30Formula (n % 60) - sieve30Formula (n % 60 / 2)) ≤
    2 * (n % 60) + 22 ∧ 2 * (n % 60) ≤
    15 * (sieve30Formula (n % 60) - sieve30Formula (n % 60 / 2)) + 22 at hs
  rw [← roughCount_two_three_five_formula, ← roughCount_two_three_five_formula] at hs
  change 15 * roughIntervalCount {2, 3, 5} (n % 60) ≤ 2 * (n % 60) + 22 ∧
    2 * (n % 60) ≤ 15 * roughIntervalCount {2, 3, 5} (n % 60) + 22 at hs
  have hw := roughIntervalCount_five_add_multiple (n % 60) (n / 60)
  rw [Nat.mod_add_div] at hw
  have hn := Nat.mod_add_div n 60
  exact sieve_interval_discrepancy_lift hn hw hs

private theorem small_count_lower_ten : ∀ r : Fin 30,
    4 * r.val ≤ 15 * sieve30Formula r.val + 10 := by decide

private theorem count_lower_lift {n r k v vr : ℕ}
    (hn : r + 30 * k = n) (hw : v = vr + 8 * k)
    (hs : 4 * r ≤ 15 * vr + 10) : 4 * n ≤ 15 * v + 10 := by omega

/-- The sharper integer lower error leaves room for real interpolation. -/
theorem roughCount_five_lower_ten (n : ℕ) :
    4 * n ≤ 15 * roughCount {2, 3, 5} n + 10 := by
  have hs := small_count_lower_ten ⟨n % 30, Nat.mod_lt n (by decide)⟩
  change 4 * (n % 30) ≤ 15 * sieve30Formula (n % 30) + 10 at hs
  rw [← roughCount_two_three_five_formula] at hs
  have hw := roughCount_five_add_multiple (n % 30) (n / 30)
  rw [Nat.mod_add_div] at hw
  exact count_lower_lift (Nat.mod_add_div n 30) hw hs

private theorem small_interval_lower_twenty : ∀ r : Fin 60,
    2 * r.val ≤ 15 * (sieve30Formula r.val - sieve30Formula (r.val / 2)) + 20 := by decide

private theorem interval_lower_lift {n r k v vr : ℕ}
    (hn : r + 60 * k = n) (hw : v = vr + 8 * k)
    (hs : 2 * r ≤ 15 * vr + 20) : 2 * n ≤ 15 * v + 20 := by omega

theorem roughIntervalCount_five_lower_twenty (n : ℕ) :
    2 * n ≤ 15 * roughIntervalCount {2, 3, 5} n + 20 := by
  have hs := small_interval_lower_twenty ⟨n % 60, Nat.mod_lt n (by decide)⟩
  change 2 * (n % 60) ≤
    15 * (sieve30Formula (n % 60) - sieve30Formula (n % 60 / 2)) + 20 at hs
  rw [← roughCount_two_three_five_formula, ← roughCount_two_three_five_formula] at hs
  change 2 * (n % 60) ≤ 15 * roughIntervalCount {2, 3, 5} (n % 60) + 20 at hs
  have hw := roughIntervalCount_five_add_multiple (n % 60) (n / 60)
  rw [Nat.mod_add_div] at hw
  exact interval_lower_lift (Nat.mod_add_div n 60) hw hs

end Pilz

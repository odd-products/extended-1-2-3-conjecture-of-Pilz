import Pilz.Sieve30

/-! Elementary rough-number bounds for two distinct prime variables.
The pair 2,3 has one exceptional residue class; its index-two component
provides exactly the extra term needed away from n=4. -/

namespace Pilz

private theorem roughCount_pair_add (p q n : ℕ) (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hpq : p < q) :
    roughCount {p, q} n + roughCount {p} (n / q) = roughCount {p} n := by
  have h := roughCount_insert_add {p} q n
    (by intro r hr; simpa only [Finset.mem_singleton.mp hr] using hp) hq
    (by simpa using ne_of_gt hpq)
  have hset : insert q ({p} : Finset ℕ) = {p, q} := by
    ext r
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hset] at h
  exact h

/-- Except for the pair 2,3, three copies of the rough count cover n. -/
theorem roughCount_two_primes_three (p q n : ℕ) (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hpq : p < q) (hexcept : p ≠ 2 ∨ q ≠ 3) :
    n ≤ 3 * roughCount {p, q} n := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hq4 : q ≠ 4 := by
    intro h
    subst q
    exact (by decide : ¬Nat.Prime 4) hq
  have hrec := roughCount_pair_add p q n hp hq hpq
  by_cases hpEq : p = 2
  · subst p
    have hq5 : 5 ≤ q := by omega
    have hdiv : n / q ≤ n / 5 := Nat.div_le_div_left hq5 (by decide)
    have hmono := roughCount_mono {2} hdiv
    rw [roughCount_two, roughCount_two] at hrec
    rw [roughCount_two, roughCount_two] at hmono
    omega
  · have hp3 : 3 ≤ p := by omega
    have hq5 : 5 ≤ q := by omega
    have hdivp : n / p ≤ n / 3 := Nat.div_le_div_left hp3 (by decide)
    have hdivq : n / q ≤ n / 5 := Nat.div_le_div_left hq5 (by decide)
    have hle := roughCount_le {p} (n / q)
    rw [roughCount_singleton p n hp] at hrec
    have hpLe : n / p ≤ n := Nat.div_le_self n p
    omega

theorem roughCount_two_three_index_two_of_residue (n : ℕ) (hn : 10 ≤ n)
    (hmod : n % 6 = 4) :
    1 ≤ roughCount {2, 3} (n / 2) - roughCount {2, 3} (n / 3) := by
  rw [roughCount_two_three_formula, roughCount_two_three_formula]
  omega

/-- The small exceptional residue is supplemented by the rough components
of index two. The only positive exception above n=1 is n=4. -/
theorem roughCount_two_three_with_index_two (n : ℕ) (hn : 5 ≤ n) :
    n ≤ 3 * roughCount {2, 3} n +
      (roughCount {2, 3} (n / 2) - roughCount {2, 3} (n / 3)) := by
  by_cases hmod : n % 6 = 4
  · have hbonus := roughCount_two_three_index_two_of_residue n (by omega) hmod
    have hdisc : n ≤ 3 * roughCount {2, 3} n + 1 := by
      rw [roughCount_two_three_formula]
      omega
    omega
  · have hbase : n ≤ 3 * roughCount {2, 3} n := by
      rw [roughCount_two_three_formula]
      omega
    omega

end Pilz

import Pilz.LocalizedFinite
import Pilz.SievePrimes
import Mathlib.Tactic.NormNum.Prime

/-! The large-q count in the manuscript: the 11-rough integers include one,
all primes above eleven, and the two composites 169 and 221. -/

noncomputable section

namespace Pilz

private theorem primesUpTo_eleven_exact :
    primesUpTo 11 = ({2, 3, 5, 7, 11} : Finset ℕ) := by decide

theorem roughDiscrepancy_eleven :
    RoughDiscrepancy (primesUpTo 11) (16 / 77) (56 / 15) := by
  have h := roughDiscrepancy_union ({2, 3, 5} : Finset ℕ) ({7, 11} : Finset ℕ)
    (4 / 15) (14 / 15)
    (by intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl <;> decide)
    (by intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl <;> decide)
    (by decide) roughRealCount_five_discrepancy
  have hset : ({2, 3, 5} : Finset ℕ) ∪ {7, 11} = primesUpTo 11 := by decide
  rw [hset] at h
  norm_num at h
  exact h

theorem primeCount_le_roughCount_eleven_add_two (q : ℕ) (hq : 221 ≤ q) :
    primeCount q ≤ roughCount (primesUpTo 11) q + 2 := by
  classical
  let A := primesUpTo q \ primesUpTo 11
  let B : Finset ℕ := {1, 169, 221}
  have hB : ∀ b ∈ B, ¬Nat.Prime b := by
    intro b hb
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl <;> norm_num
  have hdis : Disjoint B A := by
    apply Finset.disjoint_left.mpr
    intro b hb ha
    exact hB b hb (primesUpTo_prime q b (Finset.mem_sdiff.mp ha).1)
  have hsubset : B ∪ A ⊆ roughNumbers (primesUpTo 11) q := by
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · have hbrough : ∀ b ∈ B, 1 ≤ b ∧ b ≤ 221 ∧
          ∀ p ∈ primesUpTo 11, ¬p ∣ b := by
        rw [primesUpTo_eleven_exact]
        decide
      obtain ⟨hpos, hle, hrough⟩ := hbrough b hb
      exact (mem_roughNumbers _ _ _).mpr ⟨hpos, hle.trans hq, hrough⟩
    · obtain ⟨hbq, hbnot⟩ := Finset.mem_sdiff.mp hb
      obtain ⟨hbprime, hle⟩ := (mem_primesUpTo q b).mp hbq
      have hb11 : 11 < b := by
        by_contra hn
        exact hbnot ((mem_primesUpTo 11 b).mpr ⟨hbprime, by omega⟩)
      exact (mem_roughNumbers _ _ _).mpr
        ⟨hbprime.one_le, hle, prime_above_is_rough hbprime hb11⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_union_of_disjoint hdis] at hcard
  have hBcard : B.card = 3 := by decide
  have hsmall : primeCount 11 = 5 := by decide
  have hsplit : primeCount q ≤ A.card + primeCount 11 :=
    Finset.card_le_card_sdiff_add_card
  change B.card + A.card ≤ roughCount (primesUpTo 11) q at hcard
  omega

theorem primeCount_large_linear_bound (q : ℕ) (hq : 221 ≤ q) :
    (primeCount q : ℝ) < (16 / 77) * q + 6 := by
  have hcard : (primeCount q : ℝ) ≤ roughRealCount (primesUpTo 11) q + 2 := by
    rw [roughRealCount_natCast]
    exact_mod_cast primeCount_le_roughCount_eleven_add_two q hq
  have hupper := (abs_le.mp (roughDiscrepancy_eleven q (Nat.cast_nonneg q))).2
  linarith

end Pilz

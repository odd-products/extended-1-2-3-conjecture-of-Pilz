import Pilz.Basic
import Pilz.PrimeCounts
import Mathlib.Tactic.Linarith

/-!
# Fresh primes and the interval core

This file checks the exact linear fresh-variable structure used at the start of
Section 3. It does not assume or assert the fresh-variable elimination theorem.
-/

noncomputable section

namespace Pilz

open scoped BigOperators

/-- Primes in the paper's interval `(n/2,n]`. -/
def freshPrimes (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun p => Nat.Prime p ∧ n / 2 < p

/-- `C_n`, obtained by removing the isolated fresh prime terms from `F_n`. -/
def core (n : ℕ) : Poly :=
  polynomialOf (Finset.Icc 1 n \ freshPrimes n)

theorem freshPrimes_subset_interval (n : ℕ) :
    freshPrimes n ⊆ Finset.Icc 1 n := Finset.filter_subset _ _

theorem mem_freshPrimes_iff (n p : ℕ) :
    p ∈ freshPrimes n ↔ Nat.Prime p ∧ p ≤ n ∧ n / 2 < p := by
  simp only [freshPrimes, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_, hpn⟩, hp, hhalf⟩
    exact ⟨hp, hpn, hhalf⟩
  · rintro ⟨hp, hpn, hhalf⟩
    exact ⟨⟨hp.one_lt.le, hpn⟩, hp, hhalf⟩

/-- The fresh set agrees exactly with the prime-count convention. -/
theorem card_freshPrimes (n : ℕ) : (freshPrimes n).card = freshCount n := by
  classical
  have heq : freshPrimes n =
      ((Finset.range (n + 1)).filter Nat.Prime) \
        ((Finset.range (n / 2 + 1)).filter Nat.Prime) := by
    ext p
    rw [mem_freshPrimes_iff]
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hp, hpn, hhalf⟩
      exact ⟨⟨by omega, hp⟩, by rintro ⟨hle, _⟩; omega⟩
    · rintro ⟨⟨hpn, hp⟩, hnot⟩
      refine ⟨hp, by omega, ?_⟩
      by_contra hhalf
      exact hnot ⟨by omega, hp⟩
  have hsub : ((Finset.range (n / 2 + 1)).filter Nat.Prime) ⊆
      ((Finset.range (n + 1)).filter Nat.Prime) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  rw [heq, Finset.card_sdiff_of_subset hsub]
  rfl

/-- The constant term is always retained in a nonempty interval core. -/
theorem core_ne_zero {n : ℕ} (hn : 0 < n) : core n ≠ 0 := by
  have hpos : ∀ a ∈ Finset.Icc 1 n \ freshPrimes n, 0 < a := by
    intro a ha
    exact (Finset.mem_Icc.mp (Finset.mem_sdiff.mp ha).1).1
  have hmem : 1 ∈ Finset.Icc 1 n \ freshPrimes n := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨le_rfl, Nat.succ_le_iff.mpr hn⟩, ?_⟩
    intro hfresh
    exact Nat.not_prime_one ((mem_freshPrimes_iff n 1).mp hfresh).1
  exact polynomialOf_ne_zero _ hpos ⟨1, hmem⟩

/-- A fresh prime divides exactly one positive integer at most `n`: itself. -/
theorem eq_freshPrime_of_dvd {n p a : ℕ} (hp : p ∈ freshPrimes n)
    (ha : a ∈ Finset.Icc 1 n) (hdiv : p ∣ a) : a = p := by
  have hhalf := (mem_freshPrimes_iff n p).mp hp |>.2.2
  have halt := Finset.mem_Icc.mp ha
  have htwo : n < 2 * p := by omega
  obtain ⟨k, hk⟩ := hdiv
  have hkpos : 0 < k := by
    by_contra h
    have hkzero : k = 0 := by omega
    simp [hkzero] at hk
    omega
  have hklt : k < 2 := by
    by_contra h
    have hkge : 2 ≤ k := by omega
    have hmul := Nat.mul_le_mul_left p hkge
    nlinarith
  have hkone : k = 1 := by omega
  simpa [hkone] using hk

/-- The fresh contribution is exactly a sum of separate variables. -/
theorem interval_eq_core_add_fresh (n : ℕ) :
    interval n = core n + ∑ p ∈ freshPrimes n, MvPolynomial.X p := by
  classical
  calc
    interval n = core n + ∑ p ∈ freshPrimes n, monomialOf p := by
      exact (Finset.sum_sdiff (f := monomialOf)
        (freshPrimes_subset_interval n)).symm
    _ = core n + ∑ p ∈ freshPrimes n, MvPolynomial.X p := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      exact monomialOf_prime ((mem_freshPrimes_iff n p).mp hp).1

/-- No monomial in the core contains any fresh prime variable. -/
theorem core_fresh_exponent_zero {n p : ℕ} (hp : p ∈ freshPrimes n)
    {d : ℕ →₀ ℕ} (hd : d ∈ (core n).support) : d p = 0 := by
  classical
  have hpos : ∀ a ∈ Finset.Icc 1 n \ freshPrimes n, 0 < a := by
    intro a ha
    exact (Finset.mem_Icc.mp (Finset.mem_sdiff.mp ha).1).1
  rw [core, support_polynomialOf _ hpos] at hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hdiv
  have hae : a = p := eq_freshPrime_of_dvd hp (Finset.mem_sdiff.mp ha).1 hdiv
  exact (Finset.mem_sdiff.mp ha).2 (by simpa [hae] using hp)

end Pilz

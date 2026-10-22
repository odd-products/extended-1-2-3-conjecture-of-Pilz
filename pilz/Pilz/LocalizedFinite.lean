import Pilz.ComponentProfile
import Pilz.Fresh
import Pilz.PrimeLinearBound
import Mathlib.Tactic.Linarith

/-!
# The finite-range prime budget for localized multipliers

The rough counts below are bounded by actual injections of fresh primes and
of the integer one together with primes above the smoothness threshold.
Combined with the exact component budget, these give the paper's prime-budget
lemma using natural-number inequalities without truncated subtraction.
-/

noncomputable section

namespace Pilz

/-- A prime above the smoothness threshold avoids every prime at most it. -/
theorem prime_above_is_rough {q p : ℕ} (hp : Nat.Prime p) (hqp : q < p) :
    ∀ a ∈ primesUpTo q, ¬a ∣ p := by
  intro a ha hdiv
  obtain ⟨haPrime, haq⟩ := (mem_primesUpTo q a).mp ha
  have heq : a = p := (Nat.prime_dvd_prime_iff_eq haPrime hp).mp hdiv
  omega

/-- All fresh primes are index-one rough components when `q ≤ n/2`. -/
theorem freshCount_le_roughIntervalCount (n q : ℕ) (hq : q ≤ n / 2) :
    freshCount n ≤ roughIntervalCount (primesUpTo q) n := by
  classical
  have hsubset : freshPrimes n ⊆
      roughNumbers (primesUpTo q) n \ roughNumbers (primesUpTo q) (n / 2) := by
    intro p hp
    obtain ⟨hpPrime, hpn, hhalf⟩ := (mem_freshPrimes_iff n p).mp hp
    apply Finset.mem_sdiff.mpr
    refine ⟨(mem_roughNumbers (primesUpTo q) n p).mpr
      ⟨hpPrime.one_le, hpn, prime_above_is_rough hpPrime (lt_of_le_of_lt hq hhalf)⟩, ?_⟩
    intro hrough
    have hle := ((mem_roughNumbers (primesUpTo q) (n / 2) p).mp hrough).2.1
    omega
  have hcard := Finset.card_le_card hsubset
  rw [card_freshPrimes, Finset.card_sdiff_of_subset
    (roughNumbers_mono (primesUpTo q) (Nat.div_le_self n 2))] at hcard
  exact hcard

/-- The integer one and primes above q give the prime lower bound on Phi.
The additive form remains valid when `t < q` and at `t = 0`. -/
theorem roughCount_add_primeCount_ge (q t : ℕ) (hq : Nat.Prime q) :
    1 + primeCount t ≤ roughCount (primesUpTo q) t + primeCount q := by
  classical
  by_cases ht : 1 ≤ t
  · let A := primesUpTo t \ primesUpTo q
    have hone : 1 ∉ A := by
      intro h
      have hp := ((mem_primesUpTo t 1).mp (Finset.mem_sdiff.mp h).1).1
      exact Nat.not_prime_one hp
    have hsubset : insert 1 A ⊆ roughNumbers (primesUpTo q) t := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hpA
      · apply (mem_roughNumbers (primesUpTo q) t 1).mpr
        exact ⟨le_rfl, ht, fun a ha => (primesUpTo_prime q a ha).not_dvd_one⟩
      · obtain ⟨hpt, hpq⟩ := Finset.mem_sdiff.mp hpA
        obtain ⟨hpPrime, hpt⟩ := (mem_primesUpTo t p).mp hpt
        have hqp : q < p := by
          by_contra hnot
          exact hpq ((mem_primesUpTo q p).mpr ⟨hpPrime, by omega⟩)
        exact (mem_roughNumbers (primesUpTo q) t p).mpr
          ⟨hpPrime.one_le, hpt, prime_above_is_rough hpPrime hqp⟩
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_insert_of_notMem hone] at hcard
    have hsplit : primeCount t ≤ A.card + primeCount q :=
      Finset.card_le_card_sdiff_add_card
    change A.card + 1 ≤ roughCount (primesUpTo q) t at hcard
    omega
  · have htzero : t = 0 := by omega
    have hπzero : primeCount 0 = 0 := by decide
    have hqmem : q ∈ primesUpTo q := (mem_primesUpTo q q).mpr ⟨hq, le_rfl⟩
    have hπq : 1 ≤ primeCount q := Finset.card_pos.mpr ⟨q, hqmem⟩
    rw [htzero, hπzero]
    omega

/-- The numerical implication in the prime-budget lemma, separated from
the arithmetic sets so all substitutions can be inspected directly. -/
theorem prime_budget_arithmetic
    (w u r p a b c i f₂ f₃ f₅ : ℕ)
    (hu : 10 ≤ u) (hr : 8 ≤ r) (hp : p ≤ u - 3) (hi : r ≤ i)
    (h₂ : 1 + a ≤ f₂ + p) (h₃ : 1 + b ≤ f₃ + p) (h₅ : 1 + c ≤ f₅ + p)
    (hbudget : u * i + 4 * f₂ + 2 * f₃ + 2 * f₅ ≤ w) :
    10 * r + 4 * a + 2 * b + 2 * c ≤ w + 48 := by
  have huri : u * r ≤ u * i := Nat.mul_le_mul_left u hi
  have hsum : u * r + 4 * a + 2 * b + 2 * c + 8 ≤ w + 8 * p := by
    nlinarith
  have hpu : p + 3 ≤ u := by omega
  have hproduct : 10 * r + 8 * u ≤ u * r + 80 := by
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hu
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
    nlinarith [Nat.zero_le (v * s)]
  nlinarith

/-- The exact nonnegative surplus in the paper's prime-budget lemma. -/
theorem prime_budget_arithmetic_surplus
    (w u r p a b c i f₂ f₃ f₅ : ℕ)
    (hu : 10 ≤ u) (hr : 8 ≤ r) (hp : p ≤ u - 3) (hi : r ≤ i)
    (h₂ : 1 + a ≤ f₂ + p) (h₃ : 1 + b ≤ f₃ + p) (h₅ : 1 + c ≤ f₅ + p)
    (hbudget : u * i + 4 * f₂ + 2 * f₃ + 2 * f₅ ≤ w) :
    10 * r + 4 * a + 2 * b + 2 * c + (u - 10) * (r - 8) ≤ w + 48 := by
  have huri : u * r ≤ u * i := Nat.mul_le_mul_left u hi
  have hsum : u * r + 4 * a + 2 * b + 2 * c + 8 ≤ w + 8 * p := by
    nlinarith
  have hpu : p + 3 ≤ u := by omega
  have hproduct : 10 * r + 8 * u + (u - 10) * (r - 8) = u * r + 80 := by
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hu
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
    simp only [Nat.add_sub_cancel_left]
    ring
  nlinarith

/-- The paper's prime-budget conclusion with all negative terms moved to
the right. It holds at every n satisfying the stated count hypotheses. -/
theorem localized_prime_budget (n q : ℕ) (D : Poly)
    (hq : 17 ≤ q) (hqn : q ≤ n / 2) (hcut : q < 2 * (weight D - 1))
    (hr : 8 ≤ freshCount n) (hD : D ≠ 0) (hnorm : Normalized D)
    (hlargest : LargestPrime D q) :
    10 * freshCount n + 4 * primeCount (n / 2) + 2 * primeCount (n / 3) +
      2 * primeCount (n / 5) ≤ weight (interval n * D) + 48 := by
  have hu : 10 ≤ weight D := by omega
  exact prime_budget_arithmetic (weight (interval n * D)) (weight D) (freshCount n)
    (primeCount q) (primeCount (n / 2)) (primeCount (n / 3)) (primeCount (n / 5))
    (roughIntervalCount (primesUpTo q) n)
    (roughCount (primesUpTo q) (n / 2)) (roughCount (primesUpTo q) (n / 3))
    (roughCount (primesUpTo q) (n / 5)) hu hr
    (primeCount_le_terms_sub_three hq hcut) (freshCount_le_roughIntervalCount n q hqn)
    (roughCount_add_primeCount_ge q (n / 2) hlargest.1)
    (roughCount_add_primeCount_ge q (n / 3) hlargest.1)
    (roughCount_add_primeCount_ge q (n / 5) hlargest.1)
    (component_budget_eight q n D hq hD hnorm hlargest)

theorem localized_prime_budget_surplus (n q : ℕ) (D : Poly)
    (hq : 17 ≤ q) (hqn : q ≤ n / 2) (hcut : q < 2 * (weight D - 1))
    (hr : 8 ≤ freshCount n) (hD : D ≠ 0) (hnorm : Normalized D)
    (hlargest : LargestPrime D q) :
    10 * freshCount n + 4 * primeCount (n / 2) + 2 * primeCount (n / 3) +
      2 * primeCount (n / 5) + (weight D - 10) * (freshCount n - 8) ≤
        weight (interval n * D) + 48 := by
  have hu : 10 ≤ weight D := by omega
  exact prime_budget_arithmetic_surplus (weight (interval n * D)) (weight D) (freshCount n)
    (primeCount q) (primeCount (n / 2)) (primeCount (n / 3)) (primeCount (n / 5))
    (roughIntervalCount (primesUpTo q) n)
    (roughCount (primesUpTo q) (n / 2)) (roughCount (primesUpTo q) (n / 3))
    (roughCount (primesUpTo q) (n / 5)) hu hr
    (primeCount_le_terms_sub_three hq hcut) (freshCount_le_roughIntervalCount n q hqn)
    (roughCount_add_primeCount_ge q (n / 2) hlargest.1)
    (roughCount_add_primeCount_ge q (n / 3) hlargest.1)
    (roughCount_add_primeCount_ge q (n / 5) hlargest.1)
    (component_budget_eight q n D hq hD hnorm hlargest)

theorem localized_expansion_of_primeBudget (n q : ℕ) (D : Poly)
    (hq : 17 ≤ q) (hqn : q ≤ n / 2) (hcut : q < 2 * (weight D - 1))
    (hr : 8 ≤ freshCount n) (hbudget : PrimeBudget n)
    (hD : D ≠ 0) (hnorm : Normalized D) (hlargest : LargestPrime D q) :
    n ≤ weight (interval n * D) := by
  have hh := localized_prime_budget n q D hq hqn hcut hr hD hnorm hlargest
  unfold PrimeBudget at hbudget
  omega

end Pilz

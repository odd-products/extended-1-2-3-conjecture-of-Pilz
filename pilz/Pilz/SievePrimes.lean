import Pilz.SieveBaseReal
import Pilz.ComponentProfile

/-! The sieve estimates specialized to all primes up to the largest support
prime. These are the density, discrepancy, and alpha-sieve quantities used
in the counting section of the paper. -/

noncomputable section

namespace Pilz

open scoped BigOperators

def sieveDensity (q : ℕ) : ℝ := ∏ p ∈ primesUpTo q, (1 - 1 / (p : ℝ))

def sieveDelta (q : ℕ) : ℝ := (14 / 15) * 2 ^ (primeCount q - 3)

def sieveExtraPrimes (q : ℕ) : Finset ℕ := primesUpTo q \ {2, 3, 5}

def sieveAlpha (q : ℕ) : ℝ :=
  (4 / 15) * (1 - ∑ p ∈ sieveExtraPrimes q, 1 / (p : ℝ))

def sieveNu (q : ℕ) : ℕ := primeCount q - 2

private theorem base_primes : ∀ p ∈ ({2, 3, 5} : Finset ℕ), Nat.Prime p := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem base_subset_primesUpTo {q : ℕ} (hq : 5 ≤ q) :
    ({2, 3, 5} : Finset ℕ) ⊆ primesUpTo q := by
  intro p hp
  refine (mem_primesUpTo q p).mpr ⟨base_primes p hp, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> omega

theorem base_union_sieveExtraPrimes {q : ℕ} (hq : 5 ≤ q) :
    ({2, 3, 5} : Finset ℕ) ∪ sieveExtraPrimes q = primesUpTo q := by
  exact Finset.union_sdiff_of_subset (base_subset_primesUpTo hq)

theorem base_disjoint_sieveExtraPrimes (q : ℕ) :
    Disjoint ({2, 3, 5} : Finset ℕ) (sieveExtraPrimes q) := by
  apply Finset.disjoint_left.mpr
  intro p hp hpExtra
  exact (Finset.mem_sdiff.mp hpExtra).2 hp

theorem sieveExtraPrimes_prime (q p : ℕ) (hp : p ∈ sieveExtraPrimes q) :
    Nat.Prime p := primesUpTo_prime q p (Finset.mem_sdiff.mp hp).1

theorem card_sieveExtraPrimes {q : ℕ} (hq : 5 ≤ q) :
    (sieveExtraPrimes q).card = primeCount q - 3 := by
  rw [sieveExtraPrimes, Finset.card_sdiff_of_subset (base_subset_primesUpTo hq),
    card_primesUpTo]
  rfl

theorem primeCount_ge_three {q : ℕ} (hq : 5 ≤ q) : 3 ≤ primeCount q := by
  have h := Finset.card_le_card (base_subset_primesUpTo hq)
  simpa using h

theorem sieveNu_eq_one_add_extra_card {q : ℕ} (hq : 5 ≤ q) :
    sieveNu q = 1 + (sieveExtraPrimes q).card := by
  rw [sieveNu, card_sieveExtraPrimes hq]
  have h := primeCount_ge_three hq
  omega

theorem sieveDensity_eq_base_mul_extra {q : ℕ} (hq : 5 ≤ q) :
    sieveDensity q = (4 / 15) * ∏ p ∈ sieveExtraPrimes q, (1 - 1 / (p : ℝ)) := by
  unfold sieveDensity
  rw [← base_union_sieveExtraPrimes hq,
    Finset.prod_union (base_disjoint_sieveExtraPrimes q)]
  norm_num

/-- The manuscript's exponential discrepancy for every cutoff at least five. -/
theorem roughDiscrepancy_primesUpTo {q : ℕ} (hq : 5 ≤ q) :
    RoughDiscrepancy (primesUpTo q) (sieveDensity q) (sieveDelta q) := by
  have h := roughDiscrepancy_union {2, 3, 5} (sieveExtraPrimes q)
    (4 / 15) (14 / 15) base_primes (sieveExtraPrimes_prime q)
    (base_disjoint_sieveExtraPrimes q) roughRealCount_five_discrepancy
  rw [base_union_sieveExtraPrimes hq, ← sieveDensity_eq_base_mul_extra hq,
    card_sieveExtraPrimes hq] at h
  simpa [sieveDelta, mul_comm] using h

theorem roughRealCount_primesUpTo_lower {q : ℕ} (hq : 5 ≤ q) (x : ℝ) (hx : 0 ≤ x) :
    sieveDensity q * x - sieveDelta q ≤ roughRealCount (primesUpTo q) x := by
  have h := (abs_le.mp (roughDiscrepancy_primesUpTo hq x hx)).1
  linarith

theorem roughRealIntervalCount_primesUpTo_lower {q : ℕ} (hq : 5 ≤ q)
    (x : ℝ) (hx : 0 ≤ x) :
    sieveDensity q * x / 2 - 2 * sieveDelta q ≤
      roughRealIntervalCount (primesUpTo q) x :=
  roughRealIntervalCount_lower _ _ _ x (roughDiscrepancy_primesUpTo hq) hx

/-- The ordinary alpha-sieve estimate, with error `(14/15)*(pi(q)-2)`. -/
theorem roughRealCount_primesUpTo_alpha_lower {q : ℕ} (hq : 5 ≤ q)
    (x : ℝ) (hx : 0 ≤ x) :
    sieveAlpha q * x - (14 / 15) * (sieveNu q : ℝ) ≤
      roughRealCount (primesUpTo q) x := by
  have h := roughRealCount_one_step {2, 3, 5} (sieveExtraPrimes q)
    (4 / 15) (14 / 15) x base_primes (sieveExtraPrimes_prime q)
    (base_disjoint_sieveExtraPrimes q) roughRealCount_five_discrepancy hx
  rw [base_union_sieveExtraPrimes hq] at h
  have hnu : (1 : ℝ) + (sieveExtraPrimes q).card = (sieveNu q : ℝ) := by
    rw [sieveNu_eq_one_add_extra_card hq]
    simp
  rw [hnu] at h
  simpa [sieveAlpha, mul_comm] using h

/-- The independent half-interval base discrepancy improves the alpha-sieve
error to `(22/15)*(pi(q)-2)`. -/
theorem roughRealIntervalCount_primesUpTo_alpha_lower {q : ℕ} (hq : 5 ≤ q)
    (x : ℝ) (hx : 0 ≤ x) :
    sieveAlpha q * x / 2 - (22 / 15) * (sieveNu q : ℝ) ≤
      roughRealIntervalCount (primesUpTo q) x := by
  have h := roughRealIntervalCount_one_step_refined {2, 3, 5} (sieveExtraPrimes q)
    (4 / 15) (22 / 15) x base_primes (sieveExtraPrimes_prime q)
    (base_disjoint_sieveExtraPrimes q) roughRealIntervalCount_five_discrepancy hx
  rw [base_union_sieveExtraPrimes hq] at h
  have hnu : (1 : ℝ) + (sieveExtraPrimes q).card = (sieveNu q : ℝ) := by
    rw [sieveNu_eq_one_add_extra_card hq]
    simp
  rw [hnu] at h
  simpa [sieveAlpha, mul_comm] using h

end Pilz

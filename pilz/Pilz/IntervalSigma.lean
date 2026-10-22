import Pilz.ParityClasses
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The square-root bound on interval parity classes

In a fixed full parity class, halving all prime exponents is injective.
The integer encoded by the halved exponents has its square dividing the
original interval element, so it lies in `[1, sqrt n]`.
-/

noncomputable section

namespace Pilz

/-- The positive integer encoded by the halved exponent vector. -/
def rootInteger (d : ℕ →₀ ℕ) : ℕ :=
  (halfExponent d).prod (fun p k => p ^ k)

private theorem interval_support_factorization {n : ℕ} {d : ℕ →₀ ℕ}
    (hd : d ∈ (interval n).support) :
    ∃ a ∈ Finset.Icc 1 n, a.factorization = d := by
  have hpos : ∀ a ∈ Finset.Icc 1 n, 0 < a :=
    fun a ha => (Finset.mem_Icc.mp ha).1
  rw [interval_eq_polynomialOf, support_polynomialOf _ hpos] at hd
  exact Finset.mem_image.mp hd

private theorem primes_of_interval_support {n : ℕ} {d : ℕ →₀ ℕ}
    (hd : d ∈ (interval n).support) : ∀ p ∈ d.support, Nat.Prime p := by
  obtain ⟨a, _ha, rfl⟩ := interval_support_factorization hd
  exact fun p hp => Nat.prime_of_mem_primeFactors hp

theorem rootInteger_factorization {d : ℕ →₀ ℕ}
    (hd : ∀ p ∈ d.support, Nat.Prime p) :
    (rootInteger d).factorization = halfExponent d := by
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  exact hd p (Finsupp.support_mapRange hp)

theorem rootInteger_pos {d : ℕ →₀ ℕ}
    (hd : ∀ p ∈ d.support, Nat.Prime p) : 0 < rootInteger d := by
  unfold rootInteger
  apply Nat.prod_pow_pos_of_zero_notMem_support
  intro hzero
  exact Nat.not_prime_zero (hd 0 (Finsupp.support_mapRange hzero))

theorem rootInteger_sq_dvd {a : ℕ} (ha : 0 < a) :
    (rootInteger a.factorization) ^ 2 ∣ a := by
  have hprime : ∀ p ∈ a.factorization.support, Nat.Prime p :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  apply (Nat.factorization_le_iff_dvd
    (pow_ne_zero _ (ne_of_gt (rootInteger_pos hprime))) (ne_of_gt ha)).mp
  rw [Nat.factorization_pow, rootInteger_factorization hprime]
  apply Finsupp.le_def.mpr
  intro p
  simp only [two_smul, Finsupp.add_apply, halfExponent_apply]
  omega

theorem rootInteger_le_sqrt_of_interval_support {n : ℕ} {d : ℕ →₀ ℕ}
    (hd : d ∈ (interval n).support) : rootInteger d ≤ Nat.sqrt n := by
  obtain ⟨a, ha, rfl⟩ := interval_support_factorization hd
  have hapos : 0 < a := (Finset.mem_Icc.mp ha).1
  apply Nat.le_sqrt'.mpr
  exact (Nat.le_of_dvd hapos (rootInteger_sq_dvd hapos)).trans (Finset.mem_Icc.mp ha).2

theorem rootInteger_injOn_interval_paritySupport (n : ℕ) (ε : ℕ → ℕ) :
    Set.InjOn rootInteger (paritySupport (interval n) ε : Set (ℕ →₀ ℕ)) := by
  intro d hd e he hroot
  apply halfExponent_injOn_paritySupport (interval n) ε hd he
  have hdprime := primes_of_interval_support (paritySupport_subset (interval n) ε hd)
  have heprime := primes_of_interval_support (paritySupport_subset (interval n) ε he)
  rw [← rootInteger_factorization hdprime, ← rootInteger_factorization heprime, hroot]

/-- The class of squares is largest up to the needed square-root upper bound. -/
theorem classWeight_interval_le_sqrt (n : ℕ) (ε : ℕ → ℕ) :
    classWeight (interval n) ε ≤ Nat.sqrt n := by
  classical
  have hmaps : Set.MapsTo rootInteger (paritySupport (interval n) ε)
      (Finset.Icc 1 (Nat.sqrt n)) := by
    intro d hd
    have hdI := paritySupport_subset (interval n) ε hd
    apply Finset.mem_Icc.mpr
    exact ⟨rootInteger_pos (primes_of_interval_support hdI),
      rootInteger_le_sqrt_of_interval_support hdI⟩
  have hcard := Finset.card_le_card_of_injOn rootInteger hmaps
    (rootInteger_injOn_interval_paritySupport n ε)
  simpa [classWeight] using hcard

theorem sigma_interval_le_sqrt (n : ℕ) : sigma (interval n) ≤ Nat.sqrt n := by
  unfold sigma
  exact Finset.sup_le (fun ε _hε => classWeight_interval_le_sqrt n ε)

end Pilz

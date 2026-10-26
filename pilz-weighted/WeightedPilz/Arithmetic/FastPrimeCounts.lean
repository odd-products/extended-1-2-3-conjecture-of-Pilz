import WeightedPilz.Arithmetic.Counts

/-! A computationally explicit prime-count implementation with a proved bridge.
The filter uses the bounded trial-division decision procedure from its definition. -/

namespace WeightedPilz.Arithmetic

def fastPrimeCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter kernelPrime).card

theorem primeCount_eq_fastPrimeCount (n : ℕ) : primeCount n = fastPrimeCount n := by
  unfold primeCount Pilz.primeCount fastPrimeCount
  congr 1
  apply Finset.filter_congr
  intro p hp
  exact (kernelPrime_iff p).symm

macro "fast_prime_decide" : tactic => `(tactic|
  (try dsimp only [freshCount, Pilz.freshCount]
   try simp only [primeCount_eq_fastPrimeCount]
   all_goals decide +kernel))

end WeightedPilz.Arithmetic

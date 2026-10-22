import Pilz.ComponentProfile

/-! A finite trial-divisibility form of smoothness, suitable for exact
kernel computation without evaluating the prime-factorization algorithm. -/

namespace Pilz

def trialSmoothNumbers (T : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun a => ∀ p ∈ primesUpTo n, p ∣ a → p ∈ T)

theorem smoothNumbers_eq_trialSmoothNumbers (T : Finset ℕ) (n : ℕ) :
    smoothNumbers T n = trialSmoothNumbers T n := by
  ext a
  simp only [smoothNumbers, trialSmoothNumbers, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨ha, hsm⟩
    refine ⟨ha, ?_⟩
    intro p hp hdiv
    apply hsm
    rw [Nat.support_factorization, Nat.mem_primeFactors]
    exact ⟨(mem_primesUpTo n p).mp hp |>.1, hdiv, by omega⟩
  · rintro ⟨ha, htrial⟩
    refine ⟨ha, ?_⟩
    intro p hp
    obtain ⟨hprime, hdiv, hne⟩ := (Nat.mem_primeFactors.mp hp)
    apply htrial p ((mem_primesUpTo n p).mpr ⟨hprime, ?_⟩) hdiv
    exact (Nat.le_of_dvd (by omega : 0 < a) hdiv).trans ha.2

end Pilz

import Pilz.FewMultipliers
import Pilz.ThreePrimes

/-! Three-prime support and four-term multipliers. The small interval cases
are explicit premises in the all-length wrappers until they are attached
to the independent small-case proof. -/

noncomputable section

namespace Pilz

/-- At most three specified prime variables suffice for lengths at least
eleven. Fewer than four multiplier terms are handled by the three-term
theorem; absence of the largest prime reduces to the two-prime theorem. -/
theorem three_primes_ge_eleven (n p q ell : ℕ) (D : Poly)
    (hn : 11 ≤ n) (hp : Nat.Prime p) (hq : Nat.Prime q) (hell : Nat.Prime ell)
    (hpq : p < q) (hqell : q < ell) (hD : D ≠ 0) (hnorm : Normalized D)
    (hvars : D.vars ⊆ {p, q, ell}) : n ≤ weight (interval n * D) := by
  by_cases hfew : weight D ≤ 3
  · exact three_multipliers n D hD hfew
  · have hu : 4 ≤ weight D := by omega
    by_cases hocc : VariableOccurs D ell
    · exact three_primes_of_occurring_largest n p q ell D hn hp hq hell hpq hqell
        hD hnorm hu hvars hocc
    · have hvarsPair : D.vars ⊆ {p, q} := by
        intro r hr
        have hrT := hvars hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hrT ⊢
        rcases hrT with hrp | hrq | hrell
        · exact Or.inl hrp
        · exact Or.inr hrq
        · subst r
          exact False.elim (hocc ((variableOccurs_iff_mem_vars D ell).mpr hr))
      exact two_primes n p q D hp hq hpq hD hnorm hvarsPair

/-- The paper's four-multiplier conclusion for lengths at least eleven. -/
theorem four_multipliers_ge_eleven (n : ℕ) (H : Poly) (hn : 11 ≤ n)
    (hH : H ≠ 0) (hfew : weight H ≤ 4) : n ≤ weight (interval n * H) := by
  by_contra hnot
  have hshort : weight (interval n * H) < n := Nat.lt_of_not_ge hnot
  obtain ⟨D, hD, hDshort, hnorm, hminimal, hDvars, hDsmall⟩ :=
    exists_few_minimal_counterexample n 4 H hH hshort hfew
  have hvarsSmall : D.vars ⊆ {2, 3, 5} := by
    intro p hp
    have hpPrime := ((mem_primesUpTo n p).mp (hDvars hp)).1
    have hpos := (variableOccurs_iff_mem_vars D p).mpr hp
    have hcut := deletionMinimal_prime_bound n p D hpPrime (hnorm p) hpos hminimal hDshort
    have hp5 : p ≤ 5 := by omega
    have hcases : ∀ r : Fin 6, Nat.Prime r.val →
        r.val = 2 ∨ r.val = 3 ∨ r.val = 5 := by decide
    have hr := hcases ⟨p, by omega⟩ hpPrime
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hr
  have hbound := three_primes_ge_eleven n 2 3 5 D hn (by decide) (by decide) (by decide)
    (by decide) (by decide) hD hnorm hvarsSmall
  exact (Nat.not_lt_of_ge hbound) hDshort

/-- The all-length three-prime statement with its small-case dependency
displayed explicitly. -/
theorem three_primes_of_small_cases
    (hsmall : ∀ n : ℕ, n ≤ 10 → ConjectureAt n)
    (n p q ell : ℕ) (D : Poly)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hell : Nat.Prime ell)
    (hpq : p < q) (hqell : q < ell) (hD : D ≠ 0) (hnorm : Normalized D)
    (hvars : D.vars ⊆ {p, q, ell}) : n ≤ weight (interval n * D) := by
  by_cases hn : n ≤ 10
  · exact hsmall n hn D hD
  · exact three_primes_ge_eleven n p q ell D (by omega) hp hq hell hpq hqell hD hnorm hvars

/-- The all-length four-multiplier statement with its small-case dependency
displayed explicitly. -/
theorem four_multipliers_of_small_cases
    (hsmall : ∀ n : ℕ, n ≤ 10 → ConjectureAt n)
    (n : ℕ) (H : Poly) (hH : H ≠ 0) (hfew : weight H ≤ 4) :
    n ≤ weight (interval n * H) := by
  by_cases hn : n ≤ 10
  · exact hsmall n hn H hH
  · exact four_multipliers_ge_eleven n H (by omega) hH hfew

end Pilz

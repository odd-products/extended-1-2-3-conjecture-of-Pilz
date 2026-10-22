import Pilz.TwoPrimeCounts
import Pilz.ComponentHelpers

/-! The paper's three-prime rough count and component argument. -/

noncomputable section

namespace Pilz

open scoped BigOperators

private theorem pair_primes (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    ∀ r ∈ ({p, q} : Finset ℕ), Nat.Prime r := by
  intro r hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl <;> assumption

private theorem pair_recurrence (p q n : ℕ) (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hpq : p < q) :
    roughCount {p, q} n + roughCount {p} (n / q) = roughCount {p} n := by
  have h := roughCount_insert_add {p} q n
    (by intro r hr; simpa only [Finset.mem_singleton.mp hr] using hp) hq
    (by simpa using ne_of_gt hpq)
  have hset : insert q ({p} : Finset ℕ) = {p, q} := by
    ext r
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rwa [hset] at h

private theorem triple_recurrence (p q ell n : ℕ) (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hell : Nat.Prime ell) (hpq : p < q) (hqell : q < ell) :
    roughCount {p, q, ell} n + roughCount {p, q} (n / ell) = roughCount {p, q} n := by
  have h := roughCount_insert_add {p, q} ell n (pair_primes p q hp hq) hell
    (by simp [ne_of_gt (hpq.trans hqell), ne_of_gt hqell])
  have hset : insert ell ({p, q} : Finset ℕ) = {p, q, ell} := by
    ext r
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rwa [hset] at h

/-- The count of integers coprime to 30 covers a quarter of n from 11 on.
The finite residues are checked in the first period; each later period
adds two to the surplus `4 Phi(n)-n`. -/
theorem roughCount_five_four (n : ℕ) (hn : 11 ≤ n) :
    n ≤ 4 * roughCount {2, 3, 5} n := by
  have hsmall : ∀ r : Fin 30, r.val ≤ 4 * sieve30Formula r.val + 2 := by decide
  have hgood : ∀ r : Fin 30, 11 ≤ r.val → r.val ≤ 4 * sieve30Formula r.val := by decide
  have hperiod := roughCount_five_add_multiple (n % 30) (n / 30)
  rw [Nat.mod_add_div] at hperiod
  have hres := hsmall ⟨n % 30, Nat.mod_lt n (by decide)⟩
  change n % 30 ≤ 4 * sieve30Formula (n % 30) + 2 at hres
  rw [← roughCount_two_three_five_formula] at hres
  by_cases h30 : n < 30
  · have h := hgood ⟨n, h30⟩ hn
    rwa [← roughCount_two_three_five_formula] at h
  · have hk : 1 ≤ n / 30 := by omega
    have heq := Nat.mod_add_div n 30
    omega

/-- Lemma `three-prime-count` of the paper. -/
private theorem odd_three_lower (n c : ℕ) (hn : 11 ≤ n)
    (hmain : (n + 1) / 2 ≤ c + (n / 5 + 1) / 2 + (n / 7 + 1) / 2) : n ≤ 4 * c := by
  by_cases hn13 : 13 ≤ n
  · have h2 : n ≤ 2 * ((n + 1) / 2) := by omega
    have h5 : 10 * ((n / 5 + 1) / 2) ≤ n + 5 := by omega
    have h7 : 14 * ((n / 7 + 1) / 2) ≤ n + 7 := by omega
    omega
  · have hcases : n = 11 ∨ n = 12 := by omega
    rcases hcases with rfl | rfl <;> norm_num at hmain ⊢ <;> omega

theorem roughCount_three_primes_four (p q ell n : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hell : Nat.Prime ell)
    (hpq : p < q) (hqell : q < ell) (hn : 11 ≤ n) :
    n ≤ 4 * roughCount {p, q, ell} n := by
  have hp2 := hp.two_le
  have hq4 : q ≠ 4 := by
    intro h
    subst q
    exact (by decide : ¬Nat.Prime 4) hq
  have hell4 : ell ≠ 4 := by
    intro h
    subst ell
    exact (by decide : ¬Nat.Prime 4) hell
  have hell6 : ell ≠ 6 := by
    intro h
    subst ell
    exact (by decide : ¬Nat.Prime 6) hell
  have hpair := pair_recurrence p q n hp hq hpq
  have htriple := triple_recurrence p q ell n hp hq hell hpq hqell
  by_cases hpEq : p = 2
  · subst p
    by_cases hqEq : q = 3
    · subst q
      have hell5 : 5 ≤ ell := by omega
      have hdiv : n / ell ≤ n / 5 := Nat.div_le_div_left hell5 (by decide)
      have hmono := roughCount_mono {2, 3} hdiv
      have hbase := roughCount_five_four n hn
      have hrec5 := triple_recurrence 2 3 5 n (by decide) (by decide) (by decide)
        (by decide) (by decide)
      omega
    · have hq5 : 5 ≤ q := by omega
      have hell7 : 7 ≤ ell := by omega
      have hdivq : n / q ≤ n / 5 := Nat.div_le_div_left hq5 (by decide)
      have hdivell : n / ell ≤ n / 7 := Nat.div_le_div_left hell7 (by decide)
      have hmq := roughCount_mono {2} hdivq
      have hmell := roughCount_mono {2} hdivell
      have hpairAt := pair_recurrence 2 q (n / ell) (by decide) hq hpq
      have hpairLe : roughCount {2, q} (n / ell) ≤ roughCount {2} (n / ell) :=
        (Nat.le_add_right _ _).trans_eq hpairAt
      rw [roughCount_two, roughCount_two] at hpair
      rw [roughCount_two] at hpairLe
      rw [roughCount_two, roughCount_two] at hmq hmell
      have hmain : (n + 1) / 2 ≤ roughCount {2, q, ell} n +
          (n / 5 + 1) / 2 + (n / 7 + 1) / 2 := by omega
      exact odd_three_lower n _ hn hmain
  · have hp3 : 3 ≤ p := by omega
    have hq5 : 5 ≤ q := by omega
    have hell7 : 7 ≤ ell := by omega
    have hdivp : n / p ≤ n / 3 := Nat.div_le_div_left hp3 (by decide)
    have hdivq : n / q ≤ n / 5 := Nat.div_le_div_left hq5 (by decide)
    have hdivell : n / ell ≤ n / 7 := Nat.div_le_div_left hell7 (by decide)
    have hleq := roughCount_le {p} (n / q)
    have hleell := roughCount_le {p, q} (n / ell)
    rw [roughCount_singleton p n hp] at hpair
    have hpLe : n / p ≤ n := Nat.div_le_self n p
    omega

/-- Every component of a normalized multiplier with at least four terms
and an occurring largest prime has at least four terms. -/
theorem three_prime_component_profile (p q ell j : ℕ) (D : Poly)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hell : Nat.Prime ell)
    (hpq : p < q) (hqell : q < ell) (hj : 1 ≤ j) (hD : D ≠ 0)
    (hnorm : Normalized D) (hu : 4 ≤ weight D) (hocc : VariableOccurs D ell) :
    4 ≤ weight (smoothInterval {p, q, ell} j * D) := by
  classical
  by_cases hjp : j < p
  · have hbelow : ∀ r ∈ ({p, q, ell} : Finset ℕ), j < r := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl <;> omega
    rw [smoothInterval_eq_one_below _ j hj hbelow, one_mul]
    exact hu
  · have hpj : p ≤ j := Nat.le_of_not_gt hjp
    by_cases hjell : j < ell
    · apply independent_two_slice_expansion_two _ D p ell (ne_of_lt (hpq.trans hqell))
        (smoothInterval_independent_above _ j ell hjell)
        (smoothInterval_coeff_zero _ j hj)
        (smoothInterval_coeff_prime _ j p hp (by simp) hpj)
        (hnorm ell) hocc
    · have hactive : ∀ r ∈ ({p, q, ell} : Finset ℕ), r ≤ j := by
        intro r hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl <;> omega
      have hcard : ({p, q, ell} : Finset ℕ).card = 3 := by
        simp [ne_of_lt hpq, ne_of_lt hqell, ne_of_lt (hpq.trans hqell)]
      have hprimes : ∀ r ∈ ({p, q, ell} : Finset ℕ), Nat.Prime r := by
        intro r hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl <;> assumption
      have h := smooth_component_endpoints {p, q, ell} {p, q, ell} j D hj hD
        Finset.Subset.rfl hprimes hactive
      simpa only [hcard] using h

/-- The actual three-prime component argument for interval lengths at least
eleven, before the already-small cases and fewer-prime cases are attached. -/
theorem three_primes_of_occurring_largest (n p q ell : ℕ) (D : Poly)
    (hn : 11 ≤ n) (hp : Nat.Prime p) (hq : Nat.Prime q) (hell : Nat.Prime ell)
    (hpq : p < q) (hqell : q < ell) (hD : D ≠ 0) (hnorm : Normalized D)
    (hu : 4 ≤ weight D) (hvars : D.vars ⊆ {p, q, ell})
    (hocc : VariableOccurs D ell) : n ≤ weight (interval n * D) := by
  have hprimes : ∀ r ∈ ({p, q, ell} : Finset ℕ), Nat.Prime r := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  have hbudget := uniform_component_budget_set {p, q, ell} n 4 D hprimes hvars
    (fun j hj => three_prime_component_profile p q ell j D hp hq hell hpq hqell hj hD hnorm hu hocc)
  exact (roughCount_three_primes_four p q ell n hp hq hell hpq hqell hn).trans hbudget

end Pilz

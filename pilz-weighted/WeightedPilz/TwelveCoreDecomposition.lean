import WeightedPilz.CoreTwelve

/-! Concrete prime-variable decompositions of the cores twelve through fifteen. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

def arithmeticBinomial (p : ℕ) (c : ℕ → K) : Poly K :=
  C (c p) + C (c (2 * p)) * X 2

theorem polynomialOf_prime_double (p : ℕ) (hp : Nat.Prime p) (c : ℕ → K) :
    polynomialOf {p, 2 * p} c = arithmeticBinomial p c * X p := by
  have hp0 := hp.pos
  have hneq : p ≠ 2 * p := by omega
  have h2 : (2 : ℕ).factorization = Finsupp.single 2 1 := Nat.prime_two.factorization
  have hdouble : (2 * p).factorization = Finsupp.single 2 1 + Finsupp.single p 1 := by
    rw [Nat.factorization_mul (by decide) (ne_of_gt hp0), h2, hp.factorization]
  simp [polynomialOf, arithmeticBinomial, hneq, hp.factorization, hdouble,
    ← C_apply, ← C_mul_X_pow_eq_monomial, monomial_add_single] <;> ring

def arithmeticFiveRow (c : ℕ → K) : Poly K :=
  C (c 5) + C (c 10) * X 2 + C (c 15) * X 3

theorem polynomialOf_five_row (c : ℕ → K) :
    polynomialOf {5, 10, 15} c = arithmeticFiveRow c * X 5 := by
  have h2 : (2 : ℕ).factorization = Finsupp.single 2 1 := Nat.prime_two.factorization
  have h3 : (3 : ℕ).factorization = Finsupp.single 3 1 :=
    (by decide : Nat.Prime 3).factorization
  have h5 : (5 : ℕ).factorization = Finsupp.single 5 1 :=
    (by decide : Nat.Prime 5).factorization
  have h10 : (10 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 5 1 := by
    change (2 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h5]
  have h15 : (15 : ℕ).factorization = Finsupp.single 3 1 + Finsupp.single 5 1 := by
    change (3 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h3, h5]
  simp [polynomialOf, arithmeticFiveRow, h5, h10, h15,
    ← C_apply, ← C_mul_X_pow_eq_monomial, monomial_add_single] <;> ring

theorem intervalCore_twelve_decomposition (n : ℕ) (hn : 12 ≤ n) (hn13 : n ≤ 13)
    (c : ℕ → K) :
    intervalCore n c = baseTwelve c + arithmeticBinomial 5 c * X 5 := by
  have hset : Finset.Icc 1 n \ intervalFreshPrimes n =
      ({1, 2, 3, 4, 6, 8, 9, 12} : Finset ℕ) ∪ {5, 10} := by
    interval_cases n <;> decide
  have hdis : Disjoint ({1, 2, 3, 4, 6, 8, 9, 12} : Finset ℕ) {5, 10} := by decide
  rw [intervalCore, polynomialOf, hset, Finset.sum_union hdis]
  change polynomialOf {1, 2, 3, 4, 6, 8, 9, 12} c + polynomialOf {5, 10} c = _
  rw [← baseTwelve_eq_polynomialOf,
    show polynomialOf {5, 10} c = arithmeticBinomial 5 c * X 5 from
      polynomialOf_prime_double 5 (by decide) c]

theorem intervalCore_fourteen_decomposition (c : ℕ → K) :
    intervalCore 14 c =
      (baseTwelve c + arithmeticBinomial 5 c * X 5) + arithmeticBinomial 7 c * X 7 := by
  have hset : Finset.Icc 1 14 \ intervalFreshPrimes 14 =
      (({1, 2, 3, 4, 6, 8, 9, 12} : Finset ℕ) ∪ {5, 10}) ∪ {7, 14} := by decide
  have hdis1 : Disjoint ({1, 2, 3, 4, 6, 8, 9, 12} : Finset ℕ) {5, 10} := by decide
  have hdis2 : Disjoint (({1, 2, 3, 4, 6, 8, 9, 12} : Finset ℕ) ∪ {5, 10}) {7, 14} := by decide
  rw [intervalCore, polynomialOf, hset, Finset.sum_union hdis2, Finset.sum_union hdis1]
  change (polynomialOf {1, 2, 3, 4, 6, 8, 9, 12} c + polynomialOf {5, 10} c) +
    polynomialOf {7, 14} c = _
  rw [← baseTwelve_eq_polynomialOf,
    show polynomialOf {5, 10} c = arithmeticBinomial 5 c * X 5 from
      polynomialOf_prime_double 5 (by decide) c,
    show polynomialOf {7, 14} c = arithmeticBinomial 7 c * X 7 from
      polynomialOf_prime_double 7 (by decide) c]

theorem intervalCore_fifteen_decomposition (c : ℕ → K) :
    intervalCore 15 c =
      (baseTwelve c + arithmeticFiveRow c * X 5) + arithmeticBinomial 7 c * X 7 := by
  have hset : Finset.Icc 1 15 \ intervalFreshPrimes 15 =
      (({1, 2, 3, 4, 6, 8, 9, 12} : Finset ℕ) ∪ {5, 10, 15}) ∪ {7, 14} := by decide
  have hdis1 : Disjoint ({1, 2, 3, 4, 6, 8, 9, 12} : Finset ℕ) {5, 10, 15} := by decide
  have hdis2 : Disjoint (({1, 2, 3, 4, 6, 8, 9, 12} : Finset ℕ) ∪ {5, 10, 15}) {7, 14} := by decide
  rw [intervalCore, polynomialOf, hset, Finset.sum_union hdis2, Finset.sum_union hdis1]
  change (polynomialOf {1, 2, 3, 4, 6, 8, 9, 12} c + polynomialOf {5, 10, 15} c) +
    polynomialOf {7, 14} c = _
  rw [← baseTwelve_eq_polynomialOf, polynomialOf_five_row,
    show polynomialOf {7, 14} c = arithmeticBinomial 7 c * X 7 from
      polynomialOf_prime_double 7 (by decide) c]

end WeightedPilz

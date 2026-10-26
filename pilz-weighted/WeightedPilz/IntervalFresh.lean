import WeightedPilz.Basic
import WeightedPilz.FreshRows
import WeightedPilz.Rescale
import Pilz.Fresh

/-!
# Weighted intervals and their fresh prime variables

Only the arithmetic definitions and prime-divisor facts from `Pilz.Fresh` are
reused. The core, its coefficients, and all polynomial arguments below are
weighted and valid over every field.
-/

noncomputable section

namespace WeightedPilz

open scoped BigOperators
open MvPolynomial

variable {K : Type*} [Field K]

/-- The primes in `(n/2,n]`, with the manuscript's integer endpoint convention. -/
abbrev intervalFreshPrimes (n : ℕ) : Finset ℕ := Pilz.freshPrimes n

/-- The weighted core obtained by deleting the isolated fresh prime terms. -/
def intervalCore (n : ℕ) (c : ℕ → K) : Poly K :=
  polynomialOf (Finset.Icc 1 n \ intervalFreshPrimes n) c

theorem intervalCore_support (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c) :
    (intervalCore n c).support =
      (Finset.Icc 1 n \ intervalFreshPrimes n).image Nat.factorization := by
  apply support_polynomialOf
  · intro a ha
    exact (Finset.mem_Icc.mp (Finset.mem_sdiff.mp ha).1).1
  · intro a ha
    exact hc a (Finset.mem_sdiff.mp ha).1

theorem weight_intervalCore (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c) :
    weight (intervalCore n c) = n - (intervalFreshPrimes n).card := by
  rw [intervalCore, weight_polynomialOf]
  · rw [Finset.card_sdiff_of_subset (Pilz.freshPrimes_subset_interval n)]
    simp
  · intro a ha
    exact (Finset.mem_Icc.mp (Finset.mem_sdiff.mp ha).1).1
  · intro a ha
    exact hc a (Finset.mem_sdiff.mp ha).1

theorem weight_intervalCore_add_freshCount (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) :
    weight (intervalCore n c) + Pilz.freshCount n = n := by
  have hcard : (intervalFreshPrimes n).card ≤ n := by
    simpa using Finset.card_le_card (Pilz.freshPrimes_subset_interval n)
  rw [weight_intervalCore n c hc, ← Pilz.card_freshPrimes n]
  exact Nat.sub_add_cancel hcard

theorem intervalCore_ne_zero {n : ℕ} (hn : 0 < n) (c : ℕ → K)
    (hc : NonzeroWeights n c) : intervalCore n c ≠ 0 := by
  apply polynomialOf_ne_zero
  · intro a ha
    exact (Finset.mem_Icc.mp (Finset.mem_sdiff.mp ha).1).1
  · intro a ha
    exact hc a (Finset.mem_sdiff.mp ha).1
  · refine ⟨1, Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hn⟩, ?_⟩⟩
    intro hp
    exact Nat.not_prime_one ((Pilz.mem_freshPrimes_iff n 1).mp hp).1

theorem intervalCore_fresh_exponent_zero {n p : ℕ} (c : ℕ → K)
    (hc : NonzeroWeights n c) (hp : p ∈ intervalFreshPrimes n)
    {d : ℕ →₀ ℕ} (hd : d ∈ (intervalCore n c).support) : d p = 0 := by
  rw [intervalCore_support n c hc] at hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hdiv
  have heq := Pilz.eq_freshPrime_of_dvd hp (Finset.mem_sdiff.mp ha).1 hdiv
  exact (Finset.mem_sdiff.mp ha).2 (heq.symm ▸ hp)

/-- Before scaling, the isolated fresh terms retain their specified coefficients. -/
theorem interval_eq_core_add_weighted_fresh (n : ℕ) (c : ℕ → K) :
    interval n c = intervalCore n c +
      ∑ p ∈ intervalFreshPrimes n, C (c p) * X p := by
  classical
  calc
    interval n c = intervalCore n c +
        ∑ p ∈ intervalFreshPrimes n, monomial p.factorization (c p) := by
      change (∑ p ∈ Finset.Icc 1 n, monomial p.factorization (c p)) =
        (∑ p ∈ Finset.Icc 1 n \ intervalFreshPrimes n, monomial p.factorization (c p)) + _
      exact (Finset.sum_sdiff (f := fun p => monomial p.factorization (c p))
        (Pilz.freshPrimes_subset_interval n)).symm
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      rw [((Pilz.mem_freshPrimes_iff n p).mp hp).1.factorization]
      simp [X, C_mul_monomial]

/-- Scale each fresh variable by the inverse of its nonzero interval weight. -/
def intervalFreshNormalization (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c)
    (p : ℕ) : Kˣ := by
  classical
  exact if hp : p ∈ intervalFreshPrimes n then
    (Units.mk0 (c p) (hc p (Pilz.freshPrimes_subset_interval n hp)))⁻¹ else 1

theorem rescale_intervalFreshNormalization_of_baseOnly (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (P : Poly K)
    (hP : ∀ p ∈ intervalFreshPrimes n, ∀ d ∈ P.support, d p = 0) :
    rescale (intervalFreshNormalization n c hc) P = P := by
  classical
  ext d
  rw [coeff_rescale]
  by_cases hd : d ∈ P.support
  · have hprod : d.prod (fun p e => (intervalFreshNormalization n c hc p : K) ^ e) = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      have hpf : p ∉ intervalFreshPrimes n := by
        intro hf
        exact Finsupp.mem_support_iff.mp hp (hP p hf d hd)
      simp [intervalFreshNormalization, hpf]
    rw [hprod, mul_one]
  · rw [notMem_support_iff.mp hd, zero_mul]

theorem rescale_intervalCore (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c) :
    rescale (intervalFreshNormalization n c hc) (intervalCore n c) = intervalCore n c := by
  apply rescale_intervalFreshNormalization_of_baseOnly
  intro p hp d hd
  exact intervalCore_fresh_exponent_zero c hc hp hd

theorem rescale_weighted_fresh_term (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c)
    {p : ℕ} (hp : p ∈ intervalFreshPrimes n) :
    rescale (intervalFreshNormalization n c hc) (C (c p) * X p) = X p := by
  have hcp := hc p (Pilz.freshPrimes_subset_interval n hp)
  rw [map_mul, rescale_C, rescale_X, ← mul_assoc, ← map_mul]
  simp [intervalFreshNormalization, hp, hcp]

/-- The normalized weighted interval is exactly the core plus unweighted fresh variables. -/
theorem rescale_interval_eq_core_add_fresh (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) :
    rescale (intervalFreshNormalization n c hc) (interval n c) =
      intervalCore n c + ∑ p ∈ intervalFreshPrimes n, X p := by
  rw [interval_eq_core_add_weighted_fresh, map_add, rescale_intervalCore, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  exact rescale_weighted_fresh_term n c hc hp

/-- The interval core and its fresh variables satisfy the generic independence interface. -/
def intervalFreshData (n : ℕ) (c : ℕ → K) (hn : 0 < n)
    (hc : NonzeroWeights n c) (hr : (intervalFreshPrimes n).Nonempty) : FreshData ℕ K where
  vars := intervalFreshPrimes n
  nonempty := hr
  C := intervalCore n c
  C_ne_zero := intervalCore_ne_zero hn c hc
  independent := fun p hp d hd => intervalCore_fresh_exponent_zero c hc hp hd

theorem weight_intervalFreshData_F (n : ℕ) (c : ℕ → K) (hn : 0 < n)
    (hc : NonzeroWeights n c) (hr : (intervalFreshPrimes n).Nonempty) :
    weight (intervalFreshData n c hn hc hr).F = n := by
  change weight (intervalCore n c + ∑ p ∈ intervalFreshPrimes n, X p) = n
  rw [← rescale_interval_eq_core_add_fresh n c hc, weight_rescale, weight_interval n c hc]

theorem distance_interval_eq_freshData (n : ℕ) (c : ℕ → K) (hn : 0 < n)
    (hc : NonzeroWeights n c) (hr : (intervalFreshPrimes n).Nonempty) :
    distance (interval n c) = distance (intervalFreshData n c hn hc hr).F := by
  rw [← distance_rescale (intervalFreshNormalization n c hc) (interval n c),
    rescale_interval_eq_core_add_fresh]
  rfl

/-- The exact base-only identity, with all original interval weights retained. -/
theorem weight_interval_mul_base (n : ℕ) (c : ℕ → K) (hn : 0 < n)
    (hc : NonzeroWeights n c) (hr : (intervalFreshPrimes n).Nonempty)
    (D : Poly K) (hD : ∀ p ∈ intervalFreshPrimes n, ∀ d ∈ D.support, d p = 0) :
    weight (interval n c * D) =
      weight (intervalCore n c * D) + (intervalFreshPrimes n).card * weight D := by
  rw [← weight_rescale (intervalFreshNormalization n c hc) (interval n c * D),
    map_mul, rescale_interval_eq_core_add_fresh,
    rescale_intervalFreshNormalization_of_baseOnly n c hc D hD]
  exact (intervalFreshData n c hn hc hr).weight_mul_base D hD

theorem weight_interval_mul_base_freshCount (n : ℕ) (c : ℕ → K) (hn : 0 < n)
    (hc : NonzeroWeights n c) (hr : (intervalFreshPrimes n).Nonempty)
    (D : Poly K) (hD : ∀ p ∈ intervalFreshPrimes n, ∀ d ∈ D.support, d p = 0) :
    weight (interval n c * D) =
      weight (intervalCore n c * D) + Pilz.freshCount n * weight D := by
  rw [weight_interval_mul_base n c hn hc hr D hD, Pilz.card_freshPrimes]

end WeightedPilz

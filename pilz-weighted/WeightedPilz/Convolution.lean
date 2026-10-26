import WeightedPilz.Basic
import WeightedPilz.VariableSlices
import Mathlib.Data.PNat.Basic

/-!
# Multiplicative convolution of positive integer inputs

The native monoid algebra of positive integers has the desired convolution
multiplication. Its map into the polynomial ring preserves both multiplication
and the exact support cardinality.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace WeightedPilz

open scoped BigOperators

variable {K : Type*} [CommSemiring K]

/-- Finitely supported functions on positive integers, with multiplicative convolution. -/
abbrev ArithmeticFunction (K : Type*) [Semiring K] := MonoidAlgebra K ℕ+

/-- The valuation vector is injective on positive integers. -/
theorem positive_factorization_injective :
    Function.Injective (fun a : ℕ+ => (a : ℕ).factorization) := by
  intro a b hab
  apply Subtype.ext
  exact Nat.factorization_inj (ne_of_gt a.pos) (ne_of_gt b.pos) hab

/-- Unique factorization gives a multiplicative map of positive integers to monomials. -/
def arithmeticMonomialHom : ℕ+ →* Poly K where
  toFun a := monomialOf (a : ℕ)
  map_one' := monomialOf_one
  map_mul' a b := monomialOf_mul (ne_of_gt a.pos) (ne_of_gt b.pos)

/-- Encode a finitely supported arithmetic function by its valuation monomials. -/
def arithmeticPolynomial : ArithmeticFunction K →ₐ[K] Poly K :=
  MonoidAlgebra.lift K ℕ+ (Poly K) arithmeticMonomialHom

theorem arithmeticPolynomial_eq_mapDomain (f : ArithmeticFunction K) :
    arithmeticPolynomial f =
      Finsupp.mapDomain (fun a : ℕ+ => (a : ℕ).factorization) f := by
  rw [arithmeticPolynomial, MonoidAlgebra.lift_apply, Finsupp.mapDomain]
  apply Finsupp.sum_congr
  intro a ha
  simp [arithmeticMonomialHom, monomialOf, MvPolynomial.smul_monomial]
  rfl

@[simp] theorem arithmeticPolynomial_single (a : ℕ+) (v : K) :
    arithmeticPolynomial (MonoidAlgebra.single a v) =
      MvPolynomial.monomial (a : ℕ).factorization v := by
  rw [arithmeticPolynomial_eq_mapDomain, Finsupp.mapDomain_single]
  rfl

theorem arithmeticPolynomial_support (f : ArithmeticFunction K) :
    (arithmeticPolynomial f).support =
      f.support.image (fun a : ℕ+ => (a : ℕ).factorization) := by
  classical
  rw [arithmeticPolynomial_eq_mapDomain]
  exact Finsupp.mapDomain_support_of_injective positive_factorization_injective f

@[simp] theorem weight_arithmeticPolynomial (f : ArithmeticFunction K) :
    weight (arithmeticPolynomial f) = f.support.card := by
  classical
  rw [weight, arithmeticPolynomial_support]
  exact Finset.card_image_of_injective _ positive_factorization_injective

theorem arithmeticPolynomial_injective :
    Function.Injective (arithmeticPolynomial (K := K)) := by
  intro f g h
  simp only [arithmeticPolynomial_eq_mapDomain] at h
  exact Finsupp.mapDomain_injective positive_factorization_injective h

@[simp] theorem arithmeticPolynomial_ne_zero {f : ArithmeticFunction K} :
    arithmeticPolynomial f ≠ 0 ↔ f ≠ 0 := by
  exact not_congr (map_eq_zero_iff _ arithmeticPolynomial_injective)

@[simp] theorem arithmeticPolynomial_mul (f g : ArithmeticFunction K) :
    arithmeticPolynomial (f * g) = arithmeticPolynomial f * arithmeticPolynomial g :=
  map_mul _ _ _

/-- Each polynomial coefficient recovers the corresponding arithmetic value. -/
@[simp] theorem coeff_arithmeticPolynomial (f : ArithmeticFunction K) (a : ℕ+) :
    MvPolynomial.coeff (a : ℕ).factorization (arithmeticPolynomial f) = f a := by
  rw [arithmeticPolynomial_eq_mapDomain]
  exact Finsupp.mapDomain_apply positive_factorization_injective f a

/-- The convolution is the ordinary finite sum over multiplicative pairs. -/
theorem arithmetic_mul_apply (f g : ArithmeticFunction K) (m : ℕ+) :
    (f * g) m = ∑ a ∈ f.support, ∑ b ∈ g.support,
      if a * b = m then f a * g b else 0 :=
  MonoidAlgebra.mul_apply f g m

/-- The weighted interval, represented as a finitely supported arithmetic function. -/
def arithmeticKernel (n : ℕ) (c : ℕ → K) : ArithmeticFunction K :=
  ∑ a ∈ Finset.range n, MonoidAlgebra.single (⟨a + 1, Nat.succ_pos a⟩ : ℕ+) (c (a + 1))

@[simp] theorem arithmeticPolynomial_kernel (n : ℕ) (c : ℕ → K) :
    arithmeticPolynomial (arithmeticKernel n c) = interval n c := by
  induction n with
  | zero => simp [arithmeticKernel]
  | succ n ih =>
    simp only [arithmeticKernel, Finset.sum_range_succ, map_add,
      arithmeticPolynomial_single] at *
    rw [ih, interval_succ]
    rfl

@[simp] theorem arithmeticKernel_apply (n : ℕ) (c : ℕ → K) (a : ℕ+) :
    arithmeticKernel n c a = if (a : ℕ) ≤ n then c a else 0 := by
  rw [← coeff_arithmeticPolynomial (arithmeticKernel n c) a,
    arithmeticPolynomial_kernel, coeff_interval n c a.pos]

/-- The exact positive quotient agrees with natural number division on divisors. -/
theorem divExact_val {a m : ℕ+} (h : a ∣ m) :
    (PNat.divExact m a : ℕ) = (m : ℕ) / (a : ℕ) := by
  exact Nat.eq_div_of_mul_eq_right (ne_of_gt a.pos)
    (congrArg (fun x : ℕ+ => (x : ℕ)) (PNat.mul_div_exact h))

/-- Multiplication by a singleton is the expected division and weight operation. -/
theorem arithmetic_single_mul_apply (a m : ℕ+) (v : K) (f : ArithmeticFunction K) :
    ((MonoidAlgebra.single a v : ArithmeticFunction K) * f) m =
      if a ∣ m then v * f (PNat.divExact m a) else 0 := by
  classical
  by_cases hd : a ∣ m
  · rw [if_pos hd]
    apply MonoidAlgebra.single_mul_apply_aux
    intro b hb
    constructor
    · intro h
      exact mul_left_cancel (h.trans (PNat.mul_div_exact hd).symm)
    · rintro rfl
      exact PNat.mul_div_exact hd
  · rw [if_neg hd]
    apply MonoidAlgebra.single_mul_apply_of_not_exists_mul
    simpa only [dvd_def] using hd

/-- Equation `eq:convolution`, with the finite interval indexed by `a + 1`.
`PNat.divExact m a` is the positive integer quotient whenever `a ∣ m`. -/
theorem interval_convolution_apply (n : ℕ) (c : ℕ → K)
    (f : ArithmeticFunction K) (m : ℕ+) :
    (arithmeticKernel n c * f) m =
      ∑ a ∈ Finset.range n,
        if (⟨a + 1, Nat.succ_pos a⟩ : ℕ+) ∣ m then
          c (a + 1) * f (PNat.divExact m ⟨a + 1, Nat.succ_pos a⟩) else 0 := by
  classical
  rw [arithmeticKernel, Finset.sum_mul]
  let g : ℕ → ArithmeticFunction K := fun a =>
    MonoidAlgebra.single (M := ℕ+) ⟨a + 1, Nat.succ_pos a⟩ (c (a + 1)) * f
  calc
    (∑ a ∈ Finset.range n, g a) m = ∑ a ∈ Finset.range n, g a m :=
      Finsupp.finset_sum_apply (Finset.range n) g m
    _ = _ := Finset.sum_congr rfl (fun a _ => arithmetic_single_mul_apply _ m _ f)

/-- Polynomial multiplication and weighted interval convolution coincide. -/
theorem arithmeticPolynomial_interval_convolution (n : ℕ) (c : ℕ → K)
    (f : ArithmeticFunction K) :
    arithmeticPolynomial (arithmeticKernel n c * f) = interval n c * arithmeticPolynomial f := by
  rw [map_mul, arithmeticPolynomial_kernel]

/-- The support cardinalities in the polynomial and convolution versions are equal. -/
theorem weight_interval_convolution (n : ℕ) (c : ℕ → K)
    (f : ArithmeticFunction K) :
    weight (interval n c * arithmeticPolynomial f) = (arithmeticKernel n c * f).support.card := by
  rw [← arithmeticPolynomial_interval_convolution, weight_arithmeticPolynomial]

/-- A polynomial using only prime variables is the encoding of an arithmetic function. -/
theorem exists_arithmeticPolynomial_of_prime_vars (P : Poly K)
    (hP : (P.vars : Set ℕ) ⊆ {p | p.Prime}) :
    ∃ f : ArithmeticFunction K, arithmeticPolynomial f = P := by
  classical
  let e : ℕ+ ↪ (ℕ →₀ ℕ) := ⟨fun a => (a : ℕ).factorization,
    positive_factorization_injective⟩
  have hrange : (P.support : Set (ℕ →₀ ℕ)) ⊆ Set.range e := by
    intro d hd
    have hprime : ∀ p ∈ d.support, p.Prime := by
      intro p hp
      exact hP ((MvPolynomial.mem_vars p).mpr ⟨d, hd, hp⟩)
    refine ⟨Nat.factorizationEquiv.symm ⟨d, hprime⟩, ?_⟩
    exact congrArg Subtype.val (Nat.factorizationEquiv.apply_symm_apply ⟨d, hprime⟩)
  let f : ArithmeticFunction K := Finsupp.comapDomain e P e.injective.injOn
  refine ⟨f, ?_⟩
  rw [arithmeticPolynomial_eq_mapDomain]
  exact (Finsupp.embDomain_eq_mapDomain e f).symm.trans
    (Finsupp.embDomain_comapDomain hrange)

/-- The interval polynomial contains only prime variables, even with zero weights. -/
theorem vars_interval_subset_primes (n : ℕ) (c : ℕ → K) :
    ((interval n c).vars : Set ℕ) ⊆ {p | p.Prime} := by
  classical
  intro p hp
  obtain ⟨d, hd, hdp⟩ := (MvPolynomial.mem_vars p).mp hp
  have hs := arithmeticPolynomial_support (arithmeticKernel n c)
  rw [arithmeticPolynomial_kernel] at hs
  rw [hs] at hd
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hd
  rw [← ha] at hdp
  exact (Nat.factorizationEquiv a).property p hdp

end WeightedPilz

namespace WeightedPilz

variable {K : Type*} [Field K]

/-- The field bound implies the equivalent arithmetic convolution bound. -/
theorem convolution_bound_of_intervalBound {n : ℕ} {c : ℕ → K}
    (h : IntervalBound n c) (f : ArithmeticFunction K) (hf : f ≠ 0) :
    n ≤ (arithmeticKernel n c * f).support.card := by
  rw [← weight_interval_convolution]
  exact h _ (arithmeticPolynomial_ne_zero.mpr hf)

/-- Every nonzero singleton arithmetic input attains equality. -/
theorem convolution_singleton_sharpness (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (a : ℕ+) {v : K} (hv : v ≠ 0) :
    (arithmeticKernel n c * (MonoidAlgebra.single a v : ArithmeticFunction K)).support.card = n := by
  rw [← weight_arithmeticPolynomial, map_mul, arithmeticPolynomial_kernel,
    arithmeticPolynomial_single]
  exact weight_interval_mul_scalar_monomial n c hc _ hv

/-- The arithmetic convolution bound implies the polynomial bound even for
multipliers involving additional, nonprime variable names. -/
theorem intervalBound_of_convolution_bound {n : ℕ} {c : ℕ → K}
    (h : ∀ f : ArithmeticFunction K, f ≠ 0 →
      n ≤ (arithmeticKernel n c * f).support.card) : IntervalBound n c := by
  classical
  intro H hH
  obtain ⟨D, hD, hDvars, hweight⟩ := exists_base_multiplier {p : ℕ | p.Prime}
    (interval n c) H (vars_interval_subset_primes n c) hH
  obtain ⟨f, hf⟩ := exists_arithmeticPolynomial_of_prime_vars D hDvars
  have hfn : f ≠ 0 := by
    intro hz
    apply hD
    rw [← hf, hz, map_zero]
  have hbound := h f hfn
  rw [← weight_interval_convolution, hf] at hbound
  exact hbound.trans hweight

/-- The field theorem and the finitely supported multiplicative-convolution
statement are equivalent, with exactly the same interval and weights. -/
theorem intervalBound_iff_convolution_bound (n : ℕ) (c : ℕ → K) :
    IntervalBound n c ↔ ∀ f : ArithmeticFunction K, f ≠ 0 →
      n ≤ (arithmeticKernel n c * f).support.card :=
  ⟨fun h f hf => convolution_bound_of_intervalBound h f hf,
    intervalBound_of_convolution_bound⟩

end WeightedPilz


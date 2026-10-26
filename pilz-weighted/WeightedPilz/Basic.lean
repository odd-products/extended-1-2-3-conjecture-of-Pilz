import WeightedPilz.Defs
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Weighted arithmetic encoding

The valuation encoding and the exact support statements in Section 1 of the
frozen manuscript. The coefficient statements allow a commutative semiring;
nonvanishing of the weights is stated on the finite input set.
-/

namespace WeightedPilz

open scoped BigOperators

variable {K : Type*} [CommSemiring K]

@[simp] theorem weight_zero {σ : Type*} : weight (0 : MvPolynomial σ K) = 0 := by
  simp [weight]

theorem weight_pos {σ : Type*} {P : MvPolynomial σ K} (hP : P ≠ 0) :
    0 < weight P := by
  simpa [weight, Finset.card_pos, MvPolynomial.support_nonempty] using hP

@[simp] theorem monomialOf_one : monomialOf (K := K) 1 = 1 := by
  simp only [monomialOf, Nat.factorization_one]
  rfl

theorem monomialOf_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    monomialOf (K := K) (a * b) = monomialOf a * monomialOf b := by
  simp [monomialOf, Nat.factorization_mul ha hb, MvPolynomial.monomial_mul]

theorem monomialOf_prime {p : ℕ} (hp : p.Prime) :
    monomialOf (K := K) p = MvPolynomial.X p := by
  rw [monomialOf, hp.factorization]
  rfl

theorem monomialOf_injective [Nontrivial K] {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    monomialOf (K := K) a = monomialOf b ↔ a = b := by
  constructor
  · intro h
    apply Nat.factorization_inj ha hb
    exact MvPolynomial.monomial_left_injective (one_ne_zero : (1 : K) ≠ 0) h
  · rintro rfl
    rfl

@[simp] theorem support_monomialOf [Nontrivial K] (a : ℕ) :
    (monomialOf (K := K) a).support = {a.factorization} := by
  classical
  simp [monomialOf, MvPolynomial.support_monomial]

@[simp] theorem weight_monomialOf [Nontrivial K] (a : ℕ) :
    weight (monomialOf (K := K) a) = 1 := by
  simp [weight]

@[simp] theorem polynomialOf_empty (c : ℕ → K) : polynomialOf ∅ c = 0 := by
  simp [polynomialOf]

@[simp] theorem polynomialOf_singleton (a : ℕ) (c : ℕ → K) :
    polynomialOf {a} c = MvPolynomial.monomial a.factorization (c a) := by
  simp [polynomialOf]

theorem coeff_polynomialOf (A : Finset ℕ) (c : ℕ → K)
    (hA : ∀ b ∈ A, 0 < b) {a : ℕ} (ha : 0 < a) :
    MvPolynomial.coeff a.factorization (polynomialOf A c) =
      if a ∈ A then c a else 0 := by
  classical
  rw [polynomialOf, MvPolynomial.coeff_sum]
  by_cases hmem : a ∈ A
  · rw [if_pos hmem, Finset.sum_eq_single a]
    · simp [MvPolynomial.coeff_monomial]
    · intro b hb hba
      have hfac : b.factorization ≠ a.factorization := fun h =>
        hba (Nat.factorization_inj (ne_of_gt (hA b hb)) (ne_of_gt ha) h)
      simp [MvPolynomial.coeff_monomial, hfac]
    · intro h
      exact False.elim (h hmem)
  · rw [if_neg hmem]
    apply Finset.sum_eq_zero
    intro b hb
    have hfac : b.factorization ≠ a.factorization := by
      intro h
      have hba := Nat.factorization_inj (ne_of_gt (hA b hb)) (ne_of_gt ha) h
      exact hmem (hba ▸ hb)
    simp [MvPolynomial.coeff_monomial, hfac]

theorem support_polynomialOf (A : Finset ℕ) (c : ℕ → K)
    (hA : ∀ a ∈ A, 0 < a) (hc : ∀ a ∈ A, c a ≠ 0) :
    (polynomialOf A c).support = A.image Nat.factorization := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [polynomialOf]
  | @insert a A ha ih =>
    have hapos : 0 < a := hA a (Finset.mem_insert_self a A)
    have hApos : ∀ b ∈ A, 0 < b := fun b hb => hA b (Finset.mem_insert_of_mem hb)
    have hca := hc a (Finset.mem_insert_self a A)
    have hcA : ∀ b ∈ A, c b ≠ 0 := fun b hb => hc b (Finset.mem_insert_of_mem hb)
    have hi := ih hApos hcA
    have hsup : (MvPolynomial.monomial a.factorization (c a) : Poly K).support =
        {a.factorization} := by simp [MvPolynomial.support_monomial, hca]
    have hdis : Disjoint
        (MvPolynomial.monomial a.factorization (c a) : Poly K).support
        (polynomialOf A c).support := by
      rw [hsup, Finset.disjoint_singleton_left, hi]
      intro hmem
      obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hmem
      have hba : b = a := Nat.factorization_inj (ne_of_gt (hApos b hb))
        (ne_of_gt hapos) heq
      exact ha (hba ▸ hb)
    have hpoly : polynomialOf (insert a A) c =
        MvPolynomial.monomial a.factorization (c a) + polynomialOf A c := by
      simp [polynomialOf, ha]
    have hadd : (MvPolynomial.monomial a.factorization (c a) + polynomialOf A c).support =
        (MvPolynomial.monomial a.factorization (c a)).support ∪
          (polynomialOf A c).support := Finsupp.support_add_eq hdis
    rw [hpoly, hadd, hsup, hi]
    simp

theorem weight_polynomialOf (A : Finset ℕ) (c : ℕ → K)
    (hA : ∀ a ∈ A, 0 < a) (hc : ∀ a ∈ A, c a ≠ 0) :
    weight (polynomialOf A c) = A.card := by
  classical
  rw [weight, support_polynomialOf A c hA hc]
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  exact Nat.factorization_inj (ne_of_gt (hA a ha)) (ne_of_gt (hA b hb)) hab

theorem polynomialOf_ne_zero (A : Finset ℕ) (c : ℕ → K)
    (hA : ∀ a ∈ A, 0 < a) (hc : ∀ a ∈ A, c a ≠ 0)
    (hne : A.Nonempty) : polynomialOf A c ≠ 0 := by
  intro h
  have := weight_polynomialOf A c hA hc
  rw [h, weight_zero] at this
  exact (Finset.card_pos.mpr hne).ne' this.symm

theorem support_interval (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c) :
    (interval n c).support = (Finset.Icc 1 n).image Nat.factorization := by
  exact support_polynomialOf _ c (fun _ ha => (Finset.mem_Icc.mp ha).1) hc

theorem weight_interval (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c) :
    weight (interval n c) = n := by
  rw [interval, weight_polynomialOf _ c (fun _ ha => (Finset.mem_Icc.mp ha).1) hc]
  simp

theorem coeff_interval (n : ℕ) (c : ℕ → K) {a : ℕ} (ha : 0 < a) :
    MvPolynomial.coeff a.factorization (interval n c) =
      if a ≤ n then c a else 0 := by
  rw [interval, coeff_polynomialOf _ c (fun _ hb => (Finset.mem_Icc.mp hb).1) ha]
  simp [Nat.one_le_iff_ne_zero.mpr (ne_of_gt ha)]

theorem interval_ne_zero {n : ℕ} (c : ℕ → K) (hn : 0 < n)
    (hc : NonzeroWeights n c) : interval n c ≠ 0 := by
  intro h
  have := weight_interval n c hc
  rw [h, weight_zero] at this
  exact hn.ne' this.symm

@[simp] theorem interval_zero (c : ℕ → K) : interval 0 c = 0 := by
  simp [interval, polynomialOf]

@[simp] theorem interval_one (c : ℕ → K) : interval 1 c = MvPolynomial.C (c 1) := by
  simp [interval, polynomialOf]

theorem interval_succ (n : ℕ) (c : ℕ → K) :
    interval (n + 1) c = interval n c + MvPolynomial.monomial (n + 1).factorization (c (n + 1)) := by
  exact Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n))
    (fun a => MvPolynomial.monomial a.factorization (c a))

/-- A nonzero scalar monomial attains the requested bound exactly. -/
theorem weight_interval_mul_scalar_monomial [NoZeroDivisors K]
    (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c)
    (e : ℕ →₀ ℕ) {u : K} (hu : u ≠ 0) :
    weight (interval n c * MvPolynomial.monomial e u) = n := by
  have hs : (interval n c * MvPolynomial.monomial e u).support =
      (interval n c).support.map (addRightEmbedding e) :=
    AddMonoidAlgebra.support_mul_single (interval n c) u (by simp [hu]) e
  simpa only [weight, hs, Finset.card_map] using weight_interval n c hc

/-- Singleton arithmetic inputs attain equality, independently of their position. -/
theorem weight_interval_mul_monomialOf [Nontrivial K] (n a : ℕ)
    (c : ℕ → K) (hc : NonzeroWeights n c) :
    weight (interval n c * monomialOf a) = n := by
  have hs : (interval n c * monomialOf a).support =
      (interval n c).support.map (addRightEmbedding a.factorization) :=
    AddMonoidAlgebra.support_mul_single (interval n c) 1 (by simp) a.factorization
  simpa only [weight, hs, Finset.card_map] using weight_interval n c hc

end WeightedPilz

namespace WeightedPilz

variable {K : Type*} [Field K]

theorem intervalBound_zero (c : ℕ → K) : IntervalBound 0 c := by
  intro H hH
  exact Nat.zero_le _

theorem intervalBound_one (c : ℕ → K) (hc : NonzeroWeights 1 c) :
    IntervalBound 1 c := by
  intro H hH
  exact weight_pos (mul_ne_zero (interval_ne_zero c Nat.one_pos hc) hH)

end WeightedPilz

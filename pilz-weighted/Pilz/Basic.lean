import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat

/-!
# The arithmetic polynomial model

This file translates the encoding in Section 2 of the journal manuscript.
Natural-number variable names are used; the canonical monomials have nonzero
exponents only at prime variable names. All arithmetic inputs are positive:
`Nat.factorization 0 = Nat.factorization 1`, so zero must never be admitted as
an encoded integer.
-/

namespace Pilz

open scoped BigOperators

abbrev Poly := MvPolynomial ℕ (ZMod 2)

/-- The number of nonzero monomials. -/
def weight (P : Poly) : ℕ := P.support.card

/-- The monomial `X(a)` of the paper. Its intended domain is positive integers. -/
noncomputable def monomialOf (a : ℕ) : Poly :=
  MvPolynomial.monomial a.factorization 1

/-- The polynomial associated to a finite set of positive integers. -/
noncomputable def polynomialOf (A : Finset ℕ) : Poly :=
  ∑ a ∈ A, monomialOf a

/-- The interval polynomial `F_n`. -/
noncomputable def interval (n : ℕ) : Poly :=
  ∑ a ∈ Finset.Icc 1 n, monomialOf a

@[simp] theorem polynomialOf_empty : polynomialOf ∅ = 0 := by simp [polynomialOf]

@[simp] theorem polynomialOf_singleton (a : ℕ) : polynomialOf {a} = monomialOf a := by
  simp [polynomialOf]

/-- The polynomial form of Theorem A at one interval length. -/
def ConjectureAt (n : ℕ) : Prop :=
  ∀ H : Poly, H ≠ 0 → n ≤ weight (interval n * H)

@[simp] theorem weight_zero : weight 0 = 0 := by simp [weight]

theorem weight_pos {P : Poly} (hP : P ≠ 0) : 0 < weight P := by
  simpa [weight, Finset.card_pos, MvPolynomial.support_nonempty] using hP

@[simp] theorem monomialOf_one : monomialOf 1 = 1 := by
  simp only [monomialOf, Nat.factorization_one]
  rfl

theorem monomialOf_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    monomialOf (a * b) = monomialOf a * monomialOf b := by
  simp [monomialOf, Nat.factorization_mul ha hb, MvPolynomial.monomial_mul]

theorem monomialOf_prime {p : ℕ} (hp : p.Prime) : monomialOf p = MvPolynomial.X p := by
  rw [monomialOf, hp.factorization]
  rfl

theorem monomialOf_injective {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    monomialOf a = monomialOf b ↔ a = b := by
  constructor
  · intro h
    apply Nat.factorization_inj ha hb
    exact MvPolynomial.monomial_left_injective (one_ne_zero : (1 : ZMod 2) ≠ 0) h
  · rintro rfl
    rfl

@[simp] theorem support_monomialOf (a : ℕ) :
    (monomialOf a).support = {a.factorization} := by
  simp [monomialOf, MvPolynomial.support_monomial]

@[simp] theorem weight_monomialOf (a : ℕ) : weight (monomialOf a) = 1 := by
  simp [weight]

theorem support_polynomialOf (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    (polynomialOf A).support = A.image Nat.factorization := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [polynomialOf]
  | @insert a A ha ih =>
    have hapos : 0 < a := hA a (Finset.mem_insert_self a A)
    have hApos : ∀ b ∈ A, 0 < b := fun b hb => hA b (Finset.mem_insert_of_mem hb)
    have hi := ih hApos
    have hdis : Disjoint (monomialOf a).support (polynomialOf A).support := by
      rw [support_monomialOf, Finset.disjoint_singleton_left, hi]
      intro hmem
      obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hmem
      have hba : b = a := Nat.factorization_inj (ne_of_gt (hApos b hb))
        (ne_of_gt hapos) heq
      exact ha (hba ▸ hb)
    have hpoly : polynomialOf (insert a A) = monomialOf a + polynomialOf A := by
      simp [polynomialOf, ha]
    rw [hpoly]
    have hadd : (monomialOf a + polynomialOf A).support =
        (monomialOf a).support ∪ (polynomialOf A).support := Finsupp.support_add_eq hdis
    rw [hadd, support_monomialOf, hi]
    simp

theorem weight_polynomialOf (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    weight (polynomialOf A) = A.card := by
  classical
  rw [weight, support_polynomialOf A hA]
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  exact Nat.factorization_inj (ne_of_gt (hA a ha)) (ne_of_gt (hA b hb)) hab

theorem coeff_polynomialOf (A : Finset ℕ) (hA : ∀ b ∈ A, 0 < b)
    {a : ℕ} (ha : 0 < a) :
    MvPolynomial.coeff a.factorization (polynomialOf A) = if a ∈ A then 1 else 0 := by
  classical
  rw [polynomialOf, MvPolynomial.coeff_sum]
  by_cases hmem : a ∈ A
  · rw [if_pos hmem, Finset.sum_eq_single a]
    · simp [monomialOf, MvPolynomial.coeff_monomial]
    · intro b hb hba
      have hfac : b.factorization ≠ a.factorization := fun h =>
        hba (Nat.factorization_inj (ne_of_gt (hA b hb)) (ne_of_gt ha) h)
      simp [monomialOf, MvPolynomial.coeff_monomial, hfac]
    · intro h
      exact False.elim (h hmem)
  · rw [if_neg hmem]
    apply Finset.sum_eq_zero
    intro b hb
    have hfac : b.factorization ≠ a.factorization := by
      intro h
      have hba := Nat.factorization_inj (ne_of_gt (hA b hb)) (ne_of_gt ha) h
      exact hmem (hba ▸ hb)
    simp [monomialOf, MvPolynomial.coeff_monomial, hfac]

theorem polynomialOf_ne_zero (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (hne : A.Nonempty) : polynomialOf A ≠ 0 := by
  intro h
  have := weight_polynomialOf A hA
  rw [h, weight_zero] at this
  exact (Finset.card_pos.mpr hne).ne' this.symm

theorem interval_eq_polynomialOf (n : ℕ) :
    interval n = polynomialOf (Finset.Icc 1 n) := rfl

@[simp] theorem weight_interval (n : ℕ) : weight (interval n) = n := by
  rw [interval_eq_polynomialOf, weight_polynomialOf]
  · simp
  · intro a ha
    exact (Finset.mem_Icc.mp ha).1

theorem interval_ne_zero {n : ℕ} (hn : 0 < n) : interval n ≠ 0 := by
  intro h
  have := weight_interval n
  rw [h, weight_zero] at this
  exact hn.ne' this.symm

@[simp] theorem interval_zero : interval 0 = 0 := by simp [interval]

@[simp] theorem interval_one : interval 1 = 1 := by simp [interval]

theorem interval_succ (n : ℕ) : interval (n + 1) = interval n + monomialOf (n + 1) := by
  exact Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)) monomialOf

theorem conjectureAt_zero : ConjectureAt 0 := by
  intro H hH
  exact Nat.zero_le _

theorem conjectureAt_one : ConjectureAt 1 := by
  intro H hH
  simpa using weight_pos hH

end Pilz

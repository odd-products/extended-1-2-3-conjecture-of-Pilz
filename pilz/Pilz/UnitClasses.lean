import Pilz.Protection

/-! Unit parity classes survive a one-class multiplier and the protected
normal-form argument. The finite family of arithmetic unit classes is
supplied separately by the interval calculation. -/

noncomputable section

namespace Pilz

open MvPolynomial
open scoped BigOperators

theorem parityIndex_lt_two {P : Poly} {η : ℕ →₀ ℕ} (hη : η ∈ parityIndices P) :
    ∀ i, η i < 2 := by
  classical
  obtain ⟨d, _hd, rfl⟩ := Finset.mem_image.mp hη
  exact fun i => Nat.mod_lt _ (by decide)

theorem parityExponent_add_inj {η μ ν : ℕ →₀ ℕ}
    (hμ : ∀ i, μ i < 2) (hν : ∀ i, ν i < 2)
    (heq : parityExponent (η + μ) = parityExponent (η + ν)) : μ = ν := by
  ext i
  have hi := congrArg (fun d : ℕ →₀ ℕ => d i) heq
  simp only [parityExponent_apply, Finsupp.add_apply] at hi
  have hμi := hμ i
  have hνi := hν i
  omega

/-- Multiplication by a monomial translates the full parity classes. -/
theorem parityClass_monomial_mul_shift (s μ : ℕ →₀ ℕ) (hμ : ∀ i, μ i < 2) (P : Poly) :
    parityClass (monomial s 1 * P) (parityExponent (s + μ)) =
      monomial s 1 * parityClass P μ := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
      have hpar : (∀ i, (s + d) i % 2 = parityExponent (s + μ) i) ↔
          (∀ i, d i % 2 = μ i) := by
        constructor
        · intro h i
          have hi := h i
          have hμi := hμ i
          simp only [parityExponent_apply, Finsupp.add_apply] at hi
          omega
        · intro h i
          have hi := h i
          simp only [parityExponent_apply, Finsupp.add_apply]
          omega
      rw [monomial_mul, one_mul, parityClass_monomial, parityClass_monomial]
      by_cases h : ∀ i, d i % 2 = μ i
      · rw [if_pos h, if_pos (hpar.mpr h), monomial_mul, one_mul]
      · rw [if_neg h, if_neg (fun hs => h (hpar.mp hs)), mul_zero]
  | add P Q hP hQ =>
      simp only [mul_add, parityClass_add, hP, hQ]

theorem exists_single_parity_class (D : Poly) (hclasses : (parityIndices D).card = 1) :
    ∃ η : ℕ →₀ ℕ, (∀ i, η i < 2) ∧
      D = monomial η 1 * (classRoot D η) ^ 2 := by
  classical
  obtain ⟨η, hη⟩ := Finset.card_eq_one.mp hclasses
  have hmem : η ∈ parityIndices D := by rw [hη]; simp
  have hsum := sum_parityClasses D
  rw [hη, Finset.sum_singleton] at hsum
  refine ⟨η, parityIndex_lt_two hmem, ?_⟩
  exact hsum.symm.trans (parityClass_eq_monomial_mul_square D η)

/-- A one-class multiplier translates each class of the first factor,
with its square factor acting inside the translated class. -/
theorem parityClass_mul_single_class (C D : Poly) (η μ : ℕ →₀ ℕ)
    (hμ : ∀ i, μ i < 2)
    (hD : D = monomial η 1 * (classRoot D η) ^ 2) :
    parityClass (C * D) (parityExponent (η + μ)) =
      monomial η 1 * (parityClass C μ * (classRoot D η) ^ 2) := by
  calc
    parityClass (C * D) (parityExponent (η + μ)) =
      parityClass (C * (monomial η 1 * (classRoot D η) ^ 2))
        (parityExponent (η + μ)) :=
      congrArg (fun Q => parityClass (C * Q) (parityExponent (η + μ))) hD
    _ =
      parityClass ((classRoot D η) ^ 2 * (monomial η 1 * C))
        (parityExponent (η + μ)) := by congr 1; ac_rfl
    _ = (classRoot D η) ^ 2 *
        parityClass (monomial η 1 * C) (parityExponent (η + μ)) :=
      parityClass_square_mul _ _ _
    _ = (classRoot D η) ^ 2 * (monomial η 1 * parityClass C μ) := by
      rw [parityClass_monomial_mul_shift η μ hμ]
    _ = monomial η 1 * (parityClass C μ * (classRoot D η) ^ 2) := by ac_rfl

theorem classWeight_mul_single_class_unit (C D : Poly) (η μ : ℕ →₀ ℕ)
    (hμ : ∀ i, μ i < 2)
    (hD : D = monomial η 1 * (classRoot D η) ^ 2)
    (hunit : parityClass C μ = monomial μ 1) :
    classWeight (C * D) (parityExponent (η + μ)) = weight D := by
  rw [← weight_parityClass, parityClass_mul_single_class C D η μ hμ hD, hunit,
    weight_monomial_mul, weight_monomial_mul]
  exact (congrArg weight hD).trans (weight_monomial_mul η _)
    |>.symm

/-- Every protected unit core class contributes the complete multiplier
weight, and all the fresh rows contribute as well. -/
theorem normalForm_unit_classes (S : FreshData) (N : ℕ) (nf : NormalFormData S N)
    (hN : N ≤ weight S.C + S.vars.card) (A : Finset (ℕ →₀ ℕ))
    (hbits : ∀ μ ∈ A, ∀ i, μ i < 2)
    (hunit : ∀ μ ∈ A, parityClass S.C μ = monomial μ 1)
    (hclasses : (parityIndices nf.D).card = 1) :
    (A.card + S.vars.card) * weight nf.D ≤ weight nf.G := by
  classical
  obtain ⟨η, _hη, hD⟩ := exists_single_parity_class nf.D hclasses
  let shift := fun μ : ℕ →₀ ℕ => parityExponent (η + μ)
  have hshift : Set.InjOn shift (A : Set (ℕ →₀ ℕ)) := by
    intro μ hμ ν hν heq
    exact parityExponent_add_inj (hbits μ hμ) (hbits ν hν) heq
  have hunitprod : ∀ μ ∈ A, classWeight (S.C * nf.D) (shift μ) = weight nf.D := by
    intro μ hμ
    exact classWeight_mul_single_class_unit S.C nf.D η μ (hbits μ hμ) hD (hunit μ hμ)
  have hr : 1 ≤ S.vars.card := Finset.card_pos.mpr S.nonempty
  have hbudget := normalForm_weight S N nf
  have hcost := normalForm_residual_cost S N nf hN
  have hsurvive : ∀ μ ∈ A, weight nf.D ≤ classWeight nf.G₀ (shift μ) := by
    intro μ hμ
    have hcap : classWeight (S.C * nf.D) (shift μ) ≤ S.vars.card * weight nf.D := by
      rw [hunitprod μ hμ]
      simpa using Nat.mul_le_mul_right (weight nf.D) hr
    have hzero := protected_class nf.G₀ S.C nf.D (nf.G₀ + S.C * nf.D)
      (shift μ) N (weight nf.G) S.vars.card (weight nf.D) rfl nf.extremal.1.2.2
      hbudget hcap (hcost (shift μ))
    have hsum : nf.G₀ + (nf.G₀ + S.C * nf.D) = S.C * nf.D := by
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    have htriangle := classWeight_add_le nf.G₀ (nf.G₀ + S.C * nf.D) (shift μ)
    rw [hsum, hzero, add_zero, hunitprod μ hμ] at htriangle
    exact htriangle
  have hcore : A.card * weight nf.D ≤ weight nf.G₀ := by
    calc
      A.card * weight nf.D = (A.image shift).card * weight nf.D := by
        rw [Finset.card_image_iff.mpr hshift]
      _ = ∑ _ε ∈ A.image shift, weight nf.D := by simp
      _ ≤ ∑ ε ∈ A.image shift, classWeight nf.G₀ ε := by
        apply Finset.sum_le_sum
        intro ε hε
        obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hε
        exact hsurvive μ hμ
      _ ≤ weight nf.G₀ := sum_classWeights_le nf.G₀ (A.image shift)
  rw [Nat.add_mul]
  exact (Nat.add_le_add_right hcore _).trans_eq hbudget

end Pilz

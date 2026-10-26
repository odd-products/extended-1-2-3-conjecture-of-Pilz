import WeightedPilz.Binary
import WeightedPilz.FinalConsequences

/-!
# Equality in Pilz's conjecture at prime indices

The finite-set interface uses natural numbers with explicit positivity, as in
`WeightedPilz.Binary`.  In particular the translating monomial is proved to be
the factorization monomial of a positive integer, rather than an arbitrary
monomial in the ambient polynomial ring.
-/

noncomputable section

namespace WeightedPilz

private theorem binary_output_positive (n : ℕ) (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) :
    ∀ m ∈ intervalSymmetricDifference n A, 0 < m := by
  rw [intervalSymmetricDifference_eq_oddProduct n A hA]
  exact Pilz.oddProduct_positive A (Finset.Icc 1 n) hA
    (fun _ ha => (Finset.mem_Icc.mp ha).1)

private theorem binary_output_polynomial (n : ℕ) (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) :
    Pilz.polynomialOf (intervalSymmetricDifference n A) =
      interval n (fun _ => (1 : ZMod 2)) * Pilz.polynomialOf A := by
  rw [intervalSymmetricDifference_eq_oddProduct n A hA,
    Pilz.polynomialOf_oddProduct A (Finset.Icc 1 n) hA
      (fun _ ha => (Finset.mem_Icc.mp ha).1)]
  exact mul_comm _ _

private theorem positive_factorization_image_injective (A B : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hB : ∀ b ∈ B, 0 < b)
    (h : A.image Nat.factorization = B.image Nat.factorization) : A = B := by
  classical
  ext a
  constructor
  · intro ha
    have hm : a.factorization ∈ B.image Nat.factorization := by
      rw [← h]
      exact Finset.mem_image_of_mem _ ha
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hm
    have hba' := Nat.factorization_inj (hB b hb).ne' (hA a ha).ne' hba
    exact hba' ▸ hb
  · intro ha
    have hm : a.factorization ∈ A.image Nat.factorization := by
      rw [h]
      exact Finset.mem_image_of_mem _ ha
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hm
    have hba' := Nat.factorization_inj (hA b hb).ne' (hB a ha).ne' hba
    exact hba' ▸ hb

private theorem binary_frobenius_translate_support (n b e : ℕ) (hb : 0 < b) :
    (monomialOf (K := ZMod 2) b * interval n (fun _ => (1 : ZMod 2)) ^ (2 ^ e)).support =
      ((Finset.Icc 1 n).image (fun a => b * a ^ (2 ^ e))).image Nat.factorization := by
  classical
  have hs : (monomialOf (K := ZMod 2) b * interval n (fun _ => (1 : ZMod 2)) ^ (2 ^ e)).support =
      (interval n (fun _ => (1 : ZMod 2)) ^ (2 ^ e)).support.map
        (addLeftEmbedding b.factorization) :=
    AddMonoidAlgebra.support_single_mul _ 1 (by simp) b.factorization
  rw [hs]
  rw [support_pow_expChar 2 e, support_interval n _ (fun _ _ => one_ne_zero)]
  simp only [Finset.map_eq_image, Finset.image_image, Function.comp_def]
  apply Finset.image_congr
  intro a ha
  change b.factorization + (2 ^ e) • a.factorization = (b * a ^ (2 ^ e)).factorization
  rw [Nat.factorization_mul hb.ne'
      (pow_ne_zero (2 ^ e) (ne_of_gt (show 0 < a from (Finset.mem_Icc.mp ha).1))),
    Nat.factorization_pow]

/-- Every binary prime-equality input has this exact output, a dilated
Frobenius image of the integer interval.  The implication itself holds for
every interval length. -/
theorem binary_prime_equality_output (n : ℕ) (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (b e : ℕ) (hb : 0 < b)
    (hform : Pilz.polynomialOf A =
      monomialOf b * interval n (fun _ => (1 : ZMod 2)) ^ (2 ^ e - 1)) :
    intervalSymmetricDifference n A =
      (Finset.Icc 1 n).image (fun a => b * a ^ (2 ^ e)) := by
  classical
  have hprod : interval n (fun _ => (1 : ZMod 2)) * Pilz.polynomialOf A =
      monomialOf b * interval n (fun _ => (1 : ZMod 2)) ^ (2 ^ e) := by
    rw [hform, mul_left_comm, ← pow_succ', Nat.sub_add_cancel]
    exact Nat.one_le_pow _ _ (by decide)
  apply positive_factorization_image_injective _ _ (binary_output_positive n A hA)
  · intro m hm
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hm
    exact Nat.mul_pos hb (pow_pos (Finset.mem_Icc.mp ha).1 _)
  · rw [← Pilz.support_polynomialOf _ (binary_output_positive n A hA),
      binary_output_polynomial n A hA, hprod,
      binary_frobenius_translate_support n b e hb]

/-- Complete equality classification for the original binary Pilz problem
at prime indices at least three. -/
theorem binary_prime_equality_iff (ℓ : ℕ) (hℓ : ℓ.Prime) (hthree : 3 ≤ ℓ)
    (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    (intervalSymmetricDifference ℓ A).card = ℓ ↔
      ∃ b e : ℕ, 0 < b ∧ Pilz.polynomialOf A =
        monomialOf b * interval ℓ (fun _ => (1 : ZMod 2)) ^ (2 ^ e - 1) := by
  classical
  constructor
  · intro hw
    have hw' : weight (interval ℓ (fun _ => (1 : ZMod 2)) * Pilz.polynomialOf A) = ℓ := by
      rw [← binary_output_polynomial ℓ A hA]
      exact (Pilz.weight_polynomialOf _ (binary_output_positive ℓ A hA)).trans hw
    obtain ⟨e, d, a, ha, hout, hinput⟩ := prime_index_multiplier_rigidity
      2 ℓ hℓ hthree (fun _ => (1 : ZMod 2)) (fun _ _ => one_ne_zero)
      (Pilz.polynomialOf A) (Pilz.polynomialOf_ne_zero A hA hne) hw'
    have haone : a = 1 := by
      apply ZMod.val_injective 2
      have halt := ZMod.val_lt a
      have hanz : a.val ≠ 0 := (ZMod.val_eq_zero a).not.mpr ha
      change a.val = 1
      omega
    subst a
    have hzero : (0 : ℕ →₀ ℕ) ∈
        (interval ℓ (fun _ => (1 : ZMod 2)) ^ (2 ^ e)).support := by
      rw [support_pow_expChar 2 e, support_interval ℓ _ (fun _ _ => one_ne_zero)]
      simp only [Finset.mem_image]
      refine ⟨0, ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, Nat.factorization_one⟩, ?_⟩
      · simp [scaleExponent]
    have hd : d ∈ (interval ℓ (fun _ => (1 : ZMod 2)) * Pilz.polynomialOf A).support := by
      have hs : (MvPolynomial.monomial d 1 * interval ℓ (fun _ => (1 : ZMod 2)) ^ (2 ^ e)).support =
          (interval ℓ (fun _ => (1 : ZMod 2)) ^ (2 ^ e)).support.map (addLeftEmbedding d) :=
        AddMonoidAlgebra.support_single_mul _ 1 (by simp) d
      rw [hout, hs]
      exact Finset.mem_map.mpr ⟨0, hzero, by simp⟩
    rw [← binary_output_polynomial ℓ A hA,
      Pilz.support_polynomialOf _ (binary_output_positive ℓ A hA)] at hd
    obtain ⟨b, hb, hbd⟩ := Finset.mem_image.mp hd
    refine ⟨b, e, binary_output_positive ℓ A hA b hb, ?_⟩
    simpa only [monomialOf, hbd] using hinput
  · rintro ⟨b, e, hb, hform⟩
    rw [binary_prime_equality_output ℓ A hA b e hb hform,
      Finset.card_image_of_injective]
    · simp
    · intro a c hac
      exact Nat.pow_left_injective (pow_ne_zero _ (by decide : 2 ≠ 0))
        (Nat.eq_of_mul_eq_mul_left hb hac)

end WeightedPilz

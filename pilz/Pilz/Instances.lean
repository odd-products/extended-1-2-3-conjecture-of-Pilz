import Pilz.OddProduct
import Pilz.Parity
import Pilz.Support

/-! Checked finite-set consequences, including the paper's equality families. -/

namespace Pilz

theorem polynomialOf_injective_positive (A B : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hB : ∀ b ∈ B, 0 < b)
    (hpoly : polynomialOf A = polynomialOf B) : A = B := by
  classical
  ext a
  by_cases ha : 0 < a
  · have hc := congrArg (MvPolynomial.coeff a.factorization) hpoly
    rw [coeff_polynomialOf A hA ha, coeff_polynomialOf B hB ha] at hc
    by_cases hma : a ∈ A <;> by_cases hmb : a ∈ B <;> simp_all
  · have hma : a ∉ A := fun h => ha (hA a h)
    have hmb : a ∉ B := fun h => ha (hB a h)
    simp [hma, hmb]

/-- The full finite-set squaring identity, valid for every positive finite set. -/
theorem oddProduct_self (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    oddProduct A A = A.image (fun a => a * a) := by
  classical
  have hsqpos : ∀ b ∈ A.image (fun a => a * a), 0 < b := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact Nat.mul_pos (hA a ha) (hA a ha)
  apply polynomialOf_injective_positive _ _ (oddProduct_positive A A hA hA) hsqpos
  rw [polynomialOf_oddProduct A A hA hA]
  symm
  calc
    polynomialOf (A.image (fun a => a * a)) = ∑ a ∈ A, monomialOf (a * a) := by
      unfold polynomialOf
      exact Finset.sum_image (fun a _ b _ h => Nat.mul_self_inj.mp h)
    _ = ∑ a ∈ A, monomialOf a ^ 2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [monomialOf_mul (ne_of_gt (hA a ha)) (ne_of_gt (hA a ha)), pow_two]
    _ = polynomialOf A ^ 2 := (CharTwo.sum_sq A monomialOf).symm
    _ = polynomialOf A * polynomialOf A := pow_two _

/-- Singleton multipliers attain the proposed bound, for every interval length. -/
theorem singleton_interval_card (a n : ℕ) (ha : 0 < a) :
    (oddProduct {a} (Finset.Icc 1 n)).card = n := by
  have hA : ∀ b ∈ ({a} : Finset ℕ), 0 < b := by simpa
  have hI : ∀ b ∈ Finset.Icc 1 n, 0 < b := fun _ hb => (Finset.mem_Icc.mp hb).1
  rw [← weight_mul_polynomialOf {a} (Finset.Icc 1 n) hA hI]
  simpa [← interval_eq_polynomialOf, mul_comm] using weight_interval_mul_monomialOf n a

/-- The interval self-multiplier also attains equality for every `n`. -/
theorem interval_self_card (n : ℕ) :
    (oddProduct (Finset.Icc 1 n) (Finset.Icc 1 n)).card = n := by
  have hI : ∀ b ∈ Finset.Icc 1 n, 0 < b := fun _ hb => (Finset.mem_Icc.mp hb).1
  rw [← weight_mul_polynomialOf _ _ hI hI]
  exact weight_interval_self_mul n

/-- Unconditional original finite-set form for `n ≤ 2`. -/
theorem oddProduct_interval_lower_bound_le_two (n : ℕ) (hn : n ≤ 2)
    (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    n ≤ (oddProduct A (Finset.Icc 1 n)).card := by
  have h : ConjectureAt n := by
    have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact conjectureAt_zero
    · exact conjectureAt_one
    · exact conjectureAt_two
  exact oddProduct_interval_lower_bound h A hA hne

end Pilz

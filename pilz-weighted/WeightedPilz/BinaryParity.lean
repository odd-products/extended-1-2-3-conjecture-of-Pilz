import WeightedPilz.FieldTheorem
import Pilz.Parity
import Mathlib.Data.Finset.SymmDiff

/-!
# Parity and the sharp odd-index refinement

The elementary parity identity, already used by Holdridge--Pach, combines
with the full interval theorem to improve the bound by one when the interval
length is odd and the input has even cardinality.  The two-element input
`{1, 2}` attains the improved bound at every odd interval length.
-/

noncomputable section

namespace WeightedPilz

open scoped symmDiff

/-- Counting multiplicative representations modulo two gives the parity of
the original symmetric-difference output. -/
theorem symmetric_difference_card_mod_two (n : ℕ) (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) :
    (intervalSymmetricDifference n A).card % 2 = (n * A.card) % 2 := by
  have hI : ∀ b ∈ Finset.Icc 1 n, 0 < b :=
    fun _ hb => (Finset.mem_Icc.mp hb).1
  rw [intervalSymmetricDifference_eq_oddProduct n A hA,
    ← Pilz.weight_mul_polynomialOf A (Finset.Icc 1 n) hA hI,
    Pilz.weight_mul_mod_two, Pilz.weight_polynomialOf A hA,
    Pilz.weight_polynomialOf (Finset.Icc 1 n) hI]
  simp [Nat.mul_comm]

/-- For odd interval length, a nonempty even-cardinality input produces at
least one more output than the general Pilz lower bound. -/
theorem symmetric_difference_odd_even_bound (n : ℕ) (hn : Odd n)
    (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty)
    (heven : Even A.card) :
    n + 1 ≤ (intervalSymmetricDifference n A).card := by
  have hbound := weighted_symmetric_difference n A hA hne
  have hpar := symmetric_difference_card_mod_two n A hA
  have hnmod := Nat.odd_iff.mp hn
  have hAmod := Nat.even_iff.mp heven
  rw [Nat.mul_mod, hAmod] at hpar
  simp only [Nat.mul_zero, Nat.zero_mod] at hpar
  omega

private theorem two_input_output (n : ℕ) :
    intervalSymmetricDifference n {1, 2} =
      dilatedInterval n 1 ∆ dilatedInterval n 2 := by
  ext m
  rw [mem_intervalSymmetricDifference, Finset.mem_symmDiff]
  by_cases h1 : m ∈ dilatedInterval n 1 <;>
    by_cases h2 : m ∈ dilatedInterval n 2 <;>
      simp [Finset.filter_insert, Finset.filter_singleton, h1, h2]

private theorem interval_inter_double (n : ℕ) :
    dilatedInterval n 1 ∩ dilatedInterval n 2 =
      (Finset.Icc 1 (n / 2)).image (2 * ·) := by
  ext m
  simp only [Finset.mem_inter, dilatedInterval, Finset.mem_image, Finset.mem_Icc,
    one_mul, exists_eq_right]
  constructor
  · rintro ⟨hm, k, hk, rfl⟩
    exact ⟨k, ⟨hk.1, (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
      (by omega)⟩, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    have hkn := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp hk.2
    exact ⟨⟨by omega, by omega⟩, k, ⟨hk.1, by omega⟩, rfl⟩

/-- The exact two-element calculation, including the empty interval. -/
theorem symmetric_difference_one_two_card (n : ℕ) :
    (intervalSymmetricDifference n {1, 2}).card = 2 * n - 2 * (n / 2) := by
  have hc1 : (dilatedInterval n 1).card = n := by
    simp [dilatedInterval]
  have hc2 : (dilatedInterval n 2).card = n := by
    rw [dilatedInterval, Finset.card_image_of_injective _
      (fun _ _ h => Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h)]
    simp
  have hci : (dilatedInterval n 1 ∩ dilatedInterval n 2).card = n / 2 := by
    rw [interval_inter_double, Finset.card_image_of_injective _
      (fun _ _ h => Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h)]
    simp
  rw [two_input_output]
  change ((dilatedInterval n 1 \ dilatedInterval n 2) ∪
    (dilatedInterval n 2 \ dilatedInterval n 1)).card = _
  rw [Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  have h1 := Finset.card_sdiff_add_card_inter (dilatedInterval n 1) (dilatedInterval n 2)
  have h2 := Finset.card_sdiff_add_card_inter (dilatedInterval n 2) (dilatedInterval n 1)
  rw [hc1, hci] at h1
  rw [Finset.inter_comm, hci, hc2] at h2
  omega

/-- The odd-index improvement is sharp, witnessed by `{1, 2}` even for `n = 1`. -/
theorem symmetric_difference_odd_even_sharpness (n : ℕ) (hn : Odd n) :
    (intervalSymmetricDifference n {1, 2}).card = n + 1 := by
  rw [symmetric_difference_one_two_card]
  have hmod := Nat.odd_iff.mp hn
  omega

end WeightedPilz

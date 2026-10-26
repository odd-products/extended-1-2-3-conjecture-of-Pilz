import WeightedPilz.Support
import Mathlib.Data.Finset.Prod

/-! Exact multiplication of support sizes when all exponent sums are distinct. -/

noncomputable section

namespace WeightedPilz

open MvPolynomial
open scoped BigOperators

variable {σ R : Type*} [DecidableEq σ] [CommSemiring R] [NoZeroDivisors R]

theorem coeff_mul_of_injective_support_add (P Q : MvPolynomial σ R)
    (hadd : Set.InjOn (fun ab : (σ →₀ ℕ) × (σ →₀ ℕ) => ab.1 + ab.2)
      (↑(P.support ×ˢ Q.support)))
    {a b : σ →₀ ℕ} (ha : a ∈ P.support) (hb : b ∈ Q.support) :
    coeff (a + b) (P * Q) = coeff a P * coeff b Q := by
  rw [coeff_mul]
  apply Finset.sum_eq_single (a, b)
  · intro x hx hne
    by_cases hp : coeff x.1 P = 0
    · simp [hp]
    by_cases hq : coeff x.2 Q = 0
    · simp [hq]
    have heq : x = (a, b) := hadd
      (Finset.mem_product.mpr ⟨mem_support_iff.mpr hp, mem_support_iff.mpr hq⟩)
      (Finset.mem_product.mpr ⟨ha, hb⟩) (Finset.mem_antidiagonal.mp hx)
    exact (hne heq).elim
  · intro h
    exact (h (Finset.mem_antidiagonal.mpr rfl)).elim

/-- A product has exactly one output term for each input-term pair if exponent sums are injective. -/
theorem weight_mul_of_injective_support_add (P Q : MvPolynomial σ R)
    (hadd : Set.InjOn (fun ab : (σ →₀ ℕ) × (σ →₀ ℕ) => ab.1 + ab.2)
      (↑(P.support ×ˢ Q.support))) : weight (P * Q) = weight P * weight Q := by
  apply Nat.le_antisymm (weight_mul_le P Q)
  have hsub : (P.support ×ˢ Q.support).image (fun ab => ab.1 + ab.2) ⊆
      (P * Q).support := by
    intro d hd
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    apply mem_support_iff.mpr
    rw [coeff_mul_of_injective_support_add P Q hadd ha hb]
    exact mul_ne_zero (mem_support_iff.mp ha) (mem_support_iff.mp hb)
  calc
    weight P * weight Q = (P.support ×ˢ Q.support).card := (Finset.card_product _ _).symm
    _ = ((P.support ×ˢ Q.support).image (fun ab => ab.1 + ab.2)).card :=
      (Finset.card_image_of_injOn hadd).symm
    _ ≤ (P * Q).support.card := Finset.card_le_card hsub
    _ = weight (P * Q) := rfl

end WeightedPilz

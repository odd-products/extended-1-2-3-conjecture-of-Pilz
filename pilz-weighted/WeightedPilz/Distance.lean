import WeightedPilz.Defs
import Mathlib.Algebra.MvPolynomial.Equiv

/-! The attained minimum over all nonzero multipliers, over an arbitrary field.
The zero polynomial has distance zero by this same definition. -/

noncomputable section

namespace WeightedPilz

variable {σ τ K : Type*} [Field K]

private theorem exists_multiple_weight (P : MvPolynomial σ K) :
    ∃ m : ℕ, ∃ H : MvPolynomial σ K, H ≠ 0 ∧ weight (P * H) = m :=
  ⟨weight P, 1, one_ne_zero, by simp⟩

/-- The support minimum attained by a nonzero multiplier. -/
def distance (P : MvPolynomial σ K) : ℕ := by
  classical
  exact Nat.find (exists_multiple_weight P)

theorem exists_weight_eq_distance (P : MvPolynomial σ K) :
    ∃ H : MvPolynomial σ K, H ≠ 0 ∧ weight (P * H) = distance P := by
  classical
  exact Nat.find_spec (exists_multiple_weight P)

theorem distance_le_weight_mul (P H : MvPolynomial σ K) (hH : H ≠ 0) :
    distance P ≤ weight (P * H) := by
  classical
  exact Nat.find_min' (exists_multiple_weight P) ⟨H, hH, rfl⟩

theorem le_distance_iff (P : MvPolynomial σ K) (k : ℕ) :
    k ≤ distance P ↔ ∀ H : MvPolynomial σ K, H ≠ 0 → k ≤ weight (P * H) := by
  constructor
  · intro hk H hH
    exact hk.trans (distance_le_weight_mul P H hH)
  · intro h
    obtain ⟨H, hH, heq⟩ := exists_weight_eq_distance P
    rw [← heq]
    exact h H hH

theorem distance_le_weight (P : MvPolynomial σ K) : distance P ≤ weight P := by
  simpa using distance_le_weight_mul P 1 one_ne_zero

theorem distance_pos {P : MvPolynomial σ K} (hP : P ≠ 0) : 0 < distance P := by
  obtain ⟨H, hH, heq⟩ := exists_weight_eq_distance P
  rw [← heq]
  simpa [weight, Finset.card_pos, MvPolynomial.support_nonempty] using mul_ne_zero hP hH

@[simp] theorem distance_zero : distance (0 : MvPolynomial σ K) = 0 := by
  have h := distance_le_weight (0 : MvPolynomial σ K)
  simpa [weight] using h

theorem weight_renameEquiv (e : σ ≃ τ) (P : MvPolynomial σ K) :
    weight (MvPolynomial.renameEquiv K e P) = weight P := by
  classical
  rw [weight, MvPolynomial.renameEquiv_apply,
    MvPolynomial.support_rename_of_injective e.injective]
  apply Finset.card_image_iff.mpr
  exact (Finsupp.mapDomain_injective e.injective).injOn

theorem distance_renameEquiv (e : σ ≃ τ) (P : MvPolynomial σ K) :
    distance (MvPolynomial.renameEquiv K e P) = distance P := by
  let E := MvPolynomial.renameEquiv K e
  apply Nat.le_antisymm
  · obtain ⟨H, hH, heq⟩ := exists_weight_eq_distance P
    have hEH : E H ≠ 0 := fun hz => hH (E.injective (by simpa using hz))
    have hle := distance_le_weight_mul (E P) (E H) hEH
    rw [← map_mul, weight_renameEquiv, heq] at hle
    exact hle
  · obtain ⟨H, hH, heq⟩ := exists_weight_eq_distance (E P)
    have hEH : E.symm H ≠ 0 := fun hz => hH (by
      have := congrArg E hz
      simpa using this)
    have hle := distance_le_weight_mul P (E.symm H) hEH
    have hw : weight (P * E.symm H) = weight (E P * H) := by
      have hmap : E (P * E.symm H) = E P * H := by simp only [map_mul, E.apply_symm_apply]
      rw [← hmap]
      exact (weight_renameEquiv e (P * E.symm H)).symm
    rw [hw, heq] at hle
    exact hle

/-- A divisor has no larger minimum support than its nonzero multiples. -/
theorem distance_le_distance_mul (P Q : MvPolynomial σ K) (hQ : Q ≠ 0) :
    distance P ≤ distance (P * Q) := by
  apply (le_distance_iff _ _).mpr
  intro H hH
  simpa only [mul_assoc] using distance_le_weight_mul P (Q * H) (mul_ne_zero hQ hH)

end WeightedPilz

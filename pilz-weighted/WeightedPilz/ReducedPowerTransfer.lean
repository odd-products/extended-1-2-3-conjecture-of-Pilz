import WeightedPilz.FrobeniusBaseExtraction

/-! Extend reduced-exponent support bounds to arbitrary powers while preserving
the coordinate independence required of a multiplier. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ K : Type*} [Field K]

theorem weight_pow_mul_bound_of_reduced (P : MvPolynomial σ K) (hP : P ≠ 0)
    (Z : Set σ) (b : ℕ)
    (hbound : ∀ h : ℕ, 0 < h → (h : K) ≠ 0 → ∀ J : MvPolynomial σ K,
      J ≠ 0 → (∀ z ∈ Z, ∀ d ∈ J.support, d z = 0) → b ≤ weight (P ^ h * J))
    {n : ℕ} (hn : 0 < n) (E : MvPolynomial σ K) (hE : E ≠ 0)
    (hEZ : ∀ z ∈ Z, ∀ d ∈ E.support, d z = 0) : b ≤ weight (P ^ n * E) := by
  obtain ⟨p, hpK⟩ := ExpChar.exists K
  cases hpK with
  | zero => exact hbound n hn (Nat.cast_ne_zero.mpr (ne_of_gt hn)) E hE hEZ
  | prime hp =>
    letI : ExpChar K p := ExpChar.prime hp
    obtain ⟨e, h, hnp, hfactor⟩ := Nat.exists_eq_pow_mul_and_not_dvd (ne_of_gt hn) p hp.ne_one
    have hh : 0 < h := by
      by_contra hz
      have hz' : h = 0 := by omega
      simp [hz'] at hfactor
      omega
    have hhK : (h : K) ≠ 0 := fun hz => hnp ((CharP.cast_eq_zero_iff K p h).mp hz)
    obtain ⟨J, hJ, _, hJZ, hwt⟩ := frobenius_extraction_preserving_zero_coordinates
      p e (P ^ h) E Z (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hP)) hE) hEZ
    rw [hfactor, Nat.mul_comm, pow_mul]
    exact (hbound h hh hhK J hJ hJZ).trans hwt

end WeightedPilz

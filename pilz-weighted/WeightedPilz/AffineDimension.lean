import WeightedPilz.DirectionalWidth
import WeightedPilz.AffineSupportCard
import WeightedPilz.Distance
import WeightedPilz.Laurent
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Linarith

/-! Multiplication cannot decrease the rational affine dimension of support. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ K : Type*} [Field K] [DecidableEq σ]

theorem affineDifferenceSpan_mul_left (P Q : MvPolynomial σ K)
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    affineDifferenceSpan P ≤ affineDifferenceSpan (P * Q) := by
  apply Subspace.dualAnnihilator_le_dualAnnihilator_iff.mp
  intro f hf
  let v : (σ →₀ ℕ) →+ ℚ := f.toAddMonoidHom.comp rationalExponent
  have hconst : ∀ a ∈ (P * Q).support, ∀ b ∈ (P * Q).support, v a = v b := by
    intro a ha b hb
    have hmem : rationalExponent a - rationalExponent b ∈ affineDifferenceSpan (P * Q) :=
      Submodule.subset_span ⟨a, ha, b, hb, rfl⟩
    have hz := (Submodule.mem_dualAnnihilator f).mp hf _ hmem
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  have hzero : directionalWidth v (P * Q) = 0 :=
    (directionalWidth_eq_zero_iff v (P * Q) (mul_ne_zero hP hQ)).mpr hconst
  have hzeroP : directionalWidth v P = 0 := by
    rw [directionalWidth_mul v P Q hP hQ] at hzero
    have hp := directionalWidth_nonneg v P
    have hq := directionalWidth_nonneg v Q
    linarith
  have hconstP := (directionalWidth_eq_zero_iff v P hP).mp hzeroP
  apply (Submodule.mem_dualAnnihilator f).mpr
  have hker : affineDifferenceSpan P ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro x ⟨a, ha, b, hb, rfl⟩
    change f (rationalExponent a - rationalExponent b) = 0
    rw [map_sub, sub_eq_zero]
    exact hconstP a ha b hb
  intro x hx
  exact hker hx

theorem affineDifferenceSpan_mul_right (P Q : MvPolynomial σ K)
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    affineDifferenceSpan Q ≤ affineDifferenceSpan (P * Q) := by
  rw [mul_comm]
  exact affineDifferenceSpan_mul_left Q P hQ hP

theorem affineDimension_le_mul (P Q : MvPolynomial σ K) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    affineDimension P ≤ affineDimension (P * Q) :=
  Submodule.finrank_mono (affineDifferenceSpan_mul_left P Q hP hQ)

/-- Every nonzero multiple has at least one more term than the rational
affine dimension of the original polynomial support. -/
theorem affineDimension_add_one_le_weight_mul (P Q : MvPolynomial σ K)
    (hP : P ≠ 0) (hQ : Q ≠ 0) : affineDimension P + 1 ≤ weight (P * Q) :=
  (Nat.add_le_add_right (affineDimension_le_mul P Q hP hQ) 1).trans
    (affineDimension_add_one_le_weight (P * Q) (mul_ne_zero hP hQ))

theorem affineDimension_add_one_le_distance (P : MvPolynomial σ K) (hP : P ≠ 0) :
    affineDimension P + 1 ≤ distance P := by
  apply (le_distance_iff P _).mpr
  intro Q hQ
  exact affineDimension_add_one_le_weight_mul P Q hP hQ

theorem affineDimension_add_one_le_laurent_weight (P : MvPolynomial σ K) (hP : P ≠ 0)
    (H : LaurentPoly σ K) (hH : H ≠ 0) :
    affineDimension P + 1 ≤ (toLaurent P * H).support.card :=
  laurent_bound_of_polynomial_bound P (affineDimension P + 1)
    (fun Q hQ => affineDimension_add_one_le_weight_mul P Q hP hQ) H hH

end WeightedPilz

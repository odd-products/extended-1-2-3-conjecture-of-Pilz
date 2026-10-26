import WeightedPilz.InitialSixteenQuadratic
import WeightedPilz.BivariateQuadraticRatio
import WeightedPilz.RationalNonconstant

/-! The complete four-term bound for the exceptional quadratic base at sixteen. -/
noncomputable section
namespace WeightedPilz
open Polynomial
variable {K : Type*} [Field K]

theorem initial_sixteen_base_distance (A B : K[X]) (d : K)
    (hA0 : A.coeff 0 ≠ 0) (hA1 : A.coeff 1 ≠ 0)
    (hB0 : B.coeff 0 ≠ 0) (hB1 : B.coeff 1 ≠ 0)
    (hBdeg : 2 ≤ B.natDegree) (hd : d ≠ 0) :
    4 ≤ distance (bivariateQuadratic A B (C d)) := by
  have hA : A ≠ 0 := fun hz => hA0 (by rw [hz, coeff_zero])
  have hB : B ≠ 0 := fun hz => hB0 (by rw [hz, coeff_zero])
  by_cases hconstant : ∃ a : K, A = C a * B ^ 2
  · obtain ⟨a, rfl⟩ := hconstant
    have ha : a ≠ 0 := by
      intro hz
      apply hA
      simp [hz]
    exact scalar_square_quadratic_distance_four B a d ha hd hB0 hB1 hBdeg
  · have hnot : ∀ a : K, A * C d ≠ C a * B ^ 2 := by
      intro a heq
      apply hconstant
      refine ⟨a / d, ?_⟩
      apply mul_right_cancel₀ (C_ne_zero.mpr hd)
      calc
        A * C d = C a * B ^ 2 := heq
        _ = (C (a / d) * C d) * B ^ 2 := by
          rw [← map_mul, div_mul_cancel₀ a hd]
        _ = (C (a / d) * B ^ 2) * C d := by ring
    have hratio := rational_ratio_transcendental_of_not_constant (A * C d) (B ^ 2)
      (pow_ne_zero 2 hB) hnot
    simp only [map_mul, map_pow] at hratio
    exact bivariateQuadratic_distance_four_of_ratio A B (C d) hA0 hA1 hB
      (C_ne_zero.mpr hd) hratio

end WeightedPilz

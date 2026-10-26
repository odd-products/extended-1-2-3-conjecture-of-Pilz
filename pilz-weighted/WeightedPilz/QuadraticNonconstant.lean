import WeightedPilz.BivariateQuadraticRatio
import WeightedPilz.RationalNonconstant

/-! The literal nonconstant-ratio form of the initial quadratic obstruction. -/
noncomputable section
namespace WeightedPilz
open Polynomial

/-- `lem:initial-quadratic`. For nonzero A,B,D, the displayed hypothesis says
exactly that B²/(AD) is not a constant rational function. -/
theorem quadratic_polynomial_multiple_three_rows_of_nonconstant
    {K : Type*} [Field K] (A B D : K[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0)
    (hconstant : ∀ a : K, B ^ 2 ≠ C a * (A * D))
    (G : Polynomial K[X]) (hG : G ≠ 0)
    (hdiv : (C A + C B * X + C D * X ^ 2 : Polynomial K[X]) ∣ G) :
    3 ≤ G.support.card := by
  have htrans := rational_ratio_transcendental_of_not_constant (B ^ 2) (A * D)
    (mul_ne_zero hA hD) hconstant
  apply quadratic_polynomial_multiple_three_rows_of_ratio A B D hA hB hD ?_ G hG hdiv
  intro halg
  apply htrans
  simpa only [map_pow, map_mul, inv_div] using halg.inv

end WeightedPilz

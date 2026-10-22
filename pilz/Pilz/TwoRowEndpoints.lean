import Pilz.TwoRowGeneral
import Pilz.Endpoints3

/-! The general two-row obstruction joined to the endpoint distance bound. -/

noncomputable section

namespace Pilz

theorem top_three_endpoint_distance {σ : Type*} [DecidableEq σ] (p : σ)
    (P : MvPolynomial σ (ZMod 2))
    (hd : 2 ≤ (coordinateEquiv p P).natDegree)
    (h0 : (coordinateEquiv p P).coeff 0 ≠ 0)
    (hlow : (coordinateEquiv p P).coeff ((coordinateEquiv p P).natDegree - 2) ≠ 0)
    (hmid : (coordinateEquiv p P).coeff ((coordinateEquiv p P).natDegree - 1) ≠ 0)
    (hobs : (coordinateEquiv p P).coeff ((coordinateEquiv p P).natDegree - 2) *
        (coordinateEquiv p P).leadingCoeff ≠
      (coordinateEquiv p P).coeff ((coordinateEquiv p P).natDegree - 1) ^ 2) :
    distance ((coordinateEquiv p P).coeff 0) +
      distance ((coordinateEquiv p P).coeff (coordinateEquiv p P).natDegree) + 1 ≤ distance P := by
  have htrail : (coordinateEquiv p P).natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr h0)
  have hspan : (coordinateEquiv p P).natTrailingDegree < (coordinateEquiv p P).natDegree := by
    omega
  have hend := endpoint_distance_three p P hspan (by
    intro H hH
    rw [map_mul]
    exact TwoRow.top_three_le_rows (coordinateEquiv p P) hd h0 hlow hmid hobs
      (coordinateEquiv p H) (coordinateEquiv_ne_zero p hH))
  simpa only [Polynomial.trailingCoeff, htrail, Polynomial.leadingCoeff] using hend

end Pilz

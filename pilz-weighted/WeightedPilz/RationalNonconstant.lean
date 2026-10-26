import WeightedPilz.RationalTranscendence
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic.FieldSimp

/-! Every nonconstant rational function is transcendental over its constants. -/

noncomputable section
namespace WeightedPilz
open Polynomial
variable {K : Type*} [Field K]

theorem rational_ratio_transcendental_of_not_constant (A B : K[X]) (hB : B ≠ 0)
    (hconstant : ∀ a : K, A ≠ C a * B) :
    Transcendental K (algebraMap K[X] (RatFunc K) A /
      algebraMap K[X] (RatFunc K) B) := by
  have hA : A ≠ 0 := by simpa using hconstant 0
  by_cases hdeg : A.natDegree = B.natDegree
  · let a := A.leadingCoeff / B.leadingCoeff
    have ha : a ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hA) (leadingCoeff_ne_zero.mpr hB)
    let E := A - C a * B
    have hE : E ≠ 0 := sub_ne_zero.mpr (hconstant a)
    have hCB : C a * B ≠ 0 := mul_ne_zero (C_ne_zero.mpr ha) hB
    have hdegCB : (C a * B).degree = A.degree := by
      rw [degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr ha),
        degree_eq_natDegree hA, degree_eq_natDegree hB, hdeg]
    have hlead : (C a * B).leadingCoeff = A.leadingCoeff := by
      rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr ha)]
      exact div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr hB)
    have hlt : E.degree < A.degree := degree_sub_lt hdegCB.symm hA hlead.symm
    have hnat : E.natDegree < B.natDegree := by
      rw [degree_eq_natDegree hE, degree_eq_natDegree hA] at hlt
      exact hdeg ▸ WithBot.coe_lt_coe.mp hlt
    have htrans := rational_ratio_transcendental E B hE hB (Nat.ne_of_lt hnat)
    intro halg
    have hsub := halg.sub (isAlgebraic_algebraMap (A := RatFunc K) a)
    apply htrans
    convert hsub using 1
    dsimp [E]
    rw [map_sub, map_mul]
    change (_ - algebraMap K (RatFunc K) a * _) / _ = _
    field_simp [RatFunc.algebraMap_ne_zero hB]
    change _ - RatFunc.C a * _ = _
    ring
  · exact rational_ratio_transcendental A B hA hB hdeg

end WeightedPilz

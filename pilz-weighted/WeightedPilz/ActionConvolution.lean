import WeightedPilz.ModuleActions
import WeightedPilz.Convolution

/-! The scalar specialization of the finite interval endomorphism action agrees
with multiplication by the arithmetic interval kernel. -/

namespace WeightedPilz

theorem intervalEndAction_scalar_eq_convolution {K : Type*} [CommSemiring K]
    (n : ℕ) (c : ℕ → K) (f : ArithmeticFunction K) :
    intervalEndAction n (fun a => scalarWeightEnd (c a)) f = arithmeticKernel n c * f := by
  ext m
  rw [intervalScalarAction_apply, interval_convolution_apply]
  rfl

/-- The polynomial and endomorphism formulations of the scalar interval bound
are equivalent over every field. -/
theorem intervalEndBound_scalar_iff_intervalBound {K : Type*} [Field K]
    (n : ℕ) (c : ℕ → K) :
    IntervalEndBound (M := K) n (fun a => scalarWeightEnd (c a)) ↔ IntervalBound n c := by
  rw [intervalBound_iff_convolution_bound]
  simp only [IntervalEndBound, intervalEndAction_scalar_eq_convolution]
  rfl

end WeightedPilz

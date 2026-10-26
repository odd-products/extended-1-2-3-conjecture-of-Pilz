import WeightedPilz.FreshCompletion
import WeightedPilz.Rescale

/-! A nonzero coefficient on a fresh variable does not change the sharp bound. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ K : Type*} [DecidableEq σ] [Field K]

theorem weighted_sharp_completion_coordinate (P : MvPolynomial σ K) (p : σ)
    (hP : P ≠ 0) (hind : ∀ d ∈ P.support, d p = 0) (a : K) (ha : a ≠ 0) :
    min (weight P + 1) (distance P + 2) ≤ distance (P + C a * X p) := by
  classical
  let u : σ → Kˣ := fun q => if q = p then (Units.mk0 a ha)⁻¹ else 1
  have hterm : rescale u (C a * X p) = X p := by
    rw [map_mul, rescale_C, rescale_X, ← mul_assoc, ← map_mul]
    simp [u, ha]
  have hRP : rescale u P ≠ 0 := by simpa using hP
  have hRind : ∀ d ∈ (rescale u P).support, d p = 0 := by
    simpa only [support_rescale] using hind
  have h := sharp_completion_coordinate (rescale u P) p hRP hRind
  rw [weight_rescale, distance_rescale] at h
  rw [← distance_rescale u (P + C a * X p), map_add, hterm]
  exact h

end WeightedPilz

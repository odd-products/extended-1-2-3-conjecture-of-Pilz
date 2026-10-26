import WeightedPilz.IntervalFresh
import WeightedPilz.ResidueCapacity

/-! Transfer arbitrary-input comparisons to the normalized fresh kernel. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K]

def intervalUnnormalize (n : ℕ) (c : ℕ → K) (hc : NonzeroWeights n c) (D : Poly K) : Poly K :=
  rescale (fun p => (intervalFreshNormalization n c hc p)⁻¹) D

theorem support_intervalUnnormalize (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (D : Poly K) :
    (intervalUnnormalize n c hc D).support = D.support := support_rescale _ _

theorem weight_intervalUnnormalize (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (D : Poly K) :
    weight (intervalUnnormalize n c hc D) = weight D := weight_rescale _ _

theorem intervalUnnormalize_ne_zero (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (D : Poly K) (hD : D ≠ 0) :
    intervalUnnormalize n c hc D ≠ 0 := by
  exact (rescale_eq_zero _ D).not.mpr hD

theorem residueWeight_intervalUnnormalize (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (D : Poly K) (q : ℕ) (α : ℕ →₀ ℕ) :
    residueWeight q (intervalUnnormalize n c hc D) α = residueWeight q D α := by
  classical
  simp only [residueWeight, weight, support_residuePart, support_intervalUnnormalize]

theorem intervalFreshData_mul_unnormalize (n : ℕ) (c : ℕ → K) (hn : 0 < n)
    (hc : NonzeroWeights n c) (hr : (intervalFreshPrimes n).Nonempty) (D : Poly K) :
    weight ((intervalFreshData n c hn hc hr).F * D) =
      weight (interval n c * intervalUnnormalize n c hc D) := by
  have hF : (intervalFreshData n c hn hc hr).F =
      rescale (intervalFreshNormalization n c hc) (interval n c) :=
    (rescale_interval_eq_core_add_fresh n c hc).symm
  rw [← weight_rescale (fun p => (intervalFreshNormalization n c hc p)⁻¹)
    ((intervalFreshData n c hn hc hr).F * D), map_mul, hF, rescale_inv_rescale]
  rfl

theorem residueWeight_core_mul_unnormalize (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (D : Poly K) (q : ℕ) (α : ℕ →₀ ℕ) :
    residueWeight q (intervalCore n c * intervalUnnormalize n c hc D) α =
      residueWeight q (intervalCore n c * D) α := by
  classical
  have hcore : rescale (fun p => (intervalFreshNormalization n c hc p)⁻¹)
      (intervalCore n c) = intervalCore n c := by
    have h := rescale_inv_rescale (intervalFreshNormalization n c hc) (intervalCore n c)
    rwa [rescale_intervalCore n c hc] at h
  have heq : intervalCore n c * intervalUnnormalize n c hc D =
      intervalUnnormalize n c hc (intervalCore n c * D) := by
    simp only [intervalUnnormalize, map_mul, hcore]
  rw [heq, residueWeight_intervalUnnormalize]

end WeightedPilz

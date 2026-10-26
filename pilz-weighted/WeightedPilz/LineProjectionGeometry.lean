import WeightedPilz.BinomialLines
import WeightedPilz.AffineSupportCard
import Mathlib.Tactic.FieldSimp

/-! The integer cross-product projection used to count binomial lines has
exactly the rational affine lines as its fibers. -/

noncomputable section
namespace WeightedPilz

variable {σ : Type*}

/-- Equality of projected exponents is precisely rational parallelism with
the binomial displacement. No subtraction in natural exponents is used. -/
theorem binomialLineProjection_eq_iff (a b d e : σ →₀ ℕ) (j : σ)
    (hj : a j ≠ b j) :
    binomialLineProjection a b j d = binomialLineProjection a b j e ↔
      ∃ t : ℚ, rationalExponent d - rationalExponent e =
        t • (rationalExponent b - rationalExponent a) := by
  have hden : (b j : ℚ) - a j ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hj.symm
  constructor
  · intro h
    refine ⟨((d j : ℚ) - e j) / ((b j : ℚ) - a j), ?_⟩
    ext k
    have hk := congrFun h k
    change ((b j : ℤ) - a j) * d k - (d j : ℤ) * ((b k : ℤ) - a k) =
      ((b j : ℤ) - a j) * e k - (e j : ℤ) * ((b k : ℤ) - a k) at hk
    have hkq : ((b j : ℚ) - a j) * d k - (d j : ℚ) * ((b k : ℚ) - a k) =
        ((b j : ℚ) - a j) * e k - (e j : ℚ) * ((b k : ℚ) - a k) := by
      exact_mod_cast hk
    simp only [Finsupp.sub_apply, Finsupp.smul_apply, rationalExponent_apply,
      smul_eq_mul]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hden).2
    nlinarith only [hkq]
  · rintro ⟨t, ht⟩
    have hcoord (k : σ) : (d k : ℚ) - e k = t * ((b k : ℚ) - a k) := by
      simpa only [Finsupp.sub_apply, Finsupp.smul_apply, rationalExponent_apply,
        smul_eq_mul] using congrArg (fun v : σ →₀ ℚ => v k) ht
    ext k
    change ((b j : ℤ) - a j) * d k - (d j : ℤ) * ((b k : ℤ) - a k) =
      ((b j : ℤ) - a j) * e k - (e j : ℤ) * ((b k : ℤ) - a k)
    have hq : ((b j : ℚ) - a j) * d k - (d j : ℚ) * ((b k : ℚ) - a k) =
        ((b j : ℚ) - a j) * e k - (e j : ℚ) * ((b k : ℚ) - a k) := by
      calc
        _ = ((b j : ℚ) - a j) * e k - (e j : ℚ) * ((b k : ℚ) - a k) +
            (((b j : ℚ) - a j) * ((d k : ℚ) - e k) -
              ((d j : ℚ) - e j) * ((b k : ℚ) - a k)) := by ring
        _ = _ := by rw [hcoord k, hcoord j]; ring
    exact_mod_cast hq

/-- Every nonzero binomial displacement has a coordinate projection with
the exact affine-line fibers used in the endpoint counting theorem. -/
theorem exists_binomialLineProjection (a b : σ →₀ ℕ) (hab : a ≠ b) :
    ∃ j : σ, a j ≠ b j ∧ ∀ d e : σ →₀ ℕ,
      binomialLineProjection a b j d = binomialLineProjection a b j e ↔
        ∃ t : ℚ, rationalExponent d - rationalExponent e =
          t • (rationalExponent b - rationalExponent a) := by
  have hex : ∃ j, a j ≠ b j := by
    by_contra! h
    exact hab (Finsupp.ext h)
  obtain ⟨j, hj⟩ := hex
  exact ⟨j, hj, fun d e => binomialLineProjection_eq_iff a b d e j hj⟩

end WeightedPilz

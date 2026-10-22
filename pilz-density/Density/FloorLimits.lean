import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semifield

/-! Exact analytic limits needed for the odd-product density formula.
No existence-of-density hypothesis is used in the floor-sum convergence theorem.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace PilzDensity

/-- The natural quotient `(n*a)/b`, divided by `n`, tends to `a/b`.
The zero-denominator convention is harmless; applications use positive `b`. -/
theorem tendsto_nat_mul_div_ratio (a b : ℕ) :
    Tendsto (fun n : ℕ => ((n * a / b : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 ((a : ℝ) / (b : ℝ))) := by
  have h := (tendsto_nat_floor_mul_div_atTop
    (a := (a : ℝ) / (b : ℝ)) (by positivity)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  convert h using 1
  funext n
  congr 1
  rw [div_mul_eq_mul_div, mul_comm (a : ℝ) (n : ℝ), ← Nat.cast_mul,
    Nat.floor_div_natCast, Nat.floor_natCast]

/-- Every finite real linear combination of natural floor terms has the
expected density. This includes the signed inclusion-exclusion formula. -/
theorem tendsto_finite_floor_sum {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (a b : ι → ℕ) :
    Tendsto (fun n : ℕ =>
      (∑ i ∈ s, c i * ((n * a i / b i : ℕ) : ℝ)) / (n : ℝ))
      atTop (𝓝 (∑ i ∈ s, c i * ((a i : ℝ) / (b i : ℝ)))) := by
  have hi (i : ι) :
      Tendsto (fun n : ℕ => c i * (((n * a i / b i : ℕ) : ℝ) / (n : ℝ)))
        atTop (𝓝 (c i * ((a i : ℝ) / (b i : ℝ)))) :=
    tendsto_const_nhds.mul (tendsto_nat_mul_div_ratio (a i) (b i))
  have h := tendsto_finset_sum s (fun i _ => hi i)
  convert h using 1
  funext n
  simp only [div_eq_mul_inv, Finset.sum_mul, mul_assoc]

/-- Rescaling the input by a positive natural divisor rescales the density
by its reciprocal. The sequence itself need not be nonnegative. -/
theorem tendsto_div_index {f : ℕ → ℝ} {d : ℝ}
    (hf : Tendsto (fun n : ℕ => f n / (n : ℝ)) atTop (𝓝 d))
    (Q : ℕ) (hQ : 0 < Q) :
    Tendsto (fun n : ℕ => f (n / Q) / (n : ℝ))
      atTop (𝓝 (d / (Q : ℝ))) := by
  have hfirst := hf.comp (Nat.tendsto_div_const_atTop (ne_of_gt hQ))
  have hsecond : Tendsto (fun n : ℕ => ((n / Q : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 (1 / (Q : ℝ))) := by
    simpa using tendsto_nat_mul_div_ratio 1 Q
  have hprod := hfirst.mul hsecond
  have heq : (fun n : ℕ =>
      (f (n / Q) / ((n / Q : ℕ) : ℝ)) *
        (((n / Q : ℕ) : ℝ) / (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ => f (n / Q) / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop Q] with n hn
    have hpos : 0 < n / Q := Nat.div_pos hn hQ
    have hne : ((n / Q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
    field_simp
  simpa only [mul_one_div] using hprod.congr' heq

end PilzDensity


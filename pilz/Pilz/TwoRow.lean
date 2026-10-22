import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.FinCases
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The quadratic two-row obstruction

The paper's algebraic-constant argument is proved by integral closure and
polynomial units. The root-ratio argument then shows that a quadratic
dividing a binomial must satisfy `a₀ * a₂ = a₁²`. Consequently a failed
identity forces at least three occupied rows in every nonzero multiple.
The arbitrary-degree version is developed in `TwoRowGeneral`.
-/

noncomputable section

namespace Pilz.TwoRowConstants

variable {σ K : Type*} [Field K]

/-- A nonzero algebraic rational function over a field is a nonzero constant. -/
theorem algebraic_fraction_constant (u : FractionRing (MvPolynomial σ K))
    (hu : IsAlgebraic K u) (hne : u ≠ 0) :
    ∃ c : K, IsUnit c ∧ algebraMap K (FractionRing (MvPolynomial σ K)) c = u := by
  have hI : IsIntegral (MvPolynomial σ K) u := hu.isIntegral.tower_top
  have hInv : IsIntegral (MvPolynomial σ K) u⁻¹ := hu.inv.isIntegral.tower_top
  obtain ⟨P, hP⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hI
  obtain ⟨Q, hQ⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hInv
  have hPQ : P * Q = 1 := by
    apply IsFractionRing.injective (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
    rw [map_mul, map_one, hP, hQ, mul_inv_cancel₀ hne]
  have hunit : IsUnit P := isUnit_of_mul_eq_one P Q hPQ
  obtain ⟨c, hc, hPC⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hunit
  refine ⟨c, hc, ?_⟩
  rw [← hP, hPC]
  exact (IsScalarTower.algebraMap_apply K (MvPolynomial σ K)
    (FractionRing (MvPolynomial σ K)) c).symm

/-- The full relative algebraic-closedness statement, including zero. -/
theorem algebraic_fraction_in_constants (u : FractionRing (MvPolynomial σ K))
    (hu : IsAlgebraic K u) :
    ∃ c : K, algebraMap K (FractionRing (MvPolynomial σ K)) c = u := by
  by_cases hne : u = 0
  · exact ⟨0, by simp [hne]⟩
  · obtain ⟨c, _hc, heq⟩ := algebraic_fraction_constant u hu hne
    exact ⟨c, heq⟩

/-- Over F₂ the only nonzero algebraic rational function is one. This is
the exact conclusion required for the quotient of coefficient powers. -/
theorem algebraic_fraction_eq_one (u : FractionRing (MvPolynomial σ (ZMod 2)))
    (hu : IsAlgebraic (ZMod 2) u) (hne : u ≠ 0) : u = 1 := by
  obtain ⟨c, hc, heq⟩ := algebraic_fraction_constant u hu hne
  have hc1 : c = 1 := by
    have hc0 : c ≠ 0 := hc.ne_zero
    fin_cases c <;> simp_all
  rw [hc1, map_one] at heq
  exact heq.symm

end Pilz.TwoRowConstants


namespace Pilz.TwoRow

open Polynomial

variable {K : Type*} [Field K] [CharP K 2]

/-- The quadratic row polynomial, written in descending order. -/
def quadratic {R : Type*} [Semiring R] (a b c : R) : R[X] :=
  C c * X ^ 2 + C b * X + C a

/-- In characteristic two a quadratic has two (possibly equal) nonzero roots
with the usual sum and product whenever its endpoint coefficients are nonzero. -/
theorem quadratic_root_pair [IsAlgClosed K] (a b c : K)
    (ha : a ≠ 0) (hc : c ≠ 0) :
    ∃ α β : K, α ≠ 0 ∧ β ≠ 0 ∧
      eval α (quadratic a b c) = 0 ∧ eval β (quadratic a b c) = 0 ∧
      α + β = b / c ∧ α * β = a / c := by
  have hdeg : (quadratic a b c).degree ≠ 0 := by
    rw [quadratic, degree_quadratic hc]
    decide
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (quadratic a b c) hdeg
  have hαeq : c * α ^ 2 + b * α + a = 0 := by
    simpa [Polynomial.IsRoot, quadratic] using hα
  have hα0 : α ≠ 0 := by
    intro h
    simp [h, ha] at hαeq
  let β := α + b / c
  have hscale : c * (b / c) ^ 2 = b * (b / c) := by
    field_simp
  have hβeq : c * β ^ 2 + b * β + a = 0 := by
    dsimp [β]
    calc
      _ = (c * α ^ 2 + b * α + a) +
          (c * (b / c) ^ 2 + b * (b / c)) := by
        rw [CharTwo.add_sq]
        ring
      _ = 0 := by rw [hαeq, hscale, CharTwo.add_self_eq_zero, add_zero]
  have hβ0 : β ≠ 0 := by
    intro h
    simp [h, ha] at hβeq
  refine ⟨α, β, hα0, hβ0, ?_, ?_, ?_, ?_⟩
  · simpa [quadratic] using hαeq
  · simpa [quadratic] using hβeq
  · dsimp [β]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · have hp : c * (α * β) + a = 0 := by
      calc
        _ = c * α ^ 2 + b * α + a := by
          dsimp [β]
          field_simp
        _ = 0 := hαeq
    apply (eq_div_iff hc).mpr
    simpa [mul_comm] using CharTwo.add_eq_zero.mp hp

/-- Evaluating the same binomial at two nonzero roots forces an equal positive
power of those roots. The exponents need not start at zero. -/
theorem equal_pow_of_binomial_roots (α β b₀ b₁ : K) (u v : ℕ)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hb₁ : b₁ ≠ 0) (huv : u < v)
    (ha : b₀ * α ^ u + b₁ * α ^ v = 0)
    (hb : b₀ * β ^ u + b₁ * β ^ v = 0) :
    α ^ (v - u) = β ^ (v - u) := by
  have hv : v = u + (v - u) := by omega
  have hfactor (x : K) (hx : x ≠ 0)
      (heval : b₀ * x ^ u + b₁ * x ^ v = 0) :
      b₀ + b₁ * x ^ (v - u) = 0 := by
    apply (mul_eq_zero.mp (show x ^ u * (b₀ + b₁ * x ^ (v - u)) = 0 from ?_)).resolve_left
      (pow_ne_zero u hx)
    calc
      _ = b₀ * x ^ u + b₁ * x ^ v := by
        have hp : x ^ v = x ^ u * x ^ (v - u) := by
          calc
            x ^ v = x ^ (u + (v - u)) := congrArg (fun n => x ^ n) hv
            _ = x ^ u * x ^ (v - u) := pow_add _ _ _
        rw [hp]
        ring
      _ = 0 := heval
  apply mul_left_cancel₀ hb₁
  exact (CharTwo.add_eq_zero.mp (hfactor α hα ha)).symm.trans
    (CharTwo.add_eq_zero.mp (hfactor β hβ hb))

omit [CharP K 2] in
/-- A quotient of roots with the same positive power is algebraic over F₂. -/
theorem root_ratio_algebraic [Algebra (ZMod 2) K] (α β : K) (h : ℕ)
    (hβ : β ≠ 0) (hh : 0 < h) (heq : α ^ h = β ^ h) :
    IsAlgebraic (ZMod 2) (α / β) := by
  apply IsAlgebraic.of_pow hh
  have hp : (α / β) ^ h = 1 := by
    rw [div_pow, heq, div_self (pow_ne_zero h hβ)]
  rw [hp]
  exact isAlgebraic_one

/-- The symmetric quotient of two roots expresses the quadratic obstruction. -/
theorem quadratic_ratio_eq (a b c α β : K)
    (ha : a ≠ 0) (hc : c ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hsum : α + β = b / c) (hprod : α * β = a / c) :
    b ^ 2 / (a * c) = α / β + β / α := by
  calc
    _ = (b / c) ^ 2 / (a / c) := by field_simp
    _ = (α + β) ^ 2 / (α * β) := by rw [hsum, hprod]
    _ = α / β + β / α := by rw [CharTwo.add_sq]; field_simp

/-- The quadratic coefficient quotient is algebraic over F₂ if the quadratic
divides a binomial. This is the root-ratio argument from the paper. -/
theorem quadratic_binomial_ratio_algebraic [Algebra (ZMod 2) K]
    (a b c b₀ b₁ : K) (u v : ℕ)
    (ha : a ≠ 0) (hc : c ≠ 0) (hb₁ : b₁ ≠ 0) (huv : u < v)
    (hdiv : quadratic a b c ∣ monomial u b₀ + monomial v b₁) :
    IsAlgebraic (ZMod 2) (b ^ 2 / (a * c)) := by
  let Ω := AlgebraicClosure K
  let f := algebraMap K Ω
  have hf : Function.Injective f := RingHom.injective f
  have hA : f a ≠ 0 := fun hz => ha (hf (by simpa using hz))
  have hC : f c ≠ 0 := fun hz => hc (hf (by simpa using hz))
  have hB₁ : f b₁ ≠ 0 := fun hz => hb₁ (hf (by simpa using hz))
  obtain ⟨α, β, hα, hβ, hαroot, hβroot, hsum, hprod⟩ :=
    quadratic_root_pair (f a) (f b) (f c) hA hC
  have hdiv' : quadratic (f a) (f b) (f c) ∣
      monomial u (f b₀) + monomial v (f b₁) := by
    simpa [quadratic] using Polynomial.map_dvd f hdiv
  have hαeval : f b₀ * α ^ u + f b₁ * α ^ v = 0 := by
    simpa using eval_eq_zero_of_dvd_of_eval_eq_zero hdiv' hαroot
  have hβeval : f b₀ * β ^ u + f b₁ * β ^ v = 0 := by
    simpa using eval_eq_zero_of_dvd_of_eval_eq_zero hdiv' hβroot
  have hp := equal_pow_of_binomial_roots α β (f b₀) (f b₁) u v
    hα hβ hB₁ huv hαeval hβeval
  have halg := root_ratio_algebraic α β (v - u) hβ (by omega) hp
  have hinv : IsAlgebraic (ZMod 2) (β / α) := by
    simpa only [inv_div] using halg.inv
  have hquot : IsAlgebraic (ZMod 2) (f (b ^ 2 / (a * c))) := by
    simp only [map_div₀, map_pow, map_mul]
    rw [quadratic_ratio_eq (f a) (f b) (f c) α β hA hC hα hβ hsum hprod]
    exact halg.add hinv
  exact (isAlgebraic_algebraMap_iff (R := ZMod 2) hf).mp hquot

/-- The quadratic instance of the paper's two-row obstruction over the
fraction field of a multivariate F₂-polynomial ring. -/
theorem quadratic_binomial_identity {σ : Type*}
    (a b c b₀ b₁ : FractionRing (MvPolynomial σ (ZMod 2))) (u v : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hb₁ : b₁ ≠ 0) (huv : u < v)
    (hdiv : quadratic a b c ∣ monomial u b₀ + monomial v b₁) :
    a * c = b ^ 2 := by
  letI : CharP (FractionRing (MvPolynomial σ (ZMod 2))) 2 :=
    IsFractionRing.charP_of_isFractionRing (MvPolynomial σ (ZMod 2)) 2
  have halg := quadratic_binomial_ratio_algebraic a b c b₀ b₁ u v ha hc hb₁ huv hdiv
  have hne : b ^ 2 / (a * c) ≠ 0 := div_ne_zero (pow_ne_zero 2 hb) (mul_ne_zero ha hc)
  have heq := TwoRowConstants.algebraic_fraction_eq_one _ halg hne
  exact ((div_eq_one_iff_eq (mul_ne_zero ha hc)).mp heq).symm

/-- A polynomial with one or two occupied rows gives a binomial multiple.
Multiplication by X handles the single occupied row. -/
theorem exists_binomial_multiple_of_support_le_two {R : Type*} [Semiring R]
    (P Q : R[X]) (hQ : Q ≠ 0) (hdiv : P ∣ Q) (hcard : Q.support.card ≤ 2) :
    ∃ (u v : ℕ) (b₀ b₁ : R), u < v ∧ b₁ ≠ 0 ∧
      P ∣ monomial u b₀ + monomial v b₁ := by
  by_cases hcard1 : Q.support.card ≤ 1
  · obtain ⟨k, x, hQeq⟩ := card_support_le_one_iff_monomial.mp hcard1
    have hx : x ≠ 0 := by
      intro hx
      apply hQ
      simpa [hx] using hQeq
    refine ⟨0, k + 1, 0, x, by omega, hx, ?_⟩
    have hd : P ∣ monomial k x := hQeq ▸ hdiv
    simpa only [map_zero, zero_add, monomial_mul_X] using
      dvd_mul_of_dvd_left hd (X : R[X])
  · have htwo : Q.support.card = 2 := by omega
    obtain ⟨u, v, huv, b₀, b₁, _hb₀, hb₁, hQeq⟩ := card_support_eq_two.mp htwo
    refine ⟨u, v, b₀, b₁, huv, hb₁, ?_⟩
    rw [hQeq] at hdiv
    simpa only [C_mul_X_pow_eq_monomial] using hdiv

/-- A quadratic with a failed coefficient identity forces at least three
occupied rows in every nonzero polynomial multiple. -/
theorem quadratic_three_le_rows {σ : Type*}
    (a b c : MvPolynomial σ (ZMod 2))
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hobs : a * c ≠ b ^ 2)
    (H : (MvPolynomial σ (ZMod 2))[X]) (hH : H ≠ 0) :
    3 ≤ (quadratic a b c * H).support.card := by
  let R := MvPolynomial σ (ZMod 2)
  let K := FractionRing R
  let f := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  have hq : quadratic a b c ≠ 0 := by
    intro hz
    have hc0 := congrArg (fun P => Polynomial.coeff P 2) hz
    apply hc
    simpa [quadratic] using hc0
  have hQ := mul_ne_zero hq hH
  by_contra hcard
  obtain ⟨u, v, b₀, b₁, huv, hb₁, hdiv⟩ :=
    exists_binomial_multiple_of_support_le_two (quadratic a b c)
      (quadratic a b c * H) hQ (dvd_mul_right _ _) (by omega)
  have hA : f a ≠ 0 := fun hz => ha (hf (by simpa using hz))
  have hB : f b ≠ 0 := fun hz => hb (hf (by simpa using hz))
  have hC : f c ≠ 0 := fun hz => hc (hf (by simpa using hz))
  have hB₁ : f b₁ ≠ 0 := fun hz => hb₁ (hf (by simpa using hz))
  have hd : quadratic (f a) (f b) (f c) ∣
      monomial u (f b₀) + monomial v (f b₁) := by
    have hm := Polynomial.map_dvd f hdiv
    dsimp [f, R, K] at hm ⊢
    simpa [quadratic] using hm
  have heq := quadratic_binomial_identity (f a) (f b) (f c) (f b₀) (f b₁)
    u v hA hB hC hB₁ huv hd
  apply hobs
  apply hf
  simpa only [map_mul, map_pow] using heq

end Pilz.TwoRow

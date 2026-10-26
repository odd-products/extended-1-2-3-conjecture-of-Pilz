import WeightedPilz.QuadraticObstruction
import WeightedPilz.RationalTranscendence
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.EraseLead

/-! The three occupied rows forced by the initial quadratic obstruction. -/

noncomputable section
namespace WeightedPilz
open Polynomial

theorem quadratic_isCoprime_X {F : Type*} [Field F] (A B D : F) (hA : A ≠ 0) :
    IsCoprime (C A + C B * X + C D * X ^ 2 : F[X]) X := by
  refine ⟨C A⁻¹, -C A⁻¹ * (C B + C D * X), ?_⟩
  calc
    _ = C A⁻¹ * C A := by ring
    _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hA, map_one]

theorem quadratic_natDegree {F : Type*} [Field F] (A B D : F) (hD : D ≠ 0) :
    (C A + C B * X + C D * X ^ 2 : F[X]).natDegree = 2 := by
  compute_degree <;> first | assumption | decide

/-- The quadratic obstruction gives at least three occupied rows in every
nonzero multiple, before any coefficient weights are counted. -/
theorem quadratic_multiple_three_rows {K F : Type*} [Field K] [Field F] [Algebra K F]
    (A B D : F) (hA : A ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0)
    (hs : Transcendental K (A * D / B ^ 2)) (G : F[X]) (hG : G ≠ 0)
    (hdiv : (C A + C B * X + C D * X ^ 2 : F[X]) ∣ G) : 3 ≤ G.support.card := by
  have hpos : G.support.card ≠ 0 := fun h => hG (card_support_eq_zero.mp h)
  by_contra hlt
  have hcases : G.support.card = 1 ∨ G.support.card = 2 := by omega
  rcases hcases with hone | htwo
  · obtain ⟨k, x, hx, hrepr⟩ := card_support_eq_one.mp hone
    have hcop : IsCoprime (C A + C B * X + C D * X ^ 2 : F[X]) (X ^ k) :=
      (quadratic_isCoprime_X A B D hA).pow_right
    have hd : (C A + C B * X + C D * X ^ 2 : F[X]) ∣ C x :=
      hcop.dvd_of_dvd_mul_right (hrepr ▸ hdiv)
    have hz : (C x : F[X]) = 0 := eq_zero_of_dvd_of_natDegree_lt hd (by
      rw [natDegree_C, quadratic_natDegree A B D hD]
      decide)
    exact hx (C_eq_zero.mp hz)
  · obtain ⟨k, m, hkm, x, y, hx, hy, hrepr⟩ := card_support_eq_two.mp htwo
    have hcop : IsCoprime (C A + C B * X + C D * X ^ 2 : F[X]) (X ^ k) :=
      (quadratic_isCoprime_X A B D hA).pow_right
    have hp : (X : F[X]) ^ m = X ^ k * X ^ (m - k) := by
      rw [← pow_add, Nat.add_sub_of_le hkm.le]
    have hfactor : G = X ^ k * (C x + C y * X ^ (m - k)) := by
      rw [hrepr, hp]
      ring
    have hd : (C A + C B * X + C D * X ^ 2 : F[X]) ∣ C x + C y * X ^ (m - k) :=
      hcop.dvd_of_dvd_mul_left (hfactor ▸ hdiv)
    exact quadratic_not_dvd_binomial_of_transcendental_ratio A B D hB hD hs x y hy
      (by omega) hd

/-- The unequal-degree case of `lem:initial-quadratic`, expressed directly for
polynomials in a row variable with univariate polynomial coefficients. -/
theorem quadratic_polynomial_multiple_three_rows {K : Type*} [Field K]
    (A B D : K[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0)
    (hdeg : A.natDegree + D.natDegree ≠ 2 * B.natDegree)
    (G : Polynomial K[X]) (hG : G ≠ 0)
    (hdiv : (C A + C B * X + C D * X ^ 2 : Polynomial K[X]) ∣ G) :
    3 ≤ G.support.card := by
  let f : K[X] →+* RatFunc K := algebraMap K[X] (RatFunc K)
  have hf : Function.Injective f := RatFunc.algebraMap_injective K
  have hratio : Transcendental K (f A * f D / (f B) ^ 2) := by
    have hr := rational_ratio_transcendental (A * D) (B ^ 2)
      (mul_ne_zero hA hD) (pow_ne_zero 2 hB) (by
        rw [natDegree_mul hA hD, natDegree_pow]
        omega)
    simpa only [map_mul, map_pow] using hr
  have hmap : (C (f A) + C (f B) * X + C (f D) * X ^ 2 : (RatFunc K)[X]) ∣ G.map f := by
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X] using Polynomial.map_dvd f hdiv
  have hGmap : G.map f ≠ 0 := by
    intro hz
    apply hG
    exact Polynomial.map_injective f hf (by simpa using hz)
  have h := quadratic_multiple_three_rows (f A) (f B) (f D)
    (RatFunc.algebraMap_ne_zero hA) (RatFunc.algebraMap_ne_zero hB)
    (RatFunc.algebraMap_ne_zero hD) hratio (G.map f) hGmap hmap
  rwa [Polynomial.support_map_of_injective G hf] at h

end WeightedPilz

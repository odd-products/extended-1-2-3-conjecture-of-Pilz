import WeightedPilz.Width
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.CharP.Algebra

/-!
# Algebra of the residue correction

The coefficient polynomials are kept fixed during aggregate replacement.
Only the displayed powers of `Z` are replaced by powers of `-C`.
-/

noncomputable section

namespace WeightedPilz

open scoped BigOperators

section Ring

variable {R : Type*} [CommRing R]

/-- Replacing displayed aggregate powers changes a polynomial by a multiple
of `C + Z`, without evaluating or modifying its coefficient polynomials. -/
theorem aggregate_replacement_dvd {ι : Type*} (s : Finset ι)
    (n : ι → ℕ) (A : ι → R) (C Z : R) :
    C + Z ∣ (∑ j ∈ s, Z ^ n j * A j) - ∑ j ∈ s, (-C) ^ n j * A j := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro j hj
  rw [← sub_mul]
  have hd := sub_dvd_pow_sub_pow Z (-C) (n j)
  have heq : Z - -C = C + Z := by ring
  rw [heq] at hd
  exact dvd_mul_of_dvd_left hd _

theorem aggregate_correction_dvd {ι : Type*} (s : Finset ι)
    (n : ι → ℕ) (A : ι → R) (C Z : R)
    (hG : C + Z ∣ ∑ j ∈ s, Z ^ n j * A j) :
    C + Z ∣ ∑ j ∈ s, (-C) ^ n j * A j := by
  have hd := aggregate_replacement_dvd s n A C Z
  have := dvd_sub hG hd
  simpa only [sub_sub_cancel] using this

end Ring

section Polynomial

variable {R : Type*} [CommRing R]

/-- A polynomial supported on multiples of `q` is an exponent dilation.
The coefficients are copied, so this does not require coefficient roots. -/
theorem polynomial_expand_contract_of_support (q : ℕ) (hq : 0 < q)
    (U : Polynomial R) (hres : ∀ n ∈ U.support, q ∣ n) :
    Polynomial.expand R q (Polynomial.contract q U) = U := by
  ext n
  rw [Polynomial.coeff_expand hq, Polynomial.coeff_contract (ne_of_gt hq)]
  split_ifs with hn
  · rw [Nat.div_mul_cancel hn]
  · symm
    exact Polynomial.notMem_support_iff.mp (fun hm => hn (hres n hm))

/-- A linear factor of a polynomial in `X^(p^e)` occurs to multiplicity at
least `p^e`. This is valid over an arbitrary coefficient ring of exponential
characteristic `p`, and uses no perfectness assumption. -/
theorem linear_pow_dvd_expand (p e : ℕ) [ExpChar R p]
    (a : R) (V : Polynomial R)
    (hdiv : Polynomial.X - Polynomial.C a ∣ Polynomial.expand R (p ^ e) V) :
    (Polynomial.X - Polynomial.C a) ^ (p ^ e) ∣ Polynomial.expand R (p ^ e) V := by
  have hroot : V.eval (a ^ (p ^ e)) = 0 := by
    rw [← Polynomial.expand_eval]
    exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdiv (by simp)
  have hV : Polynomial.X - Polynomial.C (a ^ (p ^ e)) ∣ V :=
    Polynomial.dvd_iff_isRoot.mpr hroot
  obtain ⟨W, hW⟩ := hV
  refine ⟨Polynomial.expand R (p ^ e) W, ?_⟩
  rw [hW, map_mul, map_sub, Polynomial.expand_X, Polynomial.expand_C]
  congr 1
  letI : ExpChar (Polynomial R) p :=
    expChar_of_injective_ringHom Polynomial.C_injective p
  rw [sub_pow_expChar_pow, Polynomial.C.map_pow]

theorem linear_pow_dvd_of_support (p e : ℕ) [ExpChar R p]
    (a : R) (U : Polynomial R)
    (hres : ∀ n ∈ U.support, p ^ e ∣ n)
    (hdiv : Polynomial.X - Polynomial.C a ∣ U) :
    (Polynomial.X - Polynomial.C a) ^ (p ^ e) ∣ U := by
  have hU := polynomial_expand_contract_of_support (p ^ e)
    (expChar_pow_pos R p e) U hres
  rw [← hU] at hdiv ⊢
  exact linear_pow_dvd_expand p e a _ hdiv

end Polynomial

section Coordinate

variable {σ K : Type*} [Field K] [DecidableEq σ]

/-- The correction step in one actual fresh variable. The support premise
states divisibility of that variable's exponents, not existence of roots of
the coefficients. -/
theorem coordinate_frobenius_dvd (p e : ℕ) [ExpChar K p]
    (z : σ) (P U : MvPolynomial σ K)
    (a : MvPolynomial {i : σ // i ≠ z} K)
    (hP : coordinateEquiv z P = Polynomial.X - Polynomial.C a)
    (hres : ∀ d ∈ U.support, p ^ e ∣ d z)
    (hdiv : P ∣ U) : P ^ (p ^ e) ∣ U := by
  letI : ExpChar (MvPolynomial {i : σ // i ≠ z} K) p :=
    expChar_of_injective_ringHom (MvPolynomial.C_injective (σ := {i : σ // i ≠ z})
      (R := K)) p
  have hd : Polynomial.X - Polynomial.C a ∣ coordinateEquiv z U := by
    rw [← hP]
    exact map_dvd (coordinateEquiv z).toRingHom hdiv
  have hr : ∀ n ∈ (coordinateEquiv z U).support, p ^ e ∣ n := by
    intro n hn
    rw [support_coordinateEquiv] at hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    exact hres d hd
  have hpow := linear_pow_dvd_of_support p e a (coordinateEquiv z U) hr hd
  rw [← hP, ← map_pow] at hpow
  obtain ⟨W, hW⟩ := hpow
  refine ⟨(coordinateEquiv z).symm W, ?_⟩
  apply (coordinateEquiv z).injective
  simpa using hW

end Coordinate

end WeightedPilz

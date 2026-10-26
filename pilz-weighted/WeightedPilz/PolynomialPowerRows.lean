import WeightedPilz.QuadraticRows
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.PowerSeries.Basic

/-! The first and penultimate coefficient rows of polynomial powers. -/

noncomputable section
namespace WeightedPilz
open Polynomial

theorem polynomial_coeff_one_pow {R : Type*} [CommRing R] (P : R[X]) (n : ℕ) :
    (P ^ n).coeff 1 = (n : R) * P.coeff 1 * P.coeff 0 ^ (n - 1) := by
  have h := PowerSeries.coeff_one_pow n (P : PowerSeries R)
  rw [← Polynomial.coe_pow] at h
  simpa only [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe] using h

theorem polynomial_coeff_zero_pow {R : Type*} [CommRing R] (P : R[X]) (n : ℕ) :
    (P ^ n).coeff 0 = P.coeff 0 ^ n := map_pow constantCoeff P n

/-- A nonzero reduced exponent preserves the constant, linear, and top terms
of a univariate polynomial with degree at least two. -/
theorem polynomial_power_support_three {K : Type*} [Field K]
    (P : K[X]) (h0 : P.coeff 0 ≠ 0) (h1 : P.coeff 1 ≠ 0)
    (hdeg : 2 ≤ P.natDegree) {n : ℕ} (hn : 0 < n) (hnK : (n : K) ≠ 0) :
    3 ≤ (P ^ n).support.card := by
  classical
  have hP : P ≠ 0 := fun hz => h0 (by rw [hz, coeff_zero])
  have ht : 2 ≤ n * P.natDegree := by
    simpa only [one_mul] using Nat.mul_le_mul hn hdeg
  have hc0 : (P ^ n).coeff 0 ≠ 0 := by
    rw [polynomial_coeff_zero_pow]
    exact pow_ne_zero _ h0
  have hc1 : (P ^ n).coeff 1 ≠ 0 := by
    rw [polynomial_coeff_one_pow]
    exact mul_ne_zero (mul_ne_zero hnK h1) (pow_ne_zero _ h0)
  have hct : (P ^ n).coeff (n * P.natDegree) ≠ 0 := by
    rw [coeff_pow_mul_natDegree]
    exact pow_ne_zero _ (leadingCoeff_ne_zero.mpr hP)
  have hs : ({0, 1, n * P.natDegree} : Finset ℕ) ⊆ (P ^ n).support := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact mem_support_iff.mpr hc0
    · exact mem_support_iff.mpr hc1
    · exact mem_support_iff.mpr hct
  have hcard : ({0, 1, n * P.natDegree} : Finset ℕ).card = 3 := by
    simp [show n * P.natDegree ≠ 0 by omega, show 0 ≠ n * P.natDegree by omega,
      show 1 ≠ n * P.natDegree by omega]
  rw [← hcard]
  exact Finset.card_le_card hs

theorem polynomial_reverse_pow {R : Type*} [CommRing R] [IsDomain R]
    (P : R[X]) (n : ℕ) : (P ^ n).reverse = P.reverse ^ n := by
  induction n with
  | zero => simpa only [pow_zero, map_one] using (reverse_C (1 : R))
  | succ n ih => rw [pow_succ, reverse_mul_of_domain, ih, pow_succ]

theorem polynomial_coeff_penultimate_pow {R : Type*} [CommRing R] [IsDomain R]
    (P : R[X]) (hP : 0 < P.natDegree) {n : ℕ} (hn : 0 < n) :
    (P ^ n).coeff (n * P.natDegree - 1) =
      (n : R) * P.coeff (P.natDegree - 1) * P.leadingCoeff ^ (n - 1) := by
  have h := polynomial_coeff_one_pow P.reverse n
  rw [← polynomial_reverse_pow, coeff_reverse, natDegree_pow,
    revAt_le (Nat.mul_pos hn hP), coeff_reverse,
    revAt_le hP, coeff_zero_reverse] at h
  exact h

/-- The upper, immediately lower, and constant rows in a quadratic power,
with an arbitrary constant multiplier. -/
theorem quadratic_power_rows {F : Type*} [CommRing F] [IsDomain F] (A B D M : F)
    (hD : D ≠ 0) {n : ℕ} (hn : 0 < n) :
    let Q : F[X] := C A + C B * X + C D * X ^ 2
    ((Q ^ n * C M).coeff (2 * n) = D ^ n * M) ∧
    ((Q ^ n * C M).coeff (2 * n - 1) = (n : F) * B * D ^ (n - 1) * M) ∧
    ((Q ^ n * C M).coeff 0 = A ^ n * M) := by
  dsimp only
  let Q : F[X] := C A + C B * X + C D * X ^ 2
  have hd : Q.natDegree = 2 := by
    dsimp [Q]
    compute_degree <;> first | exact hD | decide
  have hlead : Q.leadingCoeff = D := by rw [leadingCoeff, hd]; simp [Q]
  have h1 : Q.coeff 1 = B := by simp [Q]
  have h0 : Q.coeff 0 = A := by simp [Q]
  have htop : (Q ^ n).coeff (2 * n) = D ^ n := by
    have h := coeff_pow_mul_natDegree Q n
    simpa [hd, hlead, Nat.mul_comm] using h
  have hnext : (Q ^ n).coeff (2 * n - 1) = (n : F) * B * D ^ (n - 1) := by
    have h := polynomial_coeff_penultimate_pow Q (by omega) hn
    simpa [hd, h1, hlead, Nat.mul_comm] using h
  have hzero : (Q ^ n).coeff 0 = A ^ n := by
    change constantCoeff (Q ^ n) = _
    rw [map_pow]
    exact congrArg (fun x : F => x ^ n) h0
  change ((Q ^ n * C M).coeff (2 * n) = D ^ n * M) ∧
    ((Q ^ n * C M).coeff (2 * n - 1) = (n : F) * B * D ^ (n - 1) * M) ∧
    ((Q ^ n * C M).coeff 0 = A ^ n * M)
  simp only [coeff_mul_C, htop, hnext, hzero, and_self]

end WeightedPilz

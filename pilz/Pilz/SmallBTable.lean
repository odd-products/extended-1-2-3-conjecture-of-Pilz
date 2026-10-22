import Pilz.SmallMonomials
import Pilz.SmallCoreBounds
import Pilz.F9Parametrization
import Pilz.TwoRowGeneral
import Pilz.TwoRowEndpoints
import Pilz.ComponentProfile
import Pilz.SmallBDegree
import Pilz.SmallSmoothPrefixes
import Mathlib.Tactic.IntervalCases

/-! The bottom/core table for the square-root-smooth polynomials B_n in
27 <= n <= 66. All finite arithmetic identifications are kernel checked. -/
noncomputable section
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
namespace Pilz
open MvPolynomial
open scoped BigOperators

def smallB (n : ℕ) : Poly := smoothInterval (primesUpTo (Nat.sqrt n)) n

def smallBKappa (n : ℕ) : ℕ :=
  if n < 30 then 7 else if n < 32 then 8 else if n < 36 then 7 else
  if n < 40 then 8 else if n < 45 then 7 else if n < 49 then 6 else 8

def smallBDegree (n : ℕ) : ℕ := if n < 32 then 4 else if n < 64 then 5 else 6

def smallBLow (n : ℕ) : Poly := if n < 32 then 1 + X 3 + X 5 else
  if n < 40 then 1 + X 3 else if n < 56 then 1 + X 3 + X 5 else
  if n < 64 then 1 + X 3 + X 5 + X 7 else 1 + X 3

def smallBMid (n : ℕ) : Poly := if n < 32 then 1 + X 3 else
  if n < 48 then 1 else if n < 64 then 1 + X 3 else 1

def smallBOddLinear (n : ℕ) : Poly :=
  if n < 63 then 1 + X 3 + X 5 else 1 + X 3 + X 3 ^ 2 + X 5

def smallBBottom (n : ℕ) : Poly := if n < 45 then SmallCore.f9At (X 3) (X 5) else
  if n < 49 then SmallCore.f12At (X 3) (X 5) else
    SmallCore.f12At (X 3) (X 5) + smallBOddLinear n * X 7 + X 7 ^ 2

/-- A coordinate row, embedded back into the common variable type. -/
def smallBRow (P : Poly) (k : ℕ) : Poly :=
  rename Subtype.val ((coordinateEquiv 2 P).coeff k)

private theorem coord_X_self : coordinateEquiv 2 (X 2 : Poly) = Polynomial.X := by
  simp [coordinateEquiv, optionEquivLeft_X_none]

private theorem coord_X_ne (q : ℕ) (hq : q ≠ 2) :
    coordinateEquiv 2 (X q : Poly) = Polynomial.C (X (⟨q, hq⟩ : {q : ℕ // q ≠ 2})) := by
  simp [coordinateEquiv, Equiv.optionSubtypeNe_symm_of_ne hq, optionEquivLeft_X_some]

@[simp] theorem smallBRow_add (P Q : Poly) (k : ℕ) :
    smallBRow (P + Q) k = smallBRow P k + smallBRow Q k := by
  simp [smallBRow, map_add, Polynomial.coeff_add]

@[simp] theorem smallBRow_sum {ι : Type*} (s : Finset ι) (f : ι → Poly) (k : ℕ) :
    smallBRow (∑ i ∈ s, f i) k = ∑ i ∈ s, smallBRow (f i) k := by
  simp [smallBRow, map_sum, Polynomial.coeff_sum]

@[simp] theorem smallBRow_zero (k : ℕ) : smallBRow 0 k = 0 := by simp [smallBRow]

@[simp] theorem smallBRow_one (k : ℕ) : smallBRow 1 k = if k = 0 then 1 else 0 := by
  simp [smallBRow, Polynomial.coeff_one]


@[simp] theorem smallBRow_X_two_pow (a k : ℕ) :
    smallBRow ((X 2 : Poly) ^ a) k = if k = a then 1 else 0 := by
  simp [smallBRow, map_pow, coord_X_self, Polynomial.coeff_X_pow]


@[simp] theorem smallBRow_X_two (k : ℕ) :
    smallBRow (X 2 : Poly) k = if k = 1 then 1 else 0 := by
  simpa using smallBRow_X_two_pow 1 k

@[simp] theorem smallBRow_mul_pow_ne (P : Poly) (q a k : ℕ) (hq : q ≠ 2) :
    smallBRow (P * X q ^ a) k = smallBRow P k * X q ^ a := by
  unfold smallBRow
  rw [map_mul, map_pow, coord_X_ne q hq, ← Polynomial.C_pow,
    Polynomial.coeff_mul_C, map_mul, map_pow]
  simp

@[simp] theorem smallBRow_mul_X_ne (P : Poly) (q k : ℕ) (hq : q ≠ 2) :
    smallBRow (P * X q) k = smallBRow P k * X q := by
  simpa using smallBRow_mul_pow_ne P q 1 k hq

@[simp] theorem smallBRow_pow_ne (q a k : ℕ) (hq : q ≠ 2) :
    smallBRow ((X q : Poly) ^ a) k = if k = 0 then X q ^ a else 0 := by
  have h := smallBRow_mul_pow_ne 1 q a k hq
  by_cases hk : k = 0 <;> simpa [hk] using h

@[simp] theorem smallBRow_X_ne (q k : ℕ) (hq : q ≠ 2) :
    smallBRow (X q : Poly) k = if k = 0 then X q else 0 := by
  simpa using smallBRow_pow_ne q 1 k hq

private def smallBRelabel : ℕ ≃ ℕ := (Equiv.swap 3 5).trans (Equiv.swap 2 3)

private theorem rename_f9 : renameEquiv (ZMod 2) smallBRelabel SmallCore.f9 =
    SmallCore.f9At (X 3) (X 5) := by
  simp [renameEquiv_apply, SmallCore.f9, SmallCore.f9At, SmallCore.cAt,
    Finset.sum_range_succ, smallBRelabel, Equiv.trans_apply, Equiv.swap_apply_def]

private theorem rename_f12 : renameEquiv (ZMod 2) smallBRelabel SmallCore.f12 =
    SmallCore.f12At (X 3) (X 5) := by
  simp [renameEquiv_apply, SmallCore.f12, SmallCore.f12At, SmallCore.cAt,
    Finset.sum_range_succ, smallBRelabel, Equiv.trans_apply, Equiv.swap_apply_def]

private theorem relabelled_f9_distance : 5 ≤ distance (SmallCore.f9At (X 3) (X 5)) := by
  rw [← rename_f9, distance_renameEquiv]
  exact F9Param.f9_distance_lower_five

private theorem relabelled_f12_distance : 4 ≤ distance (SmallCore.f12At (X 3) (X 5)) := by
  rw [← rename_f12, distance_renameEquiv]
  exact SmallCore.f12_distance_lower

private theorem relabelled_f12_odd_coeff :
    coeff (Finsupp.single 3 1) (SmallCore.f12At (X 3) (X 5)) = 1 := by
  have h := coeff_rename_mapDomain smallBRelabel smallBRelabel.injective
    SmallCore.f12 (Finsupp.single 2 1)
  rw [← rename_f12]
  change coeff (Finsupp.single 3 1) (rename smallBRelabel SmallCore.f12) = 1
  have hx : (Finsupp.single 2 1 : ℕ →₀ ℕ).mapDomain smallBRelabel = Finsupp.single 3 1 := by
    simp [Finsupp.mapDomain_single, smallBRelabel, Equiv.trans_apply, Equiv.swap_apply_def]
  rw [hx] at h
  rw [h]
  simpa [SmallCore.coreExponent] using SmallCore.f12_selected_coefficients.2.1

private theorem relabelled_f12_ne_square (H : Poly) : SmallCore.f12At (X 3) (X 5) ≠ H ^ 2 := by
  intro h
  have hc := congrArg (coeff (Finsupp.single 3 1)) h
  rw [relabelled_f12_odd_coeff, SmallCore.coeff_odd_square_zero _ _ 3 (by simp)] at hc
  exact one_ne_zero hc

private theorem degree_zero_add (p : ℕ) {P Q : Poly}
    (hP : P.degreeOf p = 0) (hQ : Q.degreeOf p = 0) : (P + Q).degreeOf p = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (degreeOf_add_le p P Q).trans_eq (by rw [hP, hQ]; rfl)
private theorem degree_zero_mul (p : ℕ) {P Q : Poly}
    (hP : P.degreeOf p = 0) (hQ : Q.degreeOf p = 0) : (P * Q).degreeOf p = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (degreeOf_mul_le p P Q).trans_eq (by rw [hP, hQ])
private theorem degree_zero_pow (p : ℕ) {P : Poly} (k : ℕ)
    (hP : P.degreeOf p = 0) : (P ^ k).degreeOf p = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (degreeOf_pow_le p P k).trans_eq (by rw [hP, mul_zero])

private theorem relabelled_f12_independent : (SmallCore.f12At (X 3) (X 5)).degreeOf 7 = 0 := by
  have hx : (X 3 : Poly).degreeOf 7 = 0 := by simp [degreeOf_X]
  have hz : (X 5 : Poly).degreeOf 7 = 0 := by simp [degreeOf_X]
  have hc (k : ℕ) : (SmallCore.cAt (X 3) k).degreeOf 7 = 0 := by
    apply Nat.eq_zero_of_le_zero
    unfold SmallCore.cAt
    refine (degreeOf_sum_le 7 _ _).trans ?_
    rw [Finset.sup_le_iff]
    intro i _hi
    exact (degreeOf_pow_le 7 (X 3 : Poly) i).trans_eq (by rw [hx, mul_zero])
  exact degree_zero_add 7 (degree_zero_add 7 (hc 3) (degree_zero_mul 7 (hc 2) hz))
    (degree_zero_pow 7 2 hz)

private theorem oddLinear_independent (n : ℕ) : (smallBOddLinear n).degreeOf 7 = 0 := by
  have h1 : (1 : Poly).degreeOf 7 = 0 := degreeOf_C (1 : ZMod 2) 7
  have hx : (X 3 : Poly).degreeOf 7 = 0 := by simp [degreeOf_X]
  have hz : (X 5 : Poly).degreeOf 7 = 0 := by simp [degreeOf_X]
  unfold smallBOddLinear
  split_ifs
  · exact degree_zero_add 7 (degree_zero_add 7 h1 hx) hz
  · exact degree_zero_add 7 (degree_zero_add 7 (degree_zero_add 7 h1 hx)
      (degree_zero_pow 7 2 hx)) hz
private theorem oddLinear_ne_zero (n : ℕ) : smallBOddLinear n ≠ 0 := by
  intro h
  have hc := congrArg constantCoeff h
  simp [smallBOddLinear, map_add, map_pow] at hc
  split_ifs at hc <;> simpa using hc

private theorem relabelled_f12_ne_zero : SmallCore.f12At (X 3) (X 5) ≠ 0 := by
  intro hz
  have h := relabelled_f12_odd_coeff
  rw [hz, coeff_zero] at h
  exact zero_ne_one h

private theorem smallB_large_bottom_distance (n : ℕ) :
    6 ≤ distance (SmallCore.f12At (X 3) (X 5) + smallBOddLinear n * X 7 + X 7 ^ 2) := by
  have h := quadratic_core_distance 7 (SmallCore.f12At (X 3) (X 5)) (smallBOddLinear n) 1
    relabelled_f12_ne_zero (oddLinear_ne_zero n) one_ne_zero
    relabelled_f12_independent (oddLinear_independent n) (degreeOf_C (1 : ZMod 2) 7)
    (by simpa using relabelled_f12_ne_square (smallBOddLinear n))
  rw [distance_one] at h
  simpa using (show 6 ≤ distance (SmallCore.f12At (X 3) (X 5)) + 1 + 1 by
    have h := relabelled_f12_distance; omega).trans h




private def smallBSet27 : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 25, 27}
private def smallBSet30 : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 25, 27, 30}
private def smallBSet32 : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 25, 27, 30, 32}
private def smallBSet36 : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 25, 27, 30, 32, 36}
private def smallBSet40 : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 25, 27, 30, 32, 36, 40}
private def smallBSet45 : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 25, 27, 30, 32, 36, 40, 45}
private def smallBSet48 : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 25, 27, 30, 32, 36, 40, 45, 48}
private def smallBSet49 : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 35, 36, 40, 42, 45, 48, 49}
private def smallBSet50 : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 35, 36, 40, 42, 45, 48, 49, 50}
private def smallBSet54 : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 35, 36, 40, 42, 45, 48, 49, 50, 54}
private def smallBSet56 : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 35, 36, 40, 42, 45, 48, 49, 50, 54, 56}
private def smallBSet60 : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 35, 36, 40, 42, 45, 48, 49, 50, 54, 56, 60}
private def smallBSet63 : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 35, 36, 40, 42, 45, 48, 49, 50, 54, 56, 60, 63}
private def smallBSet64 : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 35, 36, 40, 42, 45, 48, 49, 50, 54, 56, 60, 63, 64}

private def smallBSet (n : ℕ) : Finset ℕ :=
  if n < 30 then smallBSet27 else
  if n < 32 then smallBSet30 else
  if n < 36 then smallBSet32 else
  if n < 40 then smallBSet36 else
  if n < 45 then smallBSet40 else
  if n < 48 then smallBSet45 else
  if n < 49 then smallBSet48 else
  if n < 50 then smallBSet49 else
  if n < 54 then smallBSet50 else
  if n < 56 then smallBSet54 else
  if n < 60 then smallBSet56 else
  if n < 63 then smallBSet60 else
  if n < 64 then smallBSet63 else
  smallBSet64

private theorem smallB_numbers (n : ℕ) (hlo : 27 ≤ n) (hhi : n ≤ 66) :
    smoothNumbers (primesUpTo (Nat.sqrt n)) n = smallBSet n := by
  have h6 : primesUpTo 6 = primesUpTo 5 := by decide
  have h8 : primesUpTo 8 = primesUpTo 7 := by decide
  interval_cases n
  · have hs : Nat.sqrt 27 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 27 ∧ 27 < (5 + 1) * (5 + 1))).symm
    rw [hs, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 28 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 28 ∧ 28 < (5 + 1) * (5 + 1))).symm
    rw [hs, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 29 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 29 ∧ 29 < (5 + 1) * (5 + 1))).symm
    rw [hs, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 30 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 30 ∧ 30 < (5 + 1) * (5 + 1))).symm
    rw [hs, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 31 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 31 ∧ 31 < (5 + 1) * (5 + 1))).symm
    rw [hs, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 32 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 32 ∧ 32 < (5 + 1) * (5 + 1))).symm
    rw [hs, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 33 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 33 ∧ 33 < (5 + 1) * (5 + 1))).symm
    rw [hs, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 34 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 34 ∧ 34 < (5 + 1) * (5 + 1))).symm
    rw [hs, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 35 = 5 :=
      (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 35 ∧ 35 < (5 + 1) * (5 + 1))).symm
    rw [hs, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 36 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 36 ∧ 36 < (6 + 1) * (6 + 1))).symm
    rw [hs, h6, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 37 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 37 ∧ 37 < (6 + 1) * (6 + 1))).symm
    rw [hs, h6, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 38 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 38 ∧ 38 < (6 + 1) * (6 + 1))).symm
    rw [hs, h6, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 39 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 39 ∧ 39 < (6 + 1) * (6 + 1))).symm
    rw [hs, h6, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 40 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 40 ∧ 40 < (6 + 1) * (6 + 1))).symm
    rw [hs, h6, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 41 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 41 ∧ 41 < (6 + 1) * (6 + 1))).symm
    rw [hs, h6, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 42 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 42 ∧ 42 < (6 + 1) * (6 + 1))).symm
    rw [hs, h6, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 43 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 43 ∧ 43 < (6 + 1) * (6 + 1))).symm
    rw [hs, h6, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 44 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 44 ∧ 44 < (6 + 1) * (6 + 1))).symm
    rw [hs, h6, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 45 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 45 ∧ 45 < (6 + 1) * (6 + 1))).symm
    rw [hs, h6, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 46 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 46 ∧ 46 < (6 + 1) * (6 + 1))).symm
    rw [hs, h6, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 47 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 47 ∧ 47 < (6 + 1) * (6 + 1))).symm
    rw [hs, h6, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 48 = 6 :=
      (Nat.eq_sqrt.mpr (by decide : 6 * 6 ≤ 48 ∧ 48 < (6 + 1) * (6 + 1))).symm
    rw [hs, h6, smallSmooth_five_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 49 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 49 ∧ 49 < (7 + 1) * (7 + 1))).symm
    rw [hs, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 50 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 50 ∧ 50 < (7 + 1) * (7 + 1))).symm
    rw [hs, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 51 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 51 ∧ 51 < (7 + 1) * (7 + 1))).symm
    rw [hs, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 52 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 52 ∧ 52 < (7 + 1) * (7 + 1))).symm
    rw [hs, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 53 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 53 ∧ 53 < (7 + 1) * (7 + 1))).symm
    rw [hs, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 54 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 54 ∧ 54 < (7 + 1) * (7 + 1))).symm
    rw [hs, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 55 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 55 ∧ 55 < (7 + 1) * (7 + 1))).symm
    rw [hs, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 56 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 56 ∧ 56 < (7 + 1) * (7 + 1))).symm
    rw [hs, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 57 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 57 ∧ 57 < (7 + 1) * (7 + 1))).symm
    rw [hs, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 58 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 58 ∧ 58 < (7 + 1) * (7 + 1))).symm
    rw [hs, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 59 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 59 ∧ 59 < (7 + 1) * (7 + 1))).symm
    rw [hs, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 60 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 60 ∧ 60 < (7 + 1) * (7 + 1))).symm
    rw [hs, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 61 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 61 ∧ 61 < (7 + 1) * (7 + 1))).symm
    rw [hs, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 62 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 62 ∧ 62 < (7 + 1) * (7 + 1))).symm
    rw [hs, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 63 = 7 :=
      (Nat.eq_sqrt.mpr (by decide : 7 * 7 ≤ 63 ∧ 63 < (7 + 1) * (7 + 1))).symm
    rw [hs, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 64 = 8 :=
      (Nat.eq_sqrt.mpr (by decide : 8 * 8 ≤ 64 ∧ 64 < (8 + 1) * (8 + 1))).symm
    rw [hs, h8, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 65 = 8 :=
      (Nat.eq_sqrt.mpr (by decide : 8 * 8 ≤ 65 ∧ 65 < (8 + 1) * (8 + 1))).symm
    rw [hs, h8, smallSmooth_seven_prefix (by decide)]
    decide
  · have hs : Nat.sqrt 66 = 8 :=
      (Nat.eq_sqrt.mpr (by decide : 8 * 8 ≤ 66 ∧ 66 < (8 + 1) * (8 + 1))).symm
    rw [hs, h8, smallSmooth_seven_prefix (by decide)]
    decide

private theorem smallB_polynomialOf (n : ℕ) (hlo : 27 ≤ n) (hhi : n ≤ 66) :
    smallB n = polynomialOf (smallBSet n) := by
  simp only [smallB, smoothInterval, smallB_numbers n hlo hhi]

private theorem smallBSet_positive (n : ℕ) (hlo : 27 ≤ n) (hhi : n ≤ 66) :
    ∀ a ∈ smallBSet n, 0 < a := by
  intro a ha
  rw [← smallB_numbers n hlo hhi] at ha
  exact (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1

private theorem smallB_weight (n : ℕ) (hlo : 27 ≤ n) (hhi : n ≤ 66) :
    weight (smallB n) = (smallBSet n).card := by
  rw [smallB_polynomialOf n hlo hhi]
  exact weight_polynomialOf (smallBSet n) (smallBSet_positive n hlo hhi)

private theorem smallB_rows_27 :
    smallBRow (polynomialOf smallBSet27) 0 = smallBBottom 27 ∧
    smallBRow (polynomialOf smallBSet27) (smallBDegree 27 - 2) = smallBLow 27 ∧
    smallBRow (polynomialOf smallBSet27) (smallBDegree 27 - 1) = smallBMid 27 ∧
    smallBRow (polynomialOf smallBSet27) (smallBDegree 27) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num only [smallBSet27, polynomialOf, smallBBottom, smallBOddLinear,
    smallBDegree, smallBLow, smallBMid, SmallCore.f9At, SmallCore.f12At,
    SmallCore.cAt, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, or_false, false_or, ite_true, ite_false, and_true, true_and,
    monomialOf_one,
    SmallMonomials.m2, SmallMonomials.m3, SmallMonomials.m4, SmallMonomials.m5,
    SmallMonomials.m6, SmallMonomials.m7, SmallMonomials.m8, SmallMonomials.m9,
    SmallMonomials.m10, SmallMonomials.m12, SmallMonomials.m14, SmallMonomials.m15,
    SmallMonomials.m16, SmallMonomials.m18, SmallMonomials.m20, SmallMonomials.m21,
    SmallMonomials.m24, SmallMonomials.m25, SmallMonomials.m27, SmallMonomials.m28,
    SmallMonomials.m30, SmallMonomials.m32, SmallMonomials.m35, SmallMonomials.m36,
    SmallMonomials.m40, SmallMonomials.m42, SmallMonomials.m45, SmallMonomials.m48,
    SmallMonomials.m49, SmallMonomials.m50, SmallMonomials.m54, SmallMonomials.m56,
    SmallMonomials.m60, SmallMonomials.m63, SmallMonomials.m64,
    smallBRow_add, smallBRow_sum, smallBRow_zero,
    smallBRow_one, smallBRow_X_two_pow, smallBRow_X_two, smallBRow_mul_pow_ne,
    smallBRow_mul_X_ne, smallBRow_pow_ne, smallBRow_X_ne,
    pow_zero, pow_one, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;>
    ring

private theorem smallB_rows_30 :
    smallBRow (polynomialOf smallBSet30) 0 = smallBBottom 30 ∧
    smallBRow (polynomialOf smallBSet30) (smallBDegree 30 - 2) = smallBLow 30 ∧
    smallBRow (polynomialOf smallBSet30) (smallBDegree 30 - 1) = smallBMid 30 ∧
    smallBRow (polynomialOf smallBSet30) (smallBDegree 30) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num only [smallBSet30, polynomialOf, smallBBottom, smallBOddLinear,
    smallBDegree, smallBLow, smallBMid, SmallCore.f9At, SmallCore.f12At,
    SmallCore.cAt, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, or_false, false_or, ite_true, ite_false, and_true, true_and,
    monomialOf_one,
    SmallMonomials.m2, SmallMonomials.m3, SmallMonomials.m4, SmallMonomials.m5,
    SmallMonomials.m6, SmallMonomials.m7, SmallMonomials.m8, SmallMonomials.m9,
    SmallMonomials.m10, SmallMonomials.m12, SmallMonomials.m14, SmallMonomials.m15,
    SmallMonomials.m16, SmallMonomials.m18, SmallMonomials.m20, SmallMonomials.m21,
    SmallMonomials.m24, SmallMonomials.m25, SmallMonomials.m27, SmallMonomials.m28,
    SmallMonomials.m30, SmallMonomials.m32, SmallMonomials.m35, SmallMonomials.m36,
    SmallMonomials.m40, SmallMonomials.m42, SmallMonomials.m45, SmallMonomials.m48,
    SmallMonomials.m49, SmallMonomials.m50, SmallMonomials.m54, SmallMonomials.m56,
    SmallMonomials.m60, SmallMonomials.m63, SmallMonomials.m64,
    smallBRow_add, smallBRow_sum, smallBRow_zero,
    smallBRow_one, smallBRow_X_two_pow, smallBRow_X_two, smallBRow_mul_pow_ne,
    smallBRow_mul_X_ne, smallBRow_pow_ne, smallBRow_X_ne,
    pow_zero, pow_one, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;>
    ring

private theorem smallB_rows_32 :
    smallBRow (polynomialOf smallBSet32) 0 = smallBBottom 32 ∧
    smallBRow (polynomialOf smallBSet32) (smallBDegree 32 - 2) = smallBLow 32 ∧
    smallBRow (polynomialOf smallBSet32) (smallBDegree 32 - 1) = smallBMid 32 ∧
    smallBRow (polynomialOf smallBSet32) (smallBDegree 32) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num only [smallBSet32, polynomialOf, smallBBottom, smallBOddLinear,
    smallBDegree, smallBLow, smallBMid, SmallCore.f9At, SmallCore.f12At,
    SmallCore.cAt, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, or_false, false_or, ite_true, ite_false, and_true, true_and,
    monomialOf_one,
    SmallMonomials.m2, SmallMonomials.m3, SmallMonomials.m4, SmallMonomials.m5,
    SmallMonomials.m6, SmallMonomials.m7, SmallMonomials.m8, SmallMonomials.m9,
    SmallMonomials.m10, SmallMonomials.m12, SmallMonomials.m14, SmallMonomials.m15,
    SmallMonomials.m16, SmallMonomials.m18, SmallMonomials.m20, SmallMonomials.m21,
    SmallMonomials.m24, SmallMonomials.m25, SmallMonomials.m27, SmallMonomials.m28,
    SmallMonomials.m30, SmallMonomials.m32, SmallMonomials.m35, SmallMonomials.m36,
    SmallMonomials.m40, SmallMonomials.m42, SmallMonomials.m45, SmallMonomials.m48,
    SmallMonomials.m49, SmallMonomials.m50, SmallMonomials.m54, SmallMonomials.m56,
    SmallMonomials.m60, SmallMonomials.m63, SmallMonomials.m64,
    smallBRow_add, smallBRow_sum, smallBRow_zero,
    smallBRow_one, smallBRow_X_two_pow, smallBRow_X_two, smallBRow_mul_pow_ne,
    smallBRow_mul_X_ne, smallBRow_pow_ne, smallBRow_X_ne,
    pow_zero, pow_one, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;>
    ring

private theorem smallB_rows_36 :
    smallBRow (polynomialOf smallBSet36) 0 = smallBBottom 36 ∧
    smallBRow (polynomialOf smallBSet36) (smallBDegree 36 - 2) = smallBLow 36 ∧
    smallBRow (polynomialOf smallBSet36) (smallBDegree 36 - 1) = smallBMid 36 ∧
    smallBRow (polynomialOf smallBSet36) (smallBDegree 36) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num only [smallBSet36, polynomialOf, smallBBottom, smallBOddLinear,
    smallBDegree, smallBLow, smallBMid, SmallCore.f9At, SmallCore.f12At,
    SmallCore.cAt, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, or_false, false_or, ite_true, ite_false, and_true, true_and,
    monomialOf_one,
    SmallMonomials.m2, SmallMonomials.m3, SmallMonomials.m4, SmallMonomials.m5,
    SmallMonomials.m6, SmallMonomials.m7, SmallMonomials.m8, SmallMonomials.m9,
    SmallMonomials.m10, SmallMonomials.m12, SmallMonomials.m14, SmallMonomials.m15,
    SmallMonomials.m16, SmallMonomials.m18, SmallMonomials.m20, SmallMonomials.m21,
    SmallMonomials.m24, SmallMonomials.m25, SmallMonomials.m27, SmallMonomials.m28,
    SmallMonomials.m30, SmallMonomials.m32, SmallMonomials.m35, SmallMonomials.m36,
    SmallMonomials.m40, SmallMonomials.m42, SmallMonomials.m45, SmallMonomials.m48,
    SmallMonomials.m49, SmallMonomials.m50, SmallMonomials.m54, SmallMonomials.m56,
    SmallMonomials.m60, SmallMonomials.m63, SmallMonomials.m64,
    smallBRow_add, smallBRow_sum, smallBRow_zero,
    smallBRow_one, smallBRow_X_two_pow, smallBRow_X_two, smallBRow_mul_pow_ne,
    smallBRow_mul_X_ne, smallBRow_pow_ne, smallBRow_X_ne,
    pow_zero, pow_one, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;>
    ring

private theorem smallB_rows_40 :
    smallBRow (polynomialOf smallBSet40) 0 = smallBBottom 40 ∧
    smallBRow (polynomialOf smallBSet40) (smallBDegree 40 - 2) = smallBLow 40 ∧
    smallBRow (polynomialOf smallBSet40) (smallBDegree 40 - 1) = smallBMid 40 ∧
    smallBRow (polynomialOf smallBSet40) (smallBDegree 40) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num only [smallBSet40, polynomialOf, smallBBottom, smallBOddLinear,
    smallBDegree, smallBLow, smallBMid, SmallCore.f9At, SmallCore.f12At,
    SmallCore.cAt, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, or_false, false_or, ite_true, ite_false, and_true, true_and,
    monomialOf_one,
    SmallMonomials.m2, SmallMonomials.m3, SmallMonomials.m4, SmallMonomials.m5,
    SmallMonomials.m6, SmallMonomials.m7, SmallMonomials.m8, SmallMonomials.m9,
    SmallMonomials.m10, SmallMonomials.m12, SmallMonomials.m14, SmallMonomials.m15,
    SmallMonomials.m16, SmallMonomials.m18, SmallMonomials.m20, SmallMonomials.m21,
    SmallMonomials.m24, SmallMonomials.m25, SmallMonomials.m27, SmallMonomials.m28,
    SmallMonomials.m30, SmallMonomials.m32, SmallMonomials.m35, SmallMonomials.m36,
    SmallMonomials.m40, SmallMonomials.m42, SmallMonomials.m45, SmallMonomials.m48,
    SmallMonomials.m49, SmallMonomials.m50, SmallMonomials.m54, SmallMonomials.m56,
    SmallMonomials.m60, SmallMonomials.m63, SmallMonomials.m64,
    smallBRow_add, smallBRow_sum, smallBRow_zero,
    smallBRow_one, smallBRow_X_two_pow, smallBRow_X_two, smallBRow_mul_pow_ne,
    smallBRow_mul_X_ne, smallBRow_pow_ne, smallBRow_X_ne,
    pow_zero, pow_one, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;>
    ring

private theorem smallB_rows_45 :
    smallBRow (polynomialOf smallBSet45) 0 = smallBBottom 45 ∧
    smallBRow (polynomialOf smallBSet45) (smallBDegree 45 - 2) = smallBLow 45 ∧
    smallBRow (polynomialOf smallBSet45) (smallBDegree 45 - 1) = smallBMid 45 ∧
    smallBRow (polynomialOf smallBSet45) (smallBDegree 45) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num only [smallBSet45, polynomialOf, smallBBottom, smallBOddLinear,
    smallBDegree, smallBLow, smallBMid, SmallCore.f9At, SmallCore.f12At,
    SmallCore.cAt, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, or_false, false_or, ite_true, ite_false, and_true, true_and,
    monomialOf_one,
    SmallMonomials.m2, SmallMonomials.m3, SmallMonomials.m4, SmallMonomials.m5,
    SmallMonomials.m6, SmallMonomials.m7, SmallMonomials.m8, SmallMonomials.m9,
    SmallMonomials.m10, SmallMonomials.m12, SmallMonomials.m14, SmallMonomials.m15,
    SmallMonomials.m16, SmallMonomials.m18, SmallMonomials.m20, SmallMonomials.m21,
    SmallMonomials.m24, SmallMonomials.m25, SmallMonomials.m27, SmallMonomials.m28,
    SmallMonomials.m30, SmallMonomials.m32, SmallMonomials.m35, SmallMonomials.m36,
    SmallMonomials.m40, SmallMonomials.m42, SmallMonomials.m45, SmallMonomials.m48,
    SmallMonomials.m49, SmallMonomials.m50, SmallMonomials.m54, SmallMonomials.m56,
    SmallMonomials.m60, SmallMonomials.m63, SmallMonomials.m64,
    smallBRow_add, smallBRow_sum, smallBRow_zero,
    smallBRow_one, smallBRow_X_two_pow, smallBRow_X_two, smallBRow_mul_pow_ne,
    smallBRow_mul_X_ne, smallBRow_pow_ne, smallBRow_X_ne,
    pow_zero, pow_one, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;>
    ring

private theorem smallB_rows_48 :
    smallBRow (polynomialOf smallBSet48) 0 = smallBBottom 48 ∧
    smallBRow (polynomialOf smallBSet48) (smallBDegree 48 - 2) = smallBLow 48 ∧
    smallBRow (polynomialOf smallBSet48) (smallBDegree 48 - 1) = smallBMid 48 ∧
    smallBRow (polynomialOf smallBSet48) (smallBDegree 48) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num only [smallBSet48, polynomialOf, smallBBottom, smallBOddLinear,
    smallBDegree, smallBLow, smallBMid, SmallCore.f9At, SmallCore.f12At,
    SmallCore.cAt, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, or_false, false_or, ite_true, ite_false, and_true, true_and,
    monomialOf_one,
    SmallMonomials.m2, SmallMonomials.m3, SmallMonomials.m4, SmallMonomials.m5,
    SmallMonomials.m6, SmallMonomials.m7, SmallMonomials.m8, SmallMonomials.m9,
    SmallMonomials.m10, SmallMonomials.m12, SmallMonomials.m14, SmallMonomials.m15,
    SmallMonomials.m16, SmallMonomials.m18, SmallMonomials.m20, SmallMonomials.m21,
    SmallMonomials.m24, SmallMonomials.m25, SmallMonomials.m27, SmallMonomials.m28,
    SmallMonomials.m30, SmallMonomials.m32, SmallMonomials.m35, SmallMonomials.m36,
    SmallMonomials.m40, SmallMonomials.m42, SmallMonomials.m45, SmallMonomials.m48,
    SmallMonomials.m49, SmallMonomials.m50, SmallMonomials.m54, SmallMonomials.m56,
    SmallMonomials.m60, SmallMonomials.m63, SmallMonomials.m64,
    smallBRow_add, smallBRow_sum, smallBRow_zero,
    smallBRow_one, smallBRow_X_two_pow, smallBRow_X_two, smallBRow_mul_pow_ne,
    smallBRow_mul_X_ne, smallBRow_pow_ne, smallBRow_X_ne,
    pow_zero, pow_one, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;>
    ring

private theorem smallB_rows_49 :
    smallBRow (polynomialOf smallBSet49) 0 = smallBBottom 49 ∧
    smallBRow (polynomialOf smallBSet49) (smallBDegree 49 - 2) = smallBLow 49 ∧
    smallBRow (polynomialOf smallBSet49) (smallBDegree 49 - 1) = smallBMid 49 ∧
    smallBRow (polynomialOf smallBSet49) (smallBDegree 49) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num only [smallBSet49, polynomialOf, smallBBottom, smallBOddLinear,
    smallBDegree, smallBLow, smallBMid, SmallCore.f9At, SmallCore.f12At,
    SmallCore.cAt, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, or_false, false_or, ite_true, ite_false, and_true, true_and,
    monomialOf_one,
    SmallMonomials.m2, SmallMonomials.m3, SmallMonomials.m4, SmallMonomials.m5,
    SmallMonomials.m6, SmallMonomials.m7, SmallMonomials.m8, SmallMonomials.m9,
    SmallMonomials.m10, SmallMonomials.m12, SmallMonomials.m14, SmallMonomials.m15,
    SmallMonomials.m16, SmallMonomials.m18, SmallMonomials.m20, SmallMonomials.m21,
    SmallMonomials.m24, SmallMonomials.m25, SmallMonomials.m27, SmallMonomials.m28,
    SmallMonomials.m30, SmallMonomials.m32, SmallMonomials.m35, SmallMonomials.m36,
    SmallMonomials.m40, SmallMonomials.m42, SmallMonomials.m45, SmallMonomials.m48,
    SmallMonomials.m49, SmallMonomials.m50, SmallMonomials.m54, SmallMonomials.m56,
    SmallMonomials.m60, SmallMonomials.m63, SmallMonomials.m64,
    smallBRow_add, smallBRow_sum, smallBRow_zero,
    smallBRow_one, smallBRow_X_two_pow, smallBRow_X_two, smallBRow_mul_pow_ne,
    smallBRow_mul_X_ne, smallBRow_pow_ne, smallBRow_X_ne,
    pow_zero, pow_one, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;>
    ring

private theorem smallB_rows_50 :
    smallBRow (polynomialOf smallBSet50) 0 = smallBBottom 50 ∧
    smallBRow (polynomialOf smallBSet50) (smallBDegree 50 - 2) = smallBLow 50 ∧
    smallBRow (polynomialOf smallBSet50) (smallBDegree 50 - 1) = smallBMid 50 ∧
    smallBRow (polynomialOf smallBSet50) (smallBDegree 50) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num only [smallBSet50, polynomialOf, smallBBottom, smallBOddLinear,
    smallBDegree, smallBLow, smallBMid, SmallCore.f9At, SmallCore.f12At,
    SmallCore.cAt, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, or_false, false_or, ite_true, ite_false, and_true, true_and,
    monomialOf_one,
    SmallMonomials.m2, SmallMonomials.m3, SmallMonomials.m4, SmallMonomials.m5,
    SmallMonomials.m6, SmallMonomials.m7, SmallMonomials.m8, SmallMonomials.m9,
    SmallMonomials.m10, SmallMonomials.m12, SmallMonomials.m14, SmallMonomials.m15,
    SmallMonomials.m16, SmallMonomials.m18, SmallMonomials.m20, SmallMonomials.m21,
    SmallMonomials.m24, SmallMonomials.m25, SmallMonomials.m27, SmallMonomials.m28,
    SmallMonomials.m30, SmallMonomials.m32, SmallMonomials.m35, SmallMonomials.m36,
    SmallMonomials.m40, SmallMonomials.m42, SmallMonomials.m45, SmallMonomials.m48,
    SmallMonomials.m49, SmallMonomials.m50, SmallMonomials.m54, SmallMonomials.m56,
    SmallMonomials.m60, SmallMonomials.m63, SmallMonomials.m64,
    smallBRow_add, smallBRow_sum, smallBRow_zero,
    smallBRow_one, smallBRow_X_two_pow, smallBRow_X_two, smallBRow_mul_pow_ne,
    smallBRow_mul_X_ne, smallBRow_pow_ne, smallBRow_X_ne,
    pow_zero, pow_one, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;>
    ring

private theorem smallB_rows_54 :
    smallBRow (polynomialOf smallBSet54) 0 = smallBBottom 54 ∧
    smallBRow (polynomialOf smallBSet54) (smallBDegree 54 - 2) = smallBLow 54 ∧
    smallBRow (polynomialOf smallBSet54) (smallBDegree 54 - 1) = smallBMid 54 ∧
    smallBRow (polynomialOf smallBSet54) (smallBDegree 54) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num only [smallBSet54, polynomialOf, smallBBottom, smallBOddLinear,
    smallBDegree, smallBLow, smallBMid, SmallCore.f9At, SmallCore.f12At,
    SmallCore.cAt, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, or_false, false_or, ite_true, ite_false, and_true, true_and,
    monomialOf_one,
    SmallMonomials.m2, SmallMonomials.m3, SmallMonomials.m4, SmallMonomials.m5,
    SmallMonomials.m6, SmallMonomials.m7, SmallMonomials.m8, SmallMonomials.m9,
    SmallMonomials.m10, SmallMonomials.m12, SmallMonomials.m14, SmallMonomials.m15,
    SmallMonomials.m16, SmallMonomials.m18, SmallMonomials.m20, SmallMonomials.m21,
    SmallMonomials.m24, SmallMonomials.m25, SmallMonomials.m27, SmallMonomials.m28,
    SmallMonomials.m30, SmallMonomials.m32, SmallMonomials.m35, SmallMonomials.m36,
    SmallMonomials.m40, SmallMonomials.m42, SmallMonomials.m45, SmallMonomials.m48,
    SmallMonomials.m49, SmallMonomials.m50, SmallMonomials.m54, SmallMonomials.m56,
    SmallMonomials.m60, SmallMonomials.m63, SmallMonomials.m64,
    smallBRow_add, smallBRow_sum, smallBRow_zero,
    smallBRow_one, smallBRow_X_two_pow, smallBRow_X_two, smallBRow_mul_pow_ne,
    smallBRow_mul_X_ne, smallBRow_pow_ne, smallBRow_X_ne,
    pow_zero, pow_one, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;>
    ring

private theorem smallB_rows_56 :
    smallBRow (polynomialOf smallBSet56) 0 = smallBBottom 56 ∧
    smallBRow (polynomialOf smallBSet56) (smallBDegree 56 - 2) = smallBLow 56 ∧
    smallBRow (polynomialOf smallBSet56) (smallBDegree 56 - 1) = smallBMid 56 ∧
    smallBRow (polynomialOf smallBSet56) (smallBDegree 56) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num only [smallBSet56, polynomialOf, smallBBottom, smallBOddLinear,
    smallBDegree, smallBLow, smallBMid, SmallCore.f9At, SmallCore.f12At,
    SmallCore.cAt, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, or_false, false_or, ite_true, ite_false, and_true, true_and,
    monomialOf_one,
    SmallMonomials.m2, SmallMonomials.m3, SmallMonomials.m4, SmallMonomials.m5,
    SmallMonomials.m6, SmallMonomials.m7, SmallMonomials.m8, SmallMonomials.m9,
    SmallMonomials.m10, SmallMonomials.m12, SmallMonomials.m14, SmallMonomials.m15,
    SmallMonomials.m16, SmallMonomials.m18, SmallMonomials.m20, SmallMonomials.m21,
    SmallMonomials.m24, SmallMonomials.m25, SmallMonomials.m27, SmallMonomials.m28,
    SmallMonomials.m30, SmallMonomials.m32, SmallMonomials.m35, SmallMonomials.m36,
    SmallMonomials.m40, SmallMonomials.m42, SmallMonomials.m45, SmallMonomials.m48,
    SmallMonomials.m49, SmallMonomials.m50, SmallMonomials.m54, SmallMonomials.m56,
    SmallMonomials.m60, SmallMonomials.m63, SmallMonomials.m64,
    smallBRow_add, smallBRow_sum, smallBRow_zero,
    smallBRow_one, smallBRow_X_two_pow, smallBRow_X_two, smallBRow_mul_pow_ne,
    smallBRow_mul_X_ne, smallBRow_pow_ne, smallBRow_X_ne,
    pow_zero, pow_one, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;>
    ring

private theorem smallB_rows_60 :
    smallBRow (polynomialOf smallBSet60) 0 = smallBBottom 60 ∧
    smallBRow (polynomialOf smallBSet60) (smallBDegree 60 - 2) = smallBLow 60 ∧
    smallBRow (polynomialOf smallBSet60) (smallBDegree 60 - 1) = smallBMid 60 ∧
    smallBRow (polynomialOf smallBSet60) (smallBDegree 60) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num only [smallBSet60, polynomialOf, smallBBottom, smallBOddLinear,
    smallBDegree, smallBLow, smallBMid, SmallCore.f9At, SmallCore.f12At,
    SmallCore.cAt, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, or_false, false_or, ite_true, ite_false, and_true, true_and,
    monomialOf_one,
    SmallMonomials.m2, SmallMonomials.m3, SmallMonomials.m4, SmallMonomials.m5,
    SmallMonomials.m6, SmallMonomials.m7, SmallMonomials.m8, SmallMonomials.m9,
    SmallMonomials.m10, SmallMonomials.m12, SmallMonomials.m14, SmallMonomials.m15,
    SmallMonomials.m16, SmallMonomials.m18, SmallMonomials.m20, SmallMonomials.m21,
    SmallMonomials.m24, SmallMonomials.m25, SmallMonomials.m27, SmallMonomials.m28,
    SmallMonomials.m30, SmallMonomials.m32, SmallMonomials.m35, SmallMonomials.m36,
    SmallMonomials.m40, SmallMonomials.m42, SmallMonomials.m45, SmallMonomials.m48,
    SmallMonomials.m49, SmallMonomials.m50, SmallMonomials.m54, SmallMonomials.m56,
    SmallMonomials.m60, SmallMonomials.m63, SmallMonomials.m64,
    smallBRow_add, smallBRow_sum, smallBRow_zero,
    smallBRow_one, smallBRow_X_two_pow, smallBRow_X_two, smallBRow_mul_pow_ne,
    smallBRow_mul_X_ne, smallBRow_pow_ne, smallBRow_X_ne,
    pow_zero, pow_one, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;>
    ring

private theorem smallB_rows_63 :
    smallBRow (polynomialOf smallBSet63) 0 = smallBBottom 63 ∧
    smallBRow (polynomialOf smallBSet63) (smallBDegree 63 - 2) = smallBLow 63 ∧
    smallBRow (polynomialOf smallBSet63) (smallBDegree 63 - 1) = smallBMid 63 ∧
    smallBRow (polynomialOf smallBSet63) (smallBDegree 63) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num only [smallBSet63, polynomialOf, smallBBottom, smallBOddLinear,
    smallBDegree, smallBLow, smallBMid, SmallCore.f9At, SmallCore.f12At,
    SmallCore.cAt, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, or_false, false_or, ite_true, ite_false, and_true, true_and,
    monomialOf_one,
    SmallMonomials.m2, SmallMonomials.m3, SmallMonomials.m4, SmallMonomials.m5,
    SmallMonomials.m6, SmallMonomials.m7, SmallMonomials.m8, SmallMonomials.m9,
    SmallMonomials.m10, SmallMonomials.m12, SmallMonomials.m14, SmallMonomials.m15,
    SmallMonomials.m16, SmallMonomials.m18, SmallMonomials.m20, SmallMonomials.m21,
    SmallMonomials.m24, SmallMonomials.m25, SmallMonomials.m27, SmallMonomials.m28,
    SmallMonomials.m30, SmallMonomials.m32, SmallMonomials.m35, SmallMonomials.m36,
    SmallMonomials.m40, SmallMonomials.m42, SmallMonomials.m45, SmallMonomials.m48,
    SmallMonomials.m49, SmallMonomials.m50, SmallMonomials.m54, SmallMonomials.m56,
    SmallMonomials.m60, SmallMonomials.m63, SmallMonomials.m64,
    smallBRow_add, smallBRow_sum, smallBRow_zero,
    smallBRow_one, smallBRow_X_two_pow, smallBRow_X_two, smallBRow_mul_pow_ne,
    smallBRow_mul_X_ne, smallBRow_pow_ne, smallBRow_X_ne,
    pow_zero, pow_one, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;>
    ring

private theorem smallB_rows_64 :
    smallBRow (polynomialOf smallBSet64) 0 = smallBBottom 64 ∧
    smallBRow (polynomialOf smallBSet64) (smallBDegree 64 - 2) = smallBLow 64 ∧
    smallBRow (polynomialOf smallBSet64) (smallBDegree 64 - 1) = smallBMid 64 ∧
    smallBRow (polynomialOf smallBSet64) (smallBDegree 64) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num only [smallBSet64, polynomialOf, smallBBottom, smallBOddLinear,
    smallBDegree, smallBLow, smallBMid, SmallCore.f9At, SmallCore.f12At,
    SmallCore.cAt, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    not_false_eq_true, or_false, false_or, ite_true, ite_false, and_true, true_and,
    monomialOf_one,
    SmallMonomials.m2, SmallMonomials.m3, SmallMonomials.m4, SmallMonomials.m5,
    SmallMonomials.m6, SmallMonomials.m7, SmallMonomials.m8, SmallMonomials.m9,
    SmallMonomials.m10, SmallMonomials.m12, SmallMonomials.m14, SmallMonomials.m15,
    SmallMonomials.m16, SmallMonomials.m18, SmallMonomials.m20, SmallMonomials.m21,
    SmallMonomials.m24, SmallMonomials.m25, SmallMonomials.m27, SmallMonomials.m28,
    SmallMonomials.m30, SmallMonomials.m32, SmallMonomials.m35, SmallMonomials.m36,
    SmallMonomials.m40, SmallMonomials.m42, SmallMonomials.m45, SmallMonomials.m48,
    SmallMonomials.m49, SmallMonomials.m50, SmallMonomials.m54, SmallMonomials.m56,
    SmallMonomials.m60, SmallMonomials.m63, SmallMonomials.m64,
    smallBRow_add, smallBRow_sum, smallBRow_zero,
    smallBRow_one, smallBRow_X_two_pow, smallBRow_X_two, smallBRow_mul_pow_ne,
    smallBRow_mul_X_ne, smallBRow_pow_ne, smallBRow_X_ne,
    pow_zero, pow_one, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;>
    ring

private theorem smallB_rows (n : ℕ) (hlo : 27 ≤ n) (hhi : n ≤ 66) :
    smallBRow (smallB n) 0 = smallBBottom n ∧
    smallBRow (smallB n) (smallBDegree n - 2) = smallBLow n ∧
    smallBRow (smallB n) (smallBDegree n - 1) = smallBMid n ∧
    smallBRow (smallB n) (smallBDegree n) = 1 := by
  simp only [smallB_polynomialOf n hlo hhi]
  interval_cases n
  · exact smallB_rows_27
  · exact smallB_rows_27
  · exact smallB_rows_27
  · exact smallB_rows_30
  · exact smallB_rows_30
  · exact smallB_rows_32
  · exact smallB_rows_32
  · exact smallB_rows_32
  · exact smallB_rows_32
  · exact smallB_rows_36
  · exact smallB_rows_36
  · exact smallB_rows_36
  · exact smallB_rows_36
  · exact smallB_rows_40
  · exact smallB_rows_40
  · exact smallB_rows_40
  · exact smallB_rows_40
  · exact smallB_rows_40
  · exact smallB_rows_45
  · exact smallB_rows_45
  · exact smallB_rows_45
  · exact smallB_rows_48
  · exact smallB_rows_49
  · exact smallB_rows_50
  · exact smallB_rows_50
  · exact smallB_rows_50
  · exact smallB_rows_50
  · exact smallB_rows_54
  · exact smallB_rows_54
  · exact smallB_rows_56
  · exact smallB_rows_56
  · exact smallB_rows_56
  · exact smallB_rows_56
  · exact smallB_rows_60
  · exact smallB_rows_60
  · exact smallB_rows_60
  · exact smallB_rows_63
  · exact smallB_rows_64
  · exact smallB_rows_64
  · exact smallB_rows_64

private theorem smallB_degree_upper (n : ℕ) (_hlo : 27 ≤ n) (hhi : n ≤ 66) :
    (smallB n).degreeOf 2 ≤ smallBDegree n := by
  unfold smallB
  apply smoothInterval_degreeOf_two_le
  unfold smallBDegree
  split_ifs <;> norm_num only [Nat.reduceAdd, Nat.reducePow] <;> omega

private theorem smallB_degree (n : ℕ) (hlo : 27 ≤ n) (hhi : n ≤ 66) :
    (coordinateEquiv 2 (smallB n)).natDegree = smallBDegree n := by
  apply Nat.le_antisymm
  · rw [natDegree_coordinateEquiv]
    exact smallB_degree_upper n hlo hhi
  · have ht := (smallB_rows n hlo hhi).2.2.2
    apply Polynomial.le_natDegree_of_ne_zero
    intro hz
    have hrow : smallBRow (smallB n) (smallBDegree n) = 0 := by simp [smallBRow, hz]
    rw [ht] at hrow
    exact one_ne_zero hrow

private theorem smallBLow_odd_coeff (n : ℕ) :
    coeff (Finsupp.single 3 1) (smallBLow n) = 1 := by
  have hne : (0 : ℕ →₀ ℕ) ≠ Finsupp.single 3 1 :=
    Ne.symm (Finsupp.single_ne_zero.mpr (by decide))
  unfold smallBLow
  split_ifs <;> simp [hne, MvPolynomial.coeff_add, MvPolynomial.coeff_one, MvPolynomial.coeff_X]

private theorem smallBLow_ne_zero (n : ℕ) : smallBLow n ≠ 0 := by
  intro hz
  have h := smallBLow_odd_coeff n
  rw [hz, coeff_zero] at h
  exact zero_ne_one h

private theorem smallBMid_ne_zero (n : ℕ) : smallBMid n ≠ 0 := by
  intro hz
  have h := congrArg constantCoeff hz
  unfold smallBMid at h
  split_ifs at h <;> simp at h

private theorem smallBLow_ne_mid_square (n : ℕ) : smallBLow n ≠ smallBMid n ^ 2 := by
  intro h
  have hc := congrArg (coeff (Finsupp.single 3 1)) h
  rw [smallBLow_odd_coeff, SmallCore.coeff_odd_square_zero _ _ 3 (by simp)] at hc
  exact one_ne_zero hc

private def smallBBottomBudget (n : ℕ) : ℕ := if n < 45 then 5 else if n < 49 then 4 else 6

private theorem smallBBottom_distance (n : ℕ) :
    smallBBottomBudget n ≤ distance (smallBBottom n) := by
  unfold smallBBottom smallBBottomBudget
  split_ifs
  · exact relabelled_f9_distance
  · exact relabelled_f12_distance
  · exact smallB_large_bottom_distance n

/-- Transfer the subtype coefficient endpoint theorem back to the common variables. -/
private theorem smallB_row_endpoint_bound (P : Poly) (d : ℕ)
    (hd : 2 ≤ d) (hdegree : (coordinateEquiv 2 P).natDegree = d)
    (h0 : smallBRow P 0 ≠ 0) (hlow : smallBRow P (d - 2) ≠ 0)
    (hmid : smallBRow P (d - 1) ≠ 0)
    (hobs : smallBRow P (d - 2) ≠ smallBRow P (d - 1) ^ 2)
    (htop : smallBRow P d = 1) : distance (smallBRow P 0) + 2 ≤ distance P := by
  have hne (k : ℕ) (hk : smallBRow P k ≠ 0) : (coordinateEquiv 2 P).coeff k ≠ 0 := by
    intro hz
    exact hk (by simp [smallBRow, hz])
  have hobs' : (coordinateEquiv 2 P).coeff ((coordinateEquiv 2 P).natDegree - 2) *
      (coordinateEquiv 2 P).leadingCoeff ≠
      (coordinateEquiv 2 P).coeff ((coordinateEquiv 2 P).natDegree - 1) ^ 2 := by
    intro heq
    simp only [Polynomial.leadingCoeff, hdegree] at heq
    have hr := congrArg (rename (Subtype.val : {q : ℕ // q ≠ 2} → ℕ)) heq
    simp only [map_mul, map_pow] at hr
    change smallBRow P (d - 2) * smallBRow P d = smallBRow P (d - 1) ^ 2 at hr
    rw [htop, mul_one] at hr
    exact hobs hr
  have h := top_three_endpoint_distance 2 P (by omega) (hne 0 h0)
    (by simpa only [hdegree] using hne (d - 2) hlow)
    (by simpa only [hdegree] using hne (d - 1) hmid) hobs'
  rw [hdegree] at h
  have h0dist := distance_rename_le Subtype.val Subtype.val_injective ((coordinateEquiv 2 P).coeff 0)
  have hddist := distance_rename_le Subtype.val Subtype.val_injective ((coordinateEquiv 2 P).coeff d)
  change distance (smallBRow P 0) ≤ distance ((coordinateEquiv 2 P).coeff 0) at h0dist
  change distance (smallBRow P d) ≤ distance ((coordinateEquiv 2 P).coeff d) at hddist
  rw [htop, distance_one] at hddist
  omega

private theorem smallB_base_distance (n : ℕ) (hlo : 27 ≤ n) (hhi : n ≤ 66) :
    smallBBottomBudget n + 2 ≤ distance (smallB n) := by
  obtain ⟨h0, hlow, hmid, htop⟩ := smallB_rows n hlo hhi
  have hd : 2 ≤ smallBDegree n := by unfold smallBDegree; split_ifs <;> omega
  have hbottompos : 0 < distance (smallBBottom n) := by
    have h := smallBBottom_distance n
    unfold smallBBottomBudget at h
    split_ifs at h <;> omega
  have hbottom : smallBBottom n ≠ 0 := by
    intro hz
    rw [hz, distance_zero] at hbottompos
    omega
  have h := smallB_row_endpoint_bound (smallB n) (smallBDegree n) hd (smallB_degree n hlo hhi)
    (by rwa [h0]) (by rw [hlow]; exact smallBLow_ne_zero n)
    (by rw [hmid]; exact smallBMid_ne_zero n)
    (by rw [hlow, hmid]; exact smallBLow_ne_mid_square n) htop
  rw [h0] at h
  exact (Nat.add_le_add_right (smallBBottom_distance n) 2).trans h

private theorem smallB_even_weight (n : ℕ) (hlo : 27 ≤ n) (hhi : n ≤ 66)
    (heven : (30 ≤ n ∧ n < 32) ∨ (36 ≤ n ∧ n < 40)) : Even (weight (smallB n)) := by
  rw [smallB_weight n hlo hhi]
  rcases heven with ⟨h30, h32⟩ | ⟨h36, h40⟩ <;> interval_cases n <;>
    decide

/-- Exactly the seven kappa_B bands in the paper. -/
theorem smallB_distance_lower (n : ℕ) (hlo : 27 ≤ n) (hhi : n ≤ 66) :
    smallBKappa n ≤ distance (smallB n) := by
  have hb := smallB_base_distance n hlo hhi
  by_cases h30 : n < 30
  · simpa [smallBKappa, smallBBottomBudget, h30, show n < 45 by omega] using hb
  by_cases h32 : n < 32
  · have he := even_distance_of_even_weight (smallB_even_weight n hlo hhi (Or.inl ⟨by omega, h32⟩))
    obtain ⟨k, hk⟩ := he
    simp [smallBKappa, smallBBottomBudget, h30, h32, show n < 45 by omega] at hb ⊢
    omega
  by_cases h36 : n < 36
  · simpa [smallBKappa, smallBBottomBudget, h30, h32, h36, show n < 45 by omega] using hb
  by_cases h40 : n < 40
  · have he := even_distance_of_even_weight (smallB_even_weight n hlo hhi (Or.inr ⟨by omega, h40⟩))
    obtain ⟨k, hk⟩ := he
    simp [smallBKappa, smallBBottomBudget, h30, h32, h36, h40, show n < 45 by omega] at hb ⊢
    omega
  by_cases h45 : n < 45
  · simpa [smallBKappa, smallBBottomBudget, h30, h32, h36, h40, h45] using hb
  by_cases h49 : n < 49
  · simpa [smallBKappa, smallBBottomBudget, h30, h32, h36, h40, h45, h49] using hb
  · simpa [smallBKappa, smallBBottomBudget, h30, h32, h36, h40, h45, h49] using hb

/-- The exact B_27 bound used by the two finite exceptional cases. -/
theorem smallB_twentyseven_distance_seven :
    7 ≤ distance (smoothInterval (primesUpTo 5) 27) := by
  have h := smallB_distance_lower 27 (by decide) (by decide)
  have hs : Nat.sqrt 27 = 5 := (Nat.eq_sqrt.mpr (by decide : 5 * 5 ≤ 27 ∧ 27 < 6 * 6)).symm
  simpa [smallBKappa, smallB, hs] using h

end Pilz


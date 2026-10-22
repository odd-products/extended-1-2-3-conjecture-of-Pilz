import Pilz.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-! Exact monomial expansions at the small interval lengths. Each composite
identity is derived from multiplicativity; the numeric factorizations are
checked by Lean. -/

noncomputable section
namespace Pilz.SmallMonomials
open MvPolynomial

@[simp] theorem m2 : monomialOf 2 = (X 2 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m3 : monomialOf 3 = (X 3 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m4 : monomialOf 4 = (X 2 ^ 2 : Poly) := by
  calc
    monomialOf 4 = monomialOf 2 * monomialOf 2 :=
      monomialOf_mul (a := 2) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m2]; ring

@[simp] theorem m5 : monomialOf 5 = (X 5 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m6 : monomialOf 6 = (X 2 * X 3 : Poly) := by
  calc
    monomialOf 6 = monomialOf 3 * monomialOf 2 :=
      monomialOf_mul (a := 3) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m3, m2]; ring

@[simp] theorem m7 : monomialOf 7 = (X 7 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m8 : monomialOf 8 = (X 2 ^ 3 : Poly) := by
  calc
    monomialOf 8 = monomialOf 4 * monomialOf 2 :=
      monomialOf_mul (a := 4) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m4, m2]; ring

@[simp] theorem m9 : monomialOf 9 = (X 3 ^ 2 : Poly) := by
  calc
    monomialOf 9 = monomialOf 3 * monomialOf 3 :=
      monomialOf_mul (a := 3) (b := 3) (by decide) (by decide)
    _ = _ := by rw [m3]; ring

@[simp] theorem m10 : monomialOf 10 = (X 2 * X 5 : Poly) := by
  calc
    monomialOf 10 = monomialOf 5 * monomialOf 2 :=
      monomialOf_mul (a := 5) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m5, m2]; ring

@[simp] theorem m11 : monomialOf 11 = (X 11 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m12 : monomialOf 12 = (X 2 ^ 2 * X 3 : Poly) := by
  calc
    monomialOf 12 = monomialOf 6 * monomialOf 2 :=
      monomialOf_mul (a := 6) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m6, m2]; ring

@[simp] theorem m13 : monomialOf 13 = (X 13 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m14 : monomialOf 14 = (X 2 * X 7 : Poly) := by
  calc
    monomialOf 14 = monomialOf 7 * monomialOf 2 :=
      monomialOf_mul (a := 7) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m7, m2]; ring

@[simp] theorem m15 : monomialOf 15 = (X 3 * X 5 : Poly) := by
  calc
    monomialOf 15 = monomialOf 5 * monomialOf 3 :=
      monomialOf_mul (a := 5) (b := 3) (by decide) (by decide)
    _ = _ := by rw [m5, m3]; ring

@[simp] theorem m16 : monomialOf 16 = (X 2 ^ 4 : Poly) := by
  calc
    monomialOf 16 = monomialOf 8 * monomialOf 2 :=
      monomialOf_mul (a := 8) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m8, m2]; ring

@[simp] theorem m17 : monomialOf 17 = (X 17 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m18 : monomialOf 18 = (X 2 * X 3 ^ 2 : Poly) := by
  calc
    monomialOf 18 = monomialOf 9 * monomialOf 2 :=
      monomialOf_mul (a := 9) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m9, m2]; ring

@[simp] theorem m19 : monomialOf 19 = (X 19 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m20 : monomialOf 20 = (X 2 ^ 2 * X 5 : Poly) := by
  calc
    monomialOf 20 = monomialOf 10 * monomialOf 2 :=
      monomialOf_mul (a := 10) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m10, m2]; ring

@[simp] theorem m21 : monomialOf 21 = (X 3 * X 7 : Poly) := by
  calc
    monomialOf 21 = monomialOf 7 * monomialOf 3 :=
      monomialOf_mul (a := 7) (b := 3) (by decide) (by decide)
    _ = _ := by rw [m7, m3]; ring

@[simp] theorem m22 : monomialOf 22 = (X 2 * X 11 : Poly) := by
  calc
    monomialOf 22 = monomialOf 11 * monomialOf 2 :=
      monomialOf_mul (a := 11) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m11, m2]; ring

@[simp] theorem m23 : monomialOf 23 = (X 23 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m24 : monomialOf 24 = (X 2 ^ 3 * X 3 : Poly) := by
  calc
    monomialOf 24 = monomialOf 12 * monomialOf 2 :=
      monomialOf_mul (a := 12) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m12, m2]; ring

@[simp] theorem m25 : monomialOf 25 = (X 5 ^ 2 : Poly) := by
  calc
    monomialOf 25 = monomialOf 5 * monomialOf 5 :=
      monomialOf_mul (a := 5) (b := 5) (by decide) (by decide)
    _ = _ := by rw [m5]; ring

@[simp] theorem m26 : monomialOf 26 = (X 2 * X 13 : Poly) := by
  calc
    monomialOf 26 = monomialOf 13 * monomialOf 2 :=
      monomialOf_mul (a := 13) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m13, m2]; ring

@[simp] theorem m27 : monomialOf 27 = (X 3 ^ 3 : Poly) := by
  calc
    monomialOf 27 = monomialOf 9 * monomialOf 3 :=
      monomialOf_mul (a := 9) (b := 3) (by decide) (by decide)
    _ = _ := by rw [m9, m3]; ring

@[simp] theorem m28 : monomialOf 28 = (X 2 ^ 2 * X 7 : Poly) := by
  calc
    monomialOf 28 = monomialOf 14 * monomialOf 2 :=
      monomialOf_mul (a := 14) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m14, m2]; ring

@[simp] theorem m29 : monomialOf 29 = (X 29 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m30 : monomialOf 30 = (X 2 * X 3 * X 5 : Poly) := by
  calc
    monomialOf 30 = monomialOf 15 * monomialOf 2 :=
      monomialOf_mul (a := 15) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m15, m2]; ring

@[simp] theorem m31 : monomialOf 31 = (X 31 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m32 : monomialOf 32 = (X 2 ^ 5 : Poly) := by
  calc
    monomialOf 32 = monomialOf 16 * monomialOf 2 :=
      monomialOf_mul (a := 16) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m16, m2]; ring

@[simp] theorem m33 : monomialOf 33 = (X 3 * X 11 : Poly) := by
  calc
    monomialOf 33 = monomialOf 11 * monomialOf 3 :=
      monomialOf_mul (a := 11) (b := 3) (by decide) (by decide)
    _ = _ := by rw [m11, m3]; ring

@[simp] theorem m34 : monomialOf 34 = (X 2 * X 17 : Poly) := by
  calc
    monomialOf 34 = monomialOf 17 * monomialOf 2 :=
      monomialOf_mul (a := 17) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m17, m2]; ring

@[simp] theorem m35 : monomialOf 35 = (X 5 * X 7 : Poly) := by
  calc
    monomialOf 35 = monomialOf 7 * monomialOf 5 :=
      monomialOf_mul (a := 7) (b := 5) (by decide) (by decide)
    _ = _ := by rw [m7, m5]; ring

@[simp] theorem m36 : monomialOf 36 = (X 2 ^ 2 * X 3 ^ 2 : Poly) := by
  calc
    monomialOf 36 = monomialOf 18 * monomialOf 2 :=
      monomialOf_mul (a := 18) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m18, m2]; ring

@[simp] theorem m37 : monomialOf 37 = (X 37 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m38 : monomialOf 38 = (X 2 * X 19 : Poly) := by
  calc
    monomialOf 38 = monomialOf 19 * monomialOf 2 :=
      monomialOf_mul (a := 19) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m19, m2]; ring

@[simp] theorem m39 : monomialOf 39 = (X 3 * X 13 : Poly) := by
  calc
    monomialOf 39 = monomialOf 13 * monomialOf 3 :=
      monomialOf_mul (a := 13) (b := 3) (by decide) (by decide)
    _ = _ := by rw [m13, m3]; ring

@[simp] theorem m40 : monomialOf 40 = (X 2 ^ 3 * X 5 : Poly) := by
  calc
    monomialOf 40 = monomialOf 20 * monomialOf 2 :=
      monomialOf_mul (a := 20) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m20, m2]; ring

@[simp] theorem m41 : monomialOf 41 = (X 41 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m42 : monomialOf 42 = (X 2 * X 3 * X 7 : Poly) := by
  calc
    monomialOf 42 = monomialOf 21 * monomialOf 2 :=
      monomialOf_mul (a := 21) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m21, m2]; ring

@[simp] theorem m43 : monomialOf 43 = (X 43 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m44 : monomialOf 44 = (X 2 ^ 2 * X 11 : Poly) := by
  calc
    monomialOf 44 = monomialOf 22 * monomialOf 2 :=
      monomialOf_mul (a := 22) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m22, m2]; ring

@[simp] theorem m45 : monomialOf 45 = (X 3 ^ 2 * X 5 : Poly) := by
  calc
    monomialOf 45 = monomialOf 15 * monomialOf 3 :=
      monomialOf_mul (a := 15) (b := 3) (by decide) (by decide)
    _ = _ := by rw [m15, m3]; ring

@[simp] theorem m46 : monomialOf 46 = (X 2 * X 23 : Poly) := by
  calc
    monomialOf 46 = monomialOf 23 * monomialOf 2 :=
      monomialOf_mul (a := 23) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m23, m2]; ring

@[simp] theorem m47 : monomialOf 47 = (X 47 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m48 : monomialOf 48 = (X 2 ^ 4 * X 3 : Poly) := by
  calc
    monomialOf 48 = monomialOf 24 * monomialOf 2 :=
      monomialOf_mul (a := 24) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m24, m2]; ring

@[simp] theorem m49 : monomialOf 49 = (X 7 ^ 2 : Poly) := by
  calc
    monomialOf 49 = monomialOf 7 * monomialOf 7 :=
      monomialOf_mul (a := 7) (b := 7) (by decide) (by decide)
    _ = _ := by rw [m7]; ring

@[simp] theorem m50 : monomialOf 50 = (X 2 * X 5 ^ 2 : Poly) := by
  calc
    monomialOf 50 = monomialOf 25 * monomialOf 2 :=
      monomialOf_mul (a := 25) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m25, m2]; ring

@[simp] theorem m51 : monomialOf 51 = (X 3 * X 17 : Poly) := by
  calc
    monomialOf 51 = monomialOf 17 * monomialOf 3 :=
      monomialOf_mul (a := 17) (b := 3) (by decide) (by decide)
    _ = _ := by rw [m17, m3]; ring

@[simp] theorem m52 : monomialOf 52 = (X 2 ^ 2 * X 13 : Poly) := by
  calc
    monomialOf 52 = monomialOf 26 * monomialOf 2 :=
      monomialOf_mul (a := 26) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m26, m2]; ring

@[simp] theorem m53 : monomialOf 53 = (X 53 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m54 : monomialOf 54 = (X 2 * X 3 ^ 3 : Poly) := by
  calc
    monomialOf 54 = monomialOf 27 * monomialOf 2 :=
      monomialOf_mul (a := 27) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m27, m2]; ring

@[simp] theorem m55 : monomialOf 55 = (X 5 * X 11 : Poly) := by
  calc
    monomialOf 55 = monomialOf 11 * monomialOf 5 :=
      monomialOf_mul (a := 11) (b := 5) (by decide) (by decide)
    _ = _ := by rw [m11, m5]; ring

@[simp] theorem m56 : monomialOf 56 = (X 2 ^ 3 * X 7 : Poly) := by
  calc
    monomialOf 56 = monomialOf 28 * monomialOf 2 :=
      monomialOf_mul (a := 28) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m28, m2]; ring

@[simp] theorem m57 : monomialOf 57 = (X 3 * X 19 : Poly) := by
  calc
    monomialOf 57 = monomialOf 19 * monomialOf 3 :=
      monomialOf_mul (a := 19) (b := 3) (by decide) (by decide)
    _ = _ := by rw [m19, m3]; ring

@[simp] theorem m58 : monomialOf 58 = (X 2 * X 29 : Poly) := by
  calc
    monomialOf 58 = monomialOf 29 * monomialOf 2 :=
      monomialOf_mul (a := 29) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m29, m2]; ring

@[simp] theorem m59 : monomialOf 59 = (X 59 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m60 : monomialOf 60 = (X 2 ^ 2 * X 3 * X 5 : Poly) := by
  calc
    monomialOf 60 = monomialOf 30 * monomialOf 2 :=
      monomialOf_mul (a := 30) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m30, m2]; ring

@[simp] theorem m61 : monomialOf 61 = (X 61 : Poly) := by
  exact monomialOf_prime (by norm_num)

@[simp] theorem m62 : monomialOf 62 = (X 2 * X 31 : Poly) := by
  calc
    monomialOf 62 = monomialOf 31 * monomialOf 2 :=
      monomialOf_mul (a := 31) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m31, m2]; ring

@[simp] theorem m63 : monomialOf 63 = (X 3 ^ 2 * X 7 : Poly) := by
  calc
    monomialOf 63 = monomialOf 21 * monomialOf 3 :=
      monomialOf_mul (a := 21) (b := 3) (by decide) (by decide)
    _ = _ := by rw [m21, m3]; ring

@[simp] theorem m64 : monomialOf 64 = (X 2 ^ 6 : Poly) := by
  calc
    monomialOf 64 = monomialOf 32 * monomialOf 2 :=
      monomialOf_mul (a := 32) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m32, m2]; ring

@[simp] theorem m65 : monomialOf 65 = (X 5 * X 13 : Poly) := by
  calc
    monomialOf 65 = monomialOf 13 * monomialOf 5 :=
      monomialOf_mul (a := 13) (b := 5) (by decide) (by decide)
    _ = _ := by rw [m13, m5]; ring

@[simp] theorem m66 : monomialOf 66 = (X 2 * X 3 * X 11 : Poly) := by
  calc
    monomialOf 66 = monomialOf 33 * monomialOf 2 :=
      monomialOf_mul (a := 33) (b := 2) (by decide) (by decide)
    _ = _ := by rw [m33, m2]; ring

end Pilz.SmallMonomials


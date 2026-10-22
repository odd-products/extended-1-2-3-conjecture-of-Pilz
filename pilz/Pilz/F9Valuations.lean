import Pilz.Parity
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring

/-!
# The two-point argument for the exceptional core f₉

The manuscript's substitution is `x = 1+v+v²`, `y=v²(v+1)`.
Translation by one fixes `x` and exchanges the two points `v=0,1`.
Thus every polynomial in `x` has the same two vanishing orders. A sum
of at most two distinct monomials involving positive powers of `y`
cannot have that symmetry.
-/

noncomputable section

namespace Pilz.F9Param

open Polynomial

abbrev R := Polynomial (ZMod 2)

def U : R := 1 + X + X ^ 2
def V : R := X ^ 2 * (X + 1)
def W : R := (X + 1) ^ 2 * X
def shift : R →+* R := Polynomial.compRingHom (X + 1)

@[simp] theorem shift_U : shift U = U := by
  simp only [shift, Polynomial.coe_compRingHom_apply, U, add_comp, pow_comp,
    one_comp, X_comp, CharTwo.add_sq, one_pow]
  calc
    1 + (X + 1) + (X ^ 2 + 1) = (1 + X + X ^ 2 : R) + (1 + 1) := by ac_rfl
    _ = 1 + X + X ^ 2 := by rw [CharTwo.add_self_eq_zero, add_zero]

@[simp] theorem shift_V : shift V = W := by
  simp only [shift, Polynomial.coe_compRingHom_apply, V, W, mul_comp, pow_comp,
    add_comp, X_comp, one_comp]
  congr 1
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

@[simp] theorem U_coeff_zero : U.coeff 0 = 1 := by simp [U]
@[simp] theorem X_add_one_coeff_zero : ((X : R) + 1).coeff 0 = 1 := by simp

theorem U_ne_zero : U ≠ 0 := by
  intro h
  have := U_coeff_zero
  rw [h, coeff_zero] at this
  exact zero_ne_one this

theorem X_add_one_ne_zero : (X : R) + 1 ≠ 0 := by
  intro h
  have := X_add_one_coeff_zero
  rw [h, coeff_zero] at this
  exact zero_ne_one this

theorem V_ne_zero : V ≠ 0 :=
  mul_ne_zero (pow_ne_zero 2 Polynomial.X_ne_zero) X_add_one_ne_zero

theorem W_ne_zero : W ≠ 0 :=
  mul_ne_zero (pow_ne_zero 2 X_add_one_ne_zero) Polynomial.X_ne_zero

@[simp] theorem U_order : U.natTrailingDegree = 0 :=
  Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (by rw [U_coeff_zero]; exact one_ne_zero))

@[simp] theorem X_add_one_order : ((X : R) + 1).natTrailingDegree = 0 :=
  Polynomial.natTrailingDegree_eq_zero.mpr
    (Or.inr (by rw [X_add_one_coeff_zero]; exact one_ne_zero))

@[simp] theorem V_order : V.natTrailingDegree = 2 := by
  rw [V, Polynomial.natTrailingDegree_mul (pow_ne_zero 2 Polynomial.X_ne_zero)
    X_add_one_ne_zero, Polynomial.natTrailingDegree_X_pow, X_add_one_order, add_zero]

@[simp] theorem W_order : W.natTrailingDegree = 1 := by
  have hpow : (((X : R) + 1) ^ 2).natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (by simp [pow_two, mul_coeff_zero]))
  rw [W, Polynomial.natTrailingDegree_mul (pow_ne_zero 2 X_add_one_ne_zero)
    Polynomial.X_ne_zero, hpow, Polynomial.natTrailingDegree_X, zero_add]

theorem order_pow (P : R) (hP : P ≠ 0) (n : ℕ) :
    (P ^ n).natTrailingDegree = n * P.natTrailingDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Polynomial.natTrailingDegree_mul (pow_ne_zero n hP) hP, ih]
    rw [Nat.succ_mul]

/-- At different orders the lowest term cannot cancel. -/
theorem order_add_of_lt (P Q : R) (hP : P ≠ 0)
    (hlt : P.natTrailingDegree < Q.natTrailingDegree) :
    P + Q ≠ 0 ∧ (P + Q).natTrailingDegree = P.natTrailingDegree := by
  have hc : (P + Q).coeff P.natTrailingDegree ≠ 0 := by
    rw [coeff_add, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt, add_zero]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hP
  have hsum : P + Q ≠ 0 := fun hz => hc (by rw [hz, coeff_zero])
  refine ⟨hsum, Nat.le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hc) ?_⟩
  apply Polynomial.le_natTrailingDegree hsum
  intro m hm
  rw [coeff_add, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hm,
    Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (hm.trans hlt), add_zero]

theorem U_degree : U.natDegree = 2 := by
  unfold U
  compute_degree!

theorem U_pow_injective : Function.Injective (fun n : ℕ => U ^ n) := by
  intro a b hab
  have hd := congrArg Polynomial.natDegree hab
  rw [Polynomial.natDegree_pow' (pow_ne_zero a (Polynomial.leadingCoeff_ne_zero.mpr U_ne_zero)),
    Polynomial.natDegree_pow' (pow_ne_zero b (Polynomial.leadingCoeff_ne_zero.mpr U_ne_zero)),
    U_degree] at hd
  omega

theorem U_pow_add_ne_zero {a b : ℕ} (hab : a ≠ b) : U ^ a + U ^ b ≠ 0 := by
  intro hz
  have heq : U ^ a = U ^ b := by
    have hh := congrArg (fun P : R => P + U ^ b) hz
    simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using hh
  exact hab (U_pow_injective heq)

theorem term_order_V (a e : ℕ) : (U ^ a * V ^ e).natTrailingDegree = 2 * e := by
  rw [Polynomial.natTrailingDegree_mul (pow_ne_zero a U_ne_zero) (pow_ne_zero e V_ne_zero),
    order_pow U U_ne_zero, order_pow V V_ne_zero, U_order, V_order]
  omega

theorem term_order_W (a e : ℕ) : (U ^ a * W ^ e).natTrailingDegree = e := by
  rw [Polynomial.natTrailingDegree_mul (pow_ne_zero a U_ne_zero) (pow_ne_zero e W_ne_zero),
    order_pow U U_ne_zero, order_pow W W_ne_zero, U_order, W_order]
  omega

theorem positive_term_not_fixed (a e : ℕ) (he : 0 < e) :
    shift (U ^ a * V ^ e) ≠ U ^ a * V ^ e := by
  intro h
  have hh := congrArg Polynomial.natTrailingDegree h
  have hh' : e = 2 * e := by
    simpa only [map_mul, map_pow, shift_U, shift_V, term_order_V, term_order_W] using hh
  omega

/-- The two positive-y terms in the paper's contradiction cannot be fixed
by the exchange of `v=0` and `v=1`. -/
theorem two_positive_terms_not_fixed (a b e f : ℕ) (he : 0 < e) (hf : 0 < f)
    (hne : (a, e) ≠ (b, f)) :
    shift (U ^ a * V ^ e + U ^ b * V ^ f) ≠ U ^ a * V ^ e + U ^ b * V ^ f := by
  intro h
  have hshift : U ^ a * W ^ e + U ^ b * W ^ f =
      U ^ a * V ^ e + U ^ b * V ^ f := by
    simpa only [map_add, map_mul, map_pow, shift_U, shift_V] using h
  rcases lt_trichotomy e f with hef | hef | hfe
  · have hV := order_add_of_lt (U ^ a * V ^ e) (U ^ b * V ^ f)
      (mul_ne_zero (pow_ne_zero a U_ne_zero) (pow_ne_zero e V_ne_zero))
      (by rw [term_order_V, term_order_V]; omega)
    have hW := order_add_of_lt (U ^ a * W ^ e) (U ^ b * W ^ f)
      (mul_ne_zero (pow_ne_zero a U_ne_zero) (pow_ne_zero e W_ne_zero))
      (by rw [term_order_W, term_order_W]; exact hef)
    have hh := congrArg Polynomial.natTrailingDegree hshift
    rw [hV.2, hW.2, term_order_V, term_order_W] at hh
    omega
  · subst f
    have hab : a ≠ b := fun hh => hne (by simp [hh])
    have hA := U_pow_add_ne_zero hab
    have hfactor : (U ^ a + U ^ b) * W ^ e = (U ^ a + U ^ b) * V ^ e := by
      simpa only [add_mul] using hshift
    have hh := congrArg Polynomial.natTrailingDegree hfactor
    rw [Polynomial.natTrailingDegree_mul hA (pow_ne_zero e W_ne_zero),
      Polynomial.natTrailingDegree_mul hA (pow_ne_zero e V_ne_zero),
      order_pow W W_ne_zero, order_pow V V_ne_zero, V_order, W_order] at hh
    omega
  · have hV := order_add_of_lt (U ^ b * V ^ f) (U ^ a * V ^ e)
      (mul_ne_zero (pow_ne_zero b U_ne_zero) (pow_ne_zero f V_ne_zero))
      (by rw [term_order_V, term_order_V]; omega)
    have hW := order_add_of_lt (U ^ b * W ^ f) (U ^ a * W ^ e)
      (mul_ne_zero (pow_ne_zero b U_ne_zero) (pow_ne_zero f W_ne_zero))
      (by rw [term_order_W, term_order_W]; exact hfe)
    have hh := congrArg Polynomial.natTrailingDegree hshift
    rw [add_comm (U ^ a * W ^ e), add_comm (U ^ a * V ^ e),
      hV.2, hW.2, term_order_V, term_order_W] at hh
    omega

end Pilz.F9Param

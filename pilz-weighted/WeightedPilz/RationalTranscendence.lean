import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Rational functions of nonzero degree are transcendental over the constant field. -/

noncomputable section
namespace WeightedPilz
open Polynomial
variable {K : Type*} [Field K]

theorem ratfunc_intDegree_pow (r : RatFunc K) (hr : r ≠ 0) (n : ℕ) :
    (r ^ n).intDegree = (n : ℤ) * r.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hr) hr, ih]
    push_cast
    ring

theorem ratfunc_add_of_intDegree_lt (x y : RatFunc K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x.intDegree < y.intDegree) :
    x + y ≠ 0 ∧ (x + y).intDegree = y.intDegree := by
  have hne : x + y ≠ 0 := by
    intro hz
    have heq : x = -y := eq_neg_of_add_eq_zero_left hz
    have hd := congrArg RatFunc.intDegree heq
    rw [RatFunc.intDegree_neg] at hd
    omega
  refine ⟨hne, ?_⟩
  have hu := RatFunc.intDegree_add_le hy hne
  rw [max_eq_right (le_of_lt hxy)] at hu
  have hrearr : x + y + -x = y := by ring
  have hl := RatFunc.intDegree_add_le (neg_ne_zero.mpr hx)
    (show x + y + -x ≠ 0 by rwa [hrearr])
  rw [hrearr, RatFunc.intDegree_neg] at hl
  omega

theorem ratfunc_aeval_of_positive_intDegree (r : RatFunc K) (hr : 0 < r.intDegree)
    (p : K[X]) (hp : p ≠ 0) :
    aeval r p ≠ 0 ∧ (aeval r p).intDegree = (p.natDegree : ℤ) * r.intDegree := by
  have hr0 : r ≠ 0 := by intro hz; simp [hz] at hr
  have aux : ∀ N : ℕ, ∀ p : K[X], p.natDegree = N → p ≠ 0 →
      aeval r p ≠ 0 ∧ (aeval r p).intDegree = (p.natDegree : ℤ) * r.intDegree := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro p hpN hp
      let L : RatFunc K := RatFunc.C p.leadingCoeff * r ^ p.natDegree
      have hc : RatFunc.C p.leadingCoeff ≠ 0 := by
        exact (_root_.map_ne_zero (algebraMap K (RatFunc K))).mpr (leadingCoeff_ne_zero.mpr hp)
      have hL : L ≠ 0 := mul_ne_zero hc (pow_ne_zero _ hr0)
      have hLd : L.intDegree = (p.natDegree : ℤ) * r.intDegree := by
        dsimp [L]
        rw [RatFunc.intDegree_mul hc (pow_ne_zero _ hr0), ratfunc_intDegree_pow r hr0]
        simp
      have heval : aeval r p = aeval r p.eraseLead + L := by
        calc
          aeval r p = aeval r (p.eraseLead + C p.leadingCoeff * X ^ p.natDegree) :=
            congrArg (aeval r) p.eraseLead_add_C_mul_X_pow.symm
          _ = _ := by
            simp only [map_add, map_mul, aeval_C, map_pow, aeval_X, RatFunc.algebraMap_eq_C, L]
      by_cases hrest : p.eraseLead = 0
      · rw [heval, hrest, map_zero, zero_add]
        exact ⟨hL, hLd⟩
      · have hlt : p.eraseLead.natDegree < p.natDegree :=
          p.eraseLead_natDegree_lt_or_eraseLead_eq_zero.resolve_right hrest
        obtain ⟨hrne, hrd⟩ := ih p.eraseLead.natDegree (by omega) p.eraseLead rfl hrest
        have hdegrees : (aeval r p.eraseLead).intDegree < L.intDegree := by
          rw [hrd, hLd]
          exact mul_lt_mul_of_pos_right (by exact_mod_cast hlt) hr
        obtain ⟨hne, hd⟩ := ratfunc_add_of_intDegree_lt _ _ hrne hL hdegrees
        rw [heval]
        exact ⟨hne, hd.trans hLd⟩
  exact aux p.natDegree p rfl hp

theorem ratfunc_transcendental_of_positive_intDegree (r : RatFunc K)
    (hr : 0 < r.intDegree) : Transcendental K r := by
  apply transcendental_iff.mpr
  intro p hp
  by_contra hne
  exact (ratfunc_aeval_of_positive_intDegree r hr p hne).1 hp

theorem ratfunc_transcendental_of_intDegree_ne_zero (r : RatFunc K)
    (hr : r.intDegree ≠ 0) : Transcendental K r := by
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · have hi : Transcendental K r⁻¹ := ratfunc_transcendental_of_positive_intDegree _ (by
      rw [RatFunc.intDegree_inv]
      omega)
    intro ha
    exact hi ha.inv
  · exact ratfunc_transcendental_of_positive_intDegree r hpos

/-- Unequal numerator and denominator degrees certify the parameter condition
in the quadratic obstruction without any assumption on the field. -/
theorem rational_ratio_transcendental (A B : K[X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hdeg : A.natDegree ≠ B.natDegree) :
    Transcendental K (algebraMap K[X] (RatFunc K) A /
      algebraMap K[X] (RatFunc K) B) := by
  apply ratfunc_transcendental_of_intDegree_ne_zero
  rw [div_eq_mul_inv, RatFunc.intDegree_mul (RatFunc.algebraMap_ne_zero hA)
    (inv_ne_zero (RatFunc.algebraMap_ne_zero hB)), RatFunc.intDegree_inv,
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
  intro hz
  have heq : (A.natDegree : ℤ) = B.natDegree := by omega
  exact hdeg (by exact_mod_cast heq)

end WeightedPilz

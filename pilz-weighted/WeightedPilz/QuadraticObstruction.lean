import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
The universal quadratic remainder used in `lem:initial-quadratic`.
Its linear coefficient has constant coefficient one in every characteristic.
-/

noncomputable section
namespace WeightedPilz
open Polynomial

def quadraticRemainder (K : Type*) [CommRing K] : ℕ → K[X] × K[X]
  | 0 => (0, 1)
  | n + 1 => ((quadraticRemainder K n).1 + (quadraticRemainder K n).2,
      -X * (quadraticRemainder K n).1)

theorem quadraticRemainder_snd_eval_zero (K : Type*) [CommRing K] (n : ℕ) :
    (quadraticRemainder K (n + 1)).2.eval 0 = 0 := by
  simp [quadraticRemainder]

theorem quadraticRemainder_fst_eval_zero (K : Type*) [CommRing K] (n : ℕ) :
    (quadraticRemainder K (n + 1)).1.eval 0 = 1 := by
  induction n with
  | zero => simp [quadraticRemainder]
  | succ n ih =>
    change ((quadraticRemainder K (n + 1)).1 +
      (quadraticRemainder K (n + 1)).2).eval 0 = 1
    rw [eval_add, ih, quadraticRemainder_snd_eval_zero, add_zero]

theorem quadraticRemainder_fst_ne_zero (K : Type*) [CommRing K] [Nontrivial K]
    {n : ℕ} (hn : 0 < n) : (quadraticRemainder K n).1 ≠ 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  intro hz
  have h := quadraticRemainder_fst_eval_zero K m
  rw [hz, eval_zero] at h
  exact zero_ne_one h

def quadraticKernel {F : Type*} [CommRing F] (s : F) : F[X] := X ^ 2 - X + C s

theorem quadraticKernel_natDegree {F : Type*} [Field F] (s : F) :
    (quadraticKernel s).natDegree = 2 := by
  unfold quadraticKernel
  compute_degree <;> exact one_ne_zero

theorem quadraticKernel_dvd_power_sub_remainder {K F : Type*}
    [CommRing K] [CommRing F] [Algebra K F] (s : F) (n : ℕ) :
    quadraticKernel s ∣ X ^ n -
      (C (aeval s (quadraticRemainder K n).1) * X +
        C (aeval s (quadraticRemainder K n).2)) := by
  induction n with
  | zero => simp [quadraticRemainder]
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih
    let a := aeval s (quadraticRemainder K n).1
    let b := aeval s (quadraticRemainder K n).2
    have hX : (X : F[X]) ^ n = quadraticKernel s * T + (C a * X + C b) :=
      sub_eq_iff_eq_add.mp hT
    refine ⟨T * X + C a, ?_⟩
    simp only [quadraticRemainder, map_add, map_mul, map_neg, aeval_X]
    rw [pow_succ, hX]
    dsimp [a, b]
    unfold quadraticKernel
    ring

/-- A transcendental quadratic parameter prohibits a two-term multiple with
nonzero top coefficient, in every characteristic. -/
theorem transcendental_quadratic_not_dvd_binomial {K F : Type*}
    [Field K] [Field F] [Algebra K F] (s : F) (hs : Transcendental K s)
    (U V : F) (hV : V ≠ 0) {n : ℕ} (hn : 0 < n) :
    ¬ quadraticKernel s ∣ C U + C V * X ^ n := by
  intro hdiv
  let a := aeval s (quadraticRemainder K n).1
  let b := aeval s (quadraticRemainder K n).2
  have ha : a ≠ 0 := by
    intro hz
    exact quadraticRemainder_fst_ne_zero K hn ((transcendental_iff.mp hs) _ hz)
  have hrem := quadraticKernel_dvd_power_sub_remainder (K := K) s n
  have hlin : quadraticKernel s ∣ C U + C (V * a) * X + C (V * b) := by
    have hd := dvd_sub hdiv (dvd_mul_of_dvd_right hrem (C V))
    convert hd using 1
    simp only [map_mul]
    dsimp [a, b]
    ring
  have hdeg : (C U + C (V * a) * X + C (V * b)).natDegree ≤ 1 := by
    compute_degree
  have hz : (C U + C (V * a) * X + C (V * b) : F[X]) = 0 :=
    eq_zero_of_dvd_of_natDegree_lt hlin (by rw [quadraticKernel_natDegree]; omega)
  have hc := congrArg (fun P : F[X] => P.coeff 1) hz
  simp at hc
  exact hc.elim hV ha

/-- The normalized obstruction applies to an arbitrary quadratic after an
invertible scaling of its variable. -/
theorem quadratic_not_dvd_binomial_of_transcendental_ratio {K F : Type*}
    [Field K] [Field F] [Algebra K F] (A B D : F) (hB : B ≠ 0) (hD : D ≠ 0)
    (hs : Transcendental K (A * D / B ^ 2)) (U V : F) (hV : V ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    ¬ (C A + C B * X + C D * X ^ 2 : F[X]) ∣ C U + C V * X ^ n := by
  let t : F := -B / D
  let l : F := B ^ 2 / D
  let s : F := A * D / B ^ 2
  have ht : t ≠ 0 := div_ne_zero (neg_ne_zero.mpr hB) hD
  have hA : l * s = A := by dsimp [l, s]; field_simp [hB, hD]
  have hB' : B * t = -l := by dsimp [l, t]; field_simp [hD]
  have hD' : D * t ^ 2 = l := by dsimp [l, t]; field_simp [hD]
  let E : F[X] →+* F[X] := eval₂RingHom C (C t * X)
  have hEC (a : F) : E (C a) = C a := by simp [E, coe_eval₂RingHom]
  have hEX : E X = C t * X := by simp [E, coe_eval₂RingHom]
  have hquad : E (C A + C B * X + C D * X ^ 2) = C l * quadraticKernel s := by
    simp only [map_add, map_mul, map_pow, hEC, hEX]
    rw [mul_pow, ← map_pow]
    have hBt : C B * C t = (C (-l) : F[X]) := by rw [← map_mul, hB']
    have hDt : C D * C (t ^ 2) = (C l : F[X]) := by rw [← map_mul, hD']
    have hAs : C l * C s = (C A : F[X]) := by rw [← map_mul, hA]
    unfold quadraticKernel
    calc
      _ = C A + (C B * C t) * X + (C D * C (t ^ 2)) * X ^ 2 := by ring
      _ = C A + C (-l) * X + C l * X ^ 2 := by rw [hBt, hDt]
      _ = _ := by rw [map_neg, ← hAs]; ring
  have hbin : E (C U + C V * X ^ n) = C U + C (V * t ^ n) * X ^ n := by
    simp only [map_add, map_mul, map_pow, hEC, hEX, mul_pow]
    ring
  intro hdvd
  have hm := map_dvd E hdvd
  rw [hquad, hbin] at hm
  have hd : quadraticKernel s ∣ C U + C (V * t ^ n) * X ^ n :=
    dvd_trans (dvd_mul_left _ _) hm
  exact transcendental_quadratic_not_dvd_binomial s hs U (V * t ^ n)
    (mul_ne_zero hV (pow_ne_zero n ht)) hn hd

end WeightedPilz

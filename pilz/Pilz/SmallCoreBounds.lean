import Pilz.TwoRow
import Pilz.Endpoints3
import Pilz.SmallCases
import Pilz.FreshDistance

/-!
# The core bounds supplied by the quadratic two-row obstruction

The coefficient identity and the extra occupied row are proved in `TwoRow`.
Here the extra row is combined with the endpoint budgets, as in the paper.
-/

noncomputable section

namespace Pilz

open MvPolynomial

private theorem coordinateEquiv_X_self' (p : ℕ) :
    coordinateEquiv p (X p : Poly) = Polynomial.X := by
  simp [coordinateEquiv, optionEquivLeft_X_none]

private theorem coordinateEquiv_rename_subtype' (p : ℕ)
    (P : MvPolynomial {q : ℕ // q ≠ p} (ZMod 2)) :
    coordinateEquiv p (rename Subtype.val P) = Polynomial.C P := by
  have hh : ((coordinateEquiv p).toRingHom.comp
      (rename (Subtype.val : {q : ℕ // q ≠ p} → ℕ)).toRingHom) = Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [coordinateEquiv, optionEquivLeft_C]
    · intro q
      simp [coordinateEquiv, Equiv.optionSubtypeNe_symm_of_ne q.property,
        optionEquivLeft_X_some]
  exact RingHom.congr_fun hh P

/-- A failed quadratic coefficient identity adds one to the two endpoint
distance budgets. The coefficients may involve any variables except `p`. -/
theorem quadratic_core_distance (p : ℕ) (a b c : Poly)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hadegree : a.degreeOf p = 0) (hbdegree : b.degreeOf p = 0)
    (hcdegree : c.degreeOf p = 0) (hobs : a * c ≠ b ^ 2) :
    distance a + distance c + 1 ≤ distance (a + b * X p + c * X p ^ 2) := by
  let E := coordinateEquiv p
  let a₀ := (E a).coeff 0
  let b₀ := (E b).coeff 0
  let c₀ := (E c).coeff 0
  have hA : E a = Polynomial.C a₀ := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rw [natDegree_coordinateEquiv, hadegree]
  have hB : E b = Polynomial.C b₀ := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rw [natDegree_coordinateEquiv, hbdegree]
  have hC : E c = Polynomial.C c₀ := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rw [natDegree_coordinateEquiv, hcdegree]
  have hrecover (A : Poly) (A₀ : MvPolynomial {q : ℕ // q ≠ p} (ZMod 2))
      (hA : E A = Polynomial.C A₀) : rename Subtype.val A₀ = A := by
    apply E.injective
    rw [coordinateEquiv_rename_subtype']
    exact hA.symm
  have hA₀ : a₀ ≠ 0 := by
    intro hz
    apply ha
    rw [← hrecover a a₀ hA, hz, map_zero]
  have hB₀ : b₀ ≠ 0 := by
    intro hz
    apply hb
    rw [← hrecover b b₀ hB, hz, map_zero]
  have hC₀ : c₀ ≠ 0 := by
    intro hz
    apply hc
    rw [← hrecover c c₀ hC, hz, map_zero]
  have hobs₀ : a₀ * c₀ ≠ b₀ ^ 2 := by
    intro heq
    apply hobs
    rw [← hrecover a a₀ hA, ← hrecover b b₀ hB, ← hrecover c c₀ hC,
      ← map_mul, ← map_pow, heq]
  let P := a + b * X p + c * X p ^ 2
  have hQ : E P = TwoRow.quadratic a₀ b₀ c₀ := by
    dsimp [P]
    rw [map_add, map_add, map_mul, map_mul, map_pow,
      coordinateEquiv_X_self', hA, hB, hC]
    unfold TwoRow.quadratic
    ring
  have hdeg : (E P).natDegree = 2 := by
    rw [hQ, TwoRow.quadratic, Polynomial.natDegree_quadratic hC₀]
  have htrail : (E P).natTrailingDegree = 0 := by
    apply Polynomial.natTrailingDegree_eq_zero.mpr
    apply Or.inr
    simpa [hQ, TwoRow.quadratic] using hA₀
  have hspan : (E P).natTrailingDegree < (E P).natDegree := by omega
  have hrows : ∀ H : Poly, H ≠ 0 → 3 ≤ (E (P * H)).support.card := by
    intro H hH
    rw [map_mul, hQ]
    exact TwoRow.quadratic_three_le_rows a₀ b₀ c₀ hA₀ hB₀ hC₀ hobs₀
      (E H) (by simpa using hH)
  have hend := endpoint_distance_three p P hspan hrows
  change distance (E P).trailingCoeff + distance (E P).leadingCoeff + 1 ≤ distance P at hend
  have htc : (E P).trailingCoeff = a₀ := by
    rw [Polynomial.trailingCoeff, htrail, hQ]
    simp [TwoRow.quadratic]
  have hlc : (E P).leadingCoeff = c₀ := by
    rw [Polynomial.leadingCoeff, hdeg, hQ]
    simp [TwoRow.quadratic]
  have haDist : distance a ≤ distance a₀ := by
    rw [← hrecover a a₀ hA]
    exact distance_rename_le Subtype.val Subtype.val_injective a₀
  have hcDist : distance c ≤ distance c₀ := by
    rw [← hrecover c c₀ hC]
    exact distance_rename_le Subtype.val Subtype.val_injective c₀
  rw [htc, hlc] at hend
  exact (by omega : distance a + distance c + 1 ≤ distance P)

namespace SmallCore

private theorem degreeOf_cAt_eq_zero (p : ℕ) (x : Poly) (hx : x.degreeOf p = 0)
    (k : ℕ) : (cAt x k).degreeOf p = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold cAt
  refine (degreeOf_sum_le p _ _).trans ?_
  rw [Finset.sup_le_iff]
  intro i _hi
  exact (degreeOf_pow_le p x i).trans_eq (by rw [hx, mul_zero])

private theorem degreeOf_c_eq_zero (p k : ℕ) (hp : p ≠ 2) : (c k).degreeOf p = 0 := by
  exact degreeOf_cAt_eq_zero p (X 2) (by simp [degreeOf_X, hp]) k

private theorem c_ne_zero (k : ℕ) : c k ≠ 0 := by
  intro hz
  have h := congrArg constantCoeff hz
  simp [constantCoeff_c] at h

/-- The paper's bound four for `f₁₆`. -/
theorem f16_distance_four : 4 ≤ distance f16 := by
  have h := quadratic_core_distance 3 (c 4) (c 2) 1
    (c_ne_zero 4) (c_ne_zero 2) one_ne_zero
    (degreeOf_c_eq_zero 3 4 (by decide))
    (degreeOf_c_eq_zero 3 2 (by decide)) (degreeOf_C (1 : ZMod 2) 3)
    (by simpa using c4_ne_c2_square)
  have heq : c 4 + c 2 * X 3 + 1 * (X 3 : Poly) ^ 2 = f16 := by
    simp [f16, f16At, c]
  rw [heq, distance_one] at h
  have hlo := c_distance_lower 4 (by decide)
  omega

/-- The paper's bound six for `f₁₈`, including the final parity improvement. -/
theorem f18_distance_six : 6 ≤ distance f18 := by
  have h := quadratic_core_distance 3 (c 4) (c 2) (c 1)
    (c_ne_zero 4) (c_ne_zero 2) (c_ne_zero 1)
    (degreeOf_c_eq_zero 3 4 (by decide))
    (degreeOf_c_eq_zero 3 2 (by decide))
    (degreeOf_c_eq_zero 3 1 (by decide))
    (by simpa [mul_comm] using c1_mul_c4_ne_c2_square)
  have heq : c 4 + c 2 * X 3 + c 1 * (X 3 : Poly) ^ 2 = f18 := by
    simp [f18, f18At, c]
  rw [heq] at h
  have hlo := c_distance_lower 4 (by decide)
  have hhi := c_distance_lower 1 (by decide)
  obtain ⟨k, hk⟩ := even_distance_of_even_weight even_weight_f18
  omega

/-- The paper's bound five for `f₂₄`. -/
theorem f24_distance_five : 5 ≤ distance f24 := by
  have h := quadratic_core_distance 3 (c 4) (c 3) (c 1)
    (c_ne_zero 4) (c_ne_zero 3) (c_ne_zero 1)
    (degreeOf_c_eq_zero 3 4 (by decide))
    (degreeOf_c_eq_zero 3 3 (by decide))
    (degreeOf_c_eq_zero 3 1 (by decide))
    (by simpa [mul_comm] using c1_mul_c4_ne_c3_square)
  have heq : c 4 + c 3 * X 3 + c 1 * (X 3 : Poly) ^ 2 = f24 := by
    simp [f24, f24At, c]
  rw [heq] at h
  have hlo := c_distance_lower 4 (by decide)
  have hhi := c_distance_lower 1 (by decide)
  omega

private theorem degreeOf_add_eq_zero (p : ℕ) (P Q : Poly)
    (hP : P.degreeOf p = 0) (hQ : Q.degreeOf p = 0) : (P + Q).degreeOf p = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (degreeOf_add_le p P Q).trans_eq (by rw [hP, hQ]; rfl)

private theorem degreeOf_mul_eq_zero (p : ℕ) (P Q : Poly)
    (hP : P.degreeOf p = 0) (hQ : Q.degreeOf p = 0) : (P * Q).degreeOf p = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (degreeOf_mul_le p P Q).trans_eq (by rw [hP, hQ])

/-- The paper's bound eight for `f₂₅`, using the alternate quadratic form. -/
theorem f25_distance_eight : 8 ≤ distance f25 := by
  let A := f16At (X 2) (X 5)
  have hrename : renameEquiv (ZMod 2) (Equiv.swap 3 5) f16 = A := by
    simp [A, renameEquiv_apply, f16, f16At, cAt, Finset.sum_range_succ,
      Equiv.swap_apply_def]
  have hAdist : 4 ≤ distance A := by
    rw [← hrename, distance_renameEquiv]
    exact f16_distance_four
  have hA : A ≠ 0 := by
    intro hz
    rw [hz, distance_zero] at hAdist
    omega
  have hB : c 3 + X 5 ≠ 0 := by
    intro hz
    have h := congrArg constantCoeff hz
    simp [map_add, constantCoeff_c] at h
  have hx : (X 2 : Poly).degreeOf 3 = 0 := by simp [degreeOf_X]
  have hz : (X 5 : Poly).degreeOf 3 = 0 := by simp [degreeOf_X]
  have hAp : A.degreeOf 3 = 0 := by
    unfold A f16At
    apply degreeOf_add_eq_zero
    · apply degreeOf_add_eq_zero
      · exact degreeOf_cAt_eq_zero 3 (X 2) hx 4
      · exact degreeOf_mul_eq_zero 3 _ _ (degreeOf_cAt_eq_zero 3 (X 2) hx 2) hz
    · apply Nat.eq_zero_of_le_zero
      exact (degreeOf_pow_le 3 (X 5 : Poly) 2).trans_eq (by rw [hz, mul_zero])
  have hBp : (c 3 + X 5 : Poly).degreeOf 3 = 0 :=
    degreeOf_add_eq_zero 3 _ _ (degreeOf_c_eq_zero 3 3 (by decide)) hz
  have h := quadratic_core_distance 3 A (c 3 + X 5) (c 1)
    hA hB (c_ne_zero 1) hAp hBp (degreeOf_c_eq_zero 3 1 (by decide))
    (by simpa only [A, mul_comm] using f25_quadratic_obstruction)
  have heq : A + (c 3 + X 5) * X 3 + c 1 * (X 3 : Poly) ^ 2 = f25 := by
    simpa only [A, c, f25] using (f25_alternate_at (X 2) (X 3) (X 5)).symm
  rw [heq] at h
  have hhi := c_distance_lower 1 (by decide)
  obtain ⟨k, hk⟩ := even_distance_of_even_weight even_weight_f25
  omega

end SmallCore

end Pilz

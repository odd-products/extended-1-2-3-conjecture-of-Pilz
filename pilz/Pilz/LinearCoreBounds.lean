import Pilz.FreshDistance

/-! Adding a linear variable adds the distances of its endpoint coefficients. -/

noncomputable section

namespace Pilz

open MvPolynomial

private theorem coordinateEquiv_rename_subtype_linear (p : ℕ)
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

theorem coordinate_zero_recover (p : ℕ) (A : Poly) (hdegree : A.degreeOf p = 0) :
    rename (Subtype.val : {q : ℕ // q ≠ p} → ℕ) ((coordinateEquiv p A).coeff 0) = A := by
  have hconst : coordinateEquiv p A = Polynomial.C ((coordinateEquiv p A).coeff 0) := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rw [natDegree_coordinateEquiv, hdegree]
  apply (coordinateEquiv p).injective
  rw [coordinateEquiv_rename_subtype_linear]
  exact hconst.symm

/-- Endpoint slicing for a new linear variable with arbitrary independent
nonzero coefficients, as used in the paper's core-sum tables. -/
theorem linear_core_distance (p : ℕ) (a b : Poly) (ha : a ≠ 0) (hb : b ≠ 0)
    (hadegree : a.degreeOf p = 0) (hbdegree : b.degreeOf p = 0) :
    distance a + distance b ≤ distance (a + b * X p) := by
  let E := coordinateEquiv p
  let a₀ := (E a).coeff 0
  let b₀ := (E b).coeff 0
  have hA : E a = Polynomial.C a₀ := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rw [natDegree_coordinateEquiv, hadegree]
  have hB : E b = Polynomial.C b₀ := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rw [natDegree_coordinateEquiv, hbdegree]
  have hA₀ : a₀ ≠ 0 := by
    intro hz
    apply ha
    rw [← coordinate_zero_recover p a hadegree]
    change rename Subtype.val a₀ = 0
    rw [hz, map_zero]
  have hB₀ : b₀ ≠ 0 := by
    intro hz
    apply hb
    rw [← coordinate_zero_recover p b hbdegree]
    change rename Subtype.val b₀ = 0
    rw [hz, map_zero]
  let P := a + b * X p
  have hQ : E P = Polynomial.C a₀ + Polynomial.C b₀ * Polynomial.X := by
    dsimp [P]
    rw [map_add, map_mul, hA, hB]
    congr 2
    simp [E, coordinateEquiv, optionEquivLeft_X_none]
  have hdeg : (E P).natDegree = 1 := by
    rw [hQ, Polynomial.natDegree_C_add, Polynomial.natDegree_C_mul_X b₀ hB₀]
  have htrail : (E P).natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (by simpa [hQ] using hA₀))
  have hspan : (E P).natTrailingDegree < (E P).natDegree := by omega
  have hend := endpoint_distance p P hspan
  change distance (E P).trailingCoeff + distance (E P).leadingCoeff ≤ distance P at hend
  have htc : (E P).trailingCoeff = a₀ := by
    rw [Polynomial.trailingCoeff, htrail, hQ]
    simp
  have hlc : (E P).leadingCoeff = b₀ := by
    rw [Polynomial.leadingCoeff, hdeg, hQ]
    simp
  have haDist : distance a ≤ distance a₀ := by
    rw [← coordinate_zero_recover p a hadegree]
    exact distance_rename_le Subtype.val Subtype.val_injective a₀
  have hbDist : distance b ≤ distance b₀ := by
    rw [← coordinate_zero_recover p b hbdegree]
    exact distance_rename_le Subtype.val Subtype.val_injective b₀
  rw [htc, hlc] at hend
  exact (Nat.add_le_add haDist hbDist).trans hend

end Pilz

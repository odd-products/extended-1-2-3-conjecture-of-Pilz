import WeightedPilz.InitialExtension
import WeightedPilz.RepeatedEndpoints

/-! The two-row distance extension in the original named variables. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem binomial_core_extension_distance (p : ℕ) (S : Set ℕ)
    (R D : Poly K) (hR : R ≠ 0)
    (hRp : R.degreeOf p = 0) (hDp : D.degreeOf p = 0)
    (hDvars : (D.vars : Set ℕ) ⊆ S) (hD : 2 ≤ weight D)
    (hcop : IsRelPrime R D) (a : ℕ) (hbase : a ≤ distance R)
    (hpower : ∀ (k : ℕ), 0 < k → ∀ M : Poly K,
      M ≠ 0 → (M.vars : Set ℕ) ⊆ S → a < weight (R ^ k * M)) :
    a + 3 ≤ distance (R + D * X p) := by
  classical
  let E := coordinateEquiv (K := K) p
  let R₀ := (E R).coeff 0
  let D₀ := (E D).coeff 0
  let S₀ : Set {q : ℕ // q ≠ p} := {q | q.val ∈ S}
  have hER : E R = Polynomial.C R₀ := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rw [natDegree_coordinateEquiv, hRp]
  have hED : E D = Polynomial.C D₀ := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rw [natDegree_coordinateEquiv, hDp]
  have hRrename : rename Subtype.val R₀ = R := coordinate_zero_recover p R hRp
  have hDrename : rename Subtype.val D₀ = D := coordinate_zero_recover p D hDp
  have hR₀ : R₀ ≠ 0 := by intro hz; apply hR; rw [← hRrename, hz, map_zero]
  have hDweight : 2 ≤ weight D₀ := by
    rw [← hDrename, weight_rename_of_injective Subtype.val Subtype.val_injective] at hD
    exact hD
  have hDvars₀ : (D₀.vars : Set {q : ℕ // q ≠ p}) ⊆ S₀ := by
    intro q hq
    apply hDvars
    rw [← hDrename, vars_def, degrees_rename_of_injective Subtype.val_injective,
      Multiset.toFinset_map]
    exact Finset.mem_image.mpr ⟨q, by simpa only [vars_def] using hq, rfl⟩
  have hcop₀ : IsRelPrime R₀ D₀ := by
    intro T hTR hTD
    have hTR' : E.symm (Polynomial.C T) ∣ R := by
      have hh := map_dvd E.symm (map_dvd Polynomial.C hTR)
      simpa only [← hER, E.symm_apply_apply] using hh
    have hTD' : E.symm (Polynomial.C T) ∣ D := by
      have hh := map_dvd E.symm (map_dvd Polynomial.C hTD)
      simpa only [← hED, E.symm_apply_apply] using hh
    have hu := (hcop hTR' hTD').map E.toRingHom
    apply Polynomial.isUnit_C.mp
    change IsUnit (E (E.symm (Polynomial.C T))) at hu
    simpa only [E.apply_symm_apply] using hu
  have hbase₀ : a ≤ distance R₀ := by
    rw [← hRrename, distance_rename_of_injective Subtype.val Subtype.val_injective] at hbase
    exact hbase
  have hpower₀ : ∀ k, 0 < k → ∀ M : MvPolynomial {q : ℕ // q ≠ p} K,
      M ≠ 0 → (M.vars : Set {q : ℕ // q ≠ p}) ⊆ S₀ → a < weight (R₀ ^ k * M) := by
    intro k hk M hM hvars
    have hMn : rename (Subtype.val : {q : ℕ // q ≠ p} → ℕ) M ≠ 0 := by
      intro hz
      exact hM (rename_injective Subtype.val Subtype.val_injective (hz.trans (map_zero _).symm))
    have hMnvars : ((rename Subtype.val M).vars : Set ℕ) ⊆ S := by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := mem_vars_rename Subtype.val M hq
      exact hvars hr
    have h := hpower k hk (rename Subtype.val M) hMn hMnvars
    rw [← hRrename, ← map_pow, ← map_mul,
      weight_rename_of_injective Subtype.val Subtype.val_injective] at h
    exact h
  have h := binomial_extension_distance S₀ R₀ D₀ hR₀ hDvars₀ hDweight hcop₀ a hbase₀ hpower₀
  let V := renameEquiv K (Equiv.optionSubtypeNe p).symm
  have heq : (optionEquivLeft K {q : ℕ // q ≠ p}).symm
      (Polynomial.C R₀ + Polynomial.C D₀ * Polynomial.X) = V (R + D * X p) := by
    apply (optionEquivLeft K {q : ℕ // q ≠ p}).injective
    rw [AlgEquiv.apply_symm_apply]
    change _ = E (R + D * X p)
    rw [map_add, map_mul, hER, hED]
    congr 2
    simp [E, coordinateEquiv, optionEquivLeft_X_none]
  rw [heq, distance_renameEquiv] at h
  exact h

end WeightedPilz

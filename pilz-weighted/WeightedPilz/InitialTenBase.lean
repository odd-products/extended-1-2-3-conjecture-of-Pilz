import WeightedPilz.BivariatePowerMultiplier
import WeightedPilz.InitialTwoRows
import WeightedPilz.CoreNine

/-! The strengthened three-variable base for the tenth interval. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

def initialTenBase (A B D : Polynomial K) (d : K) :
    MvPolynomial (Option (Option PUnit.{1})) K :=
  (optionEquivLeft K (Option PUnit.{1})).symm
    (Polynomial.C (bivariateQuadratic A B (Polynomial.C d)) +
      Polynomial.C (rename some ((pUnitAlgEquiv.{_, 0} K).symm D)) * Polynomial.X)

@[simp] theorem optionEquiv_initialTenBase (A B D : Polynomial K) (d : K) :
    optionEquivLeft K (Option PUnit.{1}) (initialTenBase A B D d) =
      Polynomial.C (bivariateQuadratic A B (Polynomial.C d)) +
        Polynomial.C (rename some ((pUnitAlgEquiv.{_, 0} K).symm D)) * Polynomial.X :=
  (optionEquivLeft K (Option PUnit.{1})).apply_symm_apply _

theorem bivariateQuadratic_isRelPrime_univariate (A B D : Polynomial K) (d : K)
    (hd : d ≠ 0) (hD : D ≠ 0) :
    IsRelPrime (bivariateQuadratic A B (Polynomial.C d))
      (rename some ((pUnitAlgEquiv.{_, 0} K).symm D)) := by
  let U := pUnitAlgEquiv.{_, 0} K
  let E := optionEquivLeft K PUnit.{1}
  have hD' : U.symm D ≠ 0 := by
    intro hz
    exact hD (by simpa only [U.apply_symm_apply, map_zero] using congrArg U hz)
  have hcop := isRelPrime_constant_of_unit_coeff
    (E (bivariateQuadratic A B (Polynomial.C d))) (U.symm D) hD' 2 (by
      rw [optionEquiv_bivariateQuadratic]
      simpa [U, pUnitAlgEquiv_symm_apply] using hd)
  intro Q hQR hQD
  have hu : IsUnit (E Q) := hcop (map_dvd E hQR)
    (by simpa only [E, optionEquivLeft_rename_some] using map_dvd E hQD)
  have hback := hu.map E.symm.toMonoidHom
  change IsUnit (E.symm (E Q)) at hback
  simpa only [E.symm_apply_apply] using hback

theorem initialTenBase_distance_seven (A B D : Polynomial K) (d : K)
    (hd : d ≠ 0) (hA0 : A.coeff 0 ≠ 0) (hA1 : A.coeff 1 ≠ 0)
    (hAdeg : 2 ≤ A.natDegree) (hB0 : B.coeff 0 ≠ 0) (hB1 : B.coeff 1 ≠ 0)
    (hD0 : D.coeff 0 ≠ 0) (hD1 : D.coeff 1 ≠ 0)
    (hbase : 4 ≤ distance (bivariateQuadratic A B (Polynomial.C d))) :
    7 ≤ distance (initialTenBase A B D d) := by
  classical
  let U := pUnitAlgEquiv.{_, 0} K
  let R := bivariateQuadratic A B (Polynomial.C d)
  let V := rename some (U.symm D)
  have hR : R ≠ 0 := by
    intro hz
    change 4 ≤ distance R at hbase
    simp [hz, distance_zero] at hbase
  have hD : D ≠ 0 := fun hz => hD0 (by rw [hz, Polynomial.coeff_zero])
  have hvars : (V.vars : Set (Option PUnit.{1})) ⊆ Set.range some := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := mem_vars_rename some (U.symm D) hi
    exact ⟨j, rfl⟩
  have hV : 2 ≤ weight V := by
    rw [weight_rename_some]
    exact (distance_pUnit_symm_two D hD0 hD1).trans (distance_le_weight _)
  apply binomial_extension_distance (Set.range some) R V hR hvars hV
    (bivariateQuadratic_isRelPrime_univariate A B D d hd hD) 4 hbase
  intro k hk M hM hMv
  obtain ⟨N, hN⟩ := exists_rename_eq_of_vars_subset_range M some (Option.some_injective _) hMv
  have hN0 : N ≠ 0 := by intro hz; simp [hz] at hN; exact hM hN.symm
  rw [← hN]
  have h := bivariateQuadratic_constant_power_mul A B d hd hA0 hA1 hAdeg hB0 hB1 N hN0 hk
  exact (by decide : 4 < 6).trans_le h

theorem initialTenBase_small_multiple_rows (A B D : Polynomial K) (d : K)
    (hd : d ≠ 0) (hA0 : A.coeff 0 ≠ 0) (hA1 : A.coeff 1 ≠ 0)
    (hAdeg : 2 ≤ A.natDegree) (hB0 : B.coeff 0 ≠ 0) (hB1 : B.coeff 1 ≠ 0)
    (hD0 : D.coeff 0 ≠ 0) (hD1 : D.coeff 1 ≠ 0)
    (hbase : 4 ≤ distance (bivariateQuadratic A B (Polynomial.C d)))
    (G : MvPolynomial (Option (Option PUnit.{1})) K) (hG : G ≠ 0)
    (hdiv : initialTenBase A B D d ∣ G) (hw : weight G ≤ 7) :
    3 ≤ (optionEquivLeft K (Option PUnit.{1}) G).support.card := by
  classical
  let U := pUnitAlgEquiv.{_, 0} K
  let R := bivariateQuadratic A B (Polynomial.C d)
  let V := rename some (U.symm D)
  have hR : R ≠ 0 := by
    intro hz
    change 4 ≤ distance R at hbase
    simp [hz, distance_zero] at hbase
  have hD : D ≠ 0 := fun hz => hD0 (by rw [hz, Polynomial.coeff_zero])
  have hvars : (V.vars : Set (Option PUnit.{1})) ⊆ Set.range some := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := mem_vars_rename some (U.symm D) hi
    exact ⟨j, rfl⟩
  have hV : 2 ≤ weight V := by
    rw [weight_rename_some]
    exact (distance_pUnit_symm_two D hD0 hD1).trans (distance_le_weight _)
  have hpower (k : ℕ) (hk : 0 < k) (M : MvPolynomial (Option PUnit.{1}) K)
      (hM : M ≠ 0) (hMv : (M.vars : Set (Option PUnit.{1})) ⊆ Set.range some) :
      6 ≤ weight (R ^ k * M) := by
    obtain ⟨N, hN⟩ := exists_rename_eq_of_vars_subset_range M some (Option.some_injective _) hMv
    have hN0 : N ≠ 0 := by intro hz; simp [hz] at hN; exact hM hN.symm
    rw [← hN]
    exact bivariateQuadratic_constant_power_mul A B d hd hA0 hA1 hAdeg hB0 hB1 N hN0 hk
  apply small_linear_multiple_three_rows (Set.range some) R V hR hvars hV
    (bivariateQuadratic_isRelPrime_univariate A B D d hd hD) 4 6 hbase
    hpower G hG ?_ hw (by omega)
  simpa only [optionEquiv_initialTenBase] using map_dvd (optionEquivLeft K (Option PUnit.{1})) hdiv

end WeightedPilz


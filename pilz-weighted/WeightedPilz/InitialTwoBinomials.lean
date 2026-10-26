import WeightedPilz.InitialTenBase
import WeightedPilz.LinearExtensionOps

/-! Two successive binomial extensions of a quadratic base. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem initialTenBase_linearExtension (A B D : Polynomial K) (d : K) :
    initialTenBase A B D d = linearExtension (bivariateQuadratic A B (Polynomial.C d))
      (rename some ((pUnitAlgEquiv.{_, 0} K).symm D)) := by
  rw [linearExtension_eq_symm]
  rfl

theorem initialTenBase_power_mul_eight (A B D : Polynomial K) (d : K)
    (hd : d ≠ 0) (hA0 : A.coeff 0 ≠ 0) (hA1 : A.coeff 1 ≠ 0)
    (hAdeg : 2 ≤ A.natDegree) (hB0 : B.coeff 0 ≠ 0) (hB1 : B.coeff 1 ≠ 0)
    (hD0 : D.coeff 0 ≠ 0) (hD1 : D.coeff 1 ≠ 0)
    (M : MvPolynomial PUnit.{1} K) (hM : M ≠ 0) {n : ℕ} (hn : 0 < n) :
    8 ≤ weight (initialTenBase A B D d ^ n * rename (some ∘ some) M) := by
  let U := pUnitAlgEquiv.{_, 0} K
  let V := rename some (U.symm D)
  have hD : D ≠ 0 := fun hz => hD0 (by rw [hz, Polynomial.coeff_zero])
  have hDne : U.symm D ≠ 0 := by
    intro hz
    exact hD (by simpa only [U.apply_symm_apply, map_zero] using congrArg U hz)
  have hV : V ≠ 0 := by
    intro hz
    have h := congrArg (optionEquivLeft K PUnit.{1}) hz
    rw [optionEquivLeft_rename_some, map_zero] at h
    exact hDne (Polynomial.C_eq_zero.mp h)
  have hlo := bivariateQuadratic_constant_power_mul A B d hd hA0 hA1 hAdeg hB0 hB1 M hM hn
  have hhi : 2 ≤ weight (V ^ n * rename some M) := by
    have h := (distance_pUnit_symm_two D hD0 hD1).trans
      (distance_le_weight_mul (U.symm D) ((U.symm D) ^ (n - 1) * M)
        (mul_ne_zero (pow_ne_zero _ hDne) hM))
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn] at h
    simpa only [V, ← map_pow, ← map_mul, weight_rename_some] using h
  have hs := linearExtension_power_mul_endpoints
    (bivariateQuadratic A B (Polynomial.C d)) V hV (rename some M) hn
  rw [initialTenBase_linearExtension, ← rename_rename]
  change 8 ≤ weight (linearExtension (bivariateQuadratic A B (Polynomial.C d)) V ^ n *
    rename some (rename some M))
  omega

def doubleBinomialBase (A B D E : Polynomial K) (d : K) :
    MvPolynomial (Option (Option (Option PUnit.{1}))) K :=
  linearExtension (initialTenBase A B D d)
    (rename (some ∘ some) ((pUnitAlgEquiv.{_, 0} K).symm E))

theorem doubleBinomialBase_distance_ten (A B D E : Polynomial K) (d : K)
    (hd : d ≠ 0) (hA0 : A.coeff 0 ≠ 0) (hA1 : A.coeff 1 ≠ 0)
    (hAdeg : 2 ≤ A.natDegree) (hB0 : B.coeff 0 ≠ 0) (hB1 : B.coeff 1 ≠ 0)
    (hD0 : D.coeff 0 ≠ 0) (hD1 : D.coeff 1 ≠ 0)
    (hE0 : E.coeff 0 ≠ 0) (hE1 : E.coeff 1 ≠ 0)
    (hbase : 4 ≤ distance (bivariateQuadratic A B (Polynomial.C d))) :
    10 ≤ distance (doubleBinomialBase A B D E d) := by
  classical
  let U := pUnitAlgEquiv.{_, 0} K
  let R := initialTenBase A B D d
  let V := rename (some ∘ some) (U.symm E)
  let f : PUnit.{1} → Option (Option PUnit.{1}) := some ∘ some
  have hf : Function.Injective f := fun _ _ h => Option.some.inj (Option.some.inj h)
  have hE : E ≠ 0 := fun hz => hE0 (by rw [hz, Polynomial.coeff_zero])
  have hEne : U.symm E ≠ 0 := by
    intro hz
    exact hE (by simpa only [U.apply_symm_apply, map_zero] using congrArg U hz)
  have hVbase : rename some (U.symm E) ≠ 0 := by
    intro hz
    have h := congrArg (optionEquivLeft K PUnit.{1}) hz
    rw [optionEquivLeft_rename_some, map_zero] at h
    exact hEne (Polynomial.C_eq_zero.mp h)
  have hRdist : 7 ≤ distance R := initialTenBase_distance_seven A B D d hd hA0 hA1 hAdeg
    hB0 hB1 hD0 hD1 hbase
  have hR : R ≠ 0 := by intro hz; simp [hz, distance_zero] at hRdist
  have hVvars : (V.vars : Set (Option (Option PUnit.{1}))) ⊆ Set.range f := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := mem_vars_rename f (U.symm E) hi
    exact ⟨j, rfl⟩
  have hVweight : 2 ≤ weight V := by
    rw [weight_rename_of_injective f hf]
    exact (distance_pUnit_symm_two E hE0 hE1).trans (distance_le_weight _)
  have hcop : IsRelPrime R V := by
    rw [show R = linearExtension (bivariateQuadratic A B (Polynomial.C d))
        (rename some (U.symm D)) from initialTenBase_linearExtension A B D d]
    change IsRelPrime _ (rename (some ∘ some) (U.symm E))
    rw [← rename_rename]
    exact linearExtension_isRelPrime_of_base _ _ _ hVbase
      (bivariateQuadratic_isRelPrime_univariate A B E d hd hE)
  rw [doubleBinomialBase, linearExtension_eq_symm]
  apply binomial_extension_distance (Set.range f) R V hR hVvars hVweight hcop 7 hRdist
  intro k hk M hM hvars
  obtain ⟨N, hN⟩ := exists_rename_eq_of_vars_subset_range M f hf hvars
  have hN0 : N ≠ 0 := by intro hz; simp [hz] at hN; exact hM hN.symm
  rw [← hN]
  have h := initialTenBase_power_mul_eight A B D d hd hA0 hA1 hAdeg
    hB0 hB1 hD0 hD1 N hN0 hk
  exact lt_of_lt_of_le (by decide : 7 < 8) h

end WeightedPilz

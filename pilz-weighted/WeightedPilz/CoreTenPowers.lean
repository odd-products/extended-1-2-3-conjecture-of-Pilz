import WeightedPilz.CoreTen
import WeightedPilz.CoordinateZero
import WeightedPilz.LinearExtensionOps
import WeightedPilz.CoreNinePowers
import WeightedPilz.LinearPowerThreeRows

/-! Power and binomial bounds for the tenth core. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem coreTenTemplate_eq_linearExtension (c : ℕ → K) :
    coreTenTemplate c = linearExtension
      (bivariateQuadratic (coreNineBottom c) (coreNineMiddle c) (Polynomial.C (c 9)))
      (rename some ((pUnitAlgEquiv.{_, 0} K).symm (coreTenLinear c))) := by
  rw [linearExtension_eq_symm]
  rfl

theorem coreTenTemplate_coordinateZero_power (c : ℕ → K) (hc : NonzeroWeights 10 c)
    {n : ℕ} (hn : 0 < n) (j : Option (Option PUnit.{1})) :
    4 ≤ weight (coordinateZero j (coreTenTemplate c ^ n)) := by
  classical
  let U := pUnitAlgEquiv.{_, 0} K
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 10) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  rw [map_pow]
  cases j with
  | none =>
    have heq : coordinateZero none (coreTenTemplate c) =
        rename some (bivariateQuadratic (coreNineBottom c) (coreNineMiddle c) (Polynomial.C (c 9))) := by
      rw [coreTenTemplate_expansion, bivariateQuadratic_coreNine]
      simp
    rw [heq, ← map_pow, weight_rename_some]
    have hc9 : NonzeroWeights 9 c := by
      intro a ha
      exact hnz a (by have h := Finset.mem_Icc.mp ha; omega)
    have h := intervalCore_nine_power_six c hc9 hn
    rw [intervalCore_nine_rename, ← map_pow,
      weight_rename_of_injective coreNineVariables coreNineVariables_injective] at h
    omega
  | some j =>
    cases j with
    | none =>
      let f : Option PUnit.{1} → Option (Option PUnit.{1})
        | none => none
        | some _ => some (some ())
      have hf : Function.Injective f := by
        intro a b h
        cases a <;> cases b <;> simp_all [f]
      have heq : coordinateZero (some none) (coreTenTemplate c) =
          rename f (linearExtension (U.symm (coreNineBottom c)) (U.symm (coreTenLinear c))) := by
        rw [coreTenTemplate_expansion]
        simp [linearExtension, coreNineBottom, coreTenLinear, U, pUnitAlgEquiv_symm_apply, f]
      rw [heq, ← map_pow, weight_rename_of_injective f hf]
      have hA0 : (coreNineBottom c).coeff 0 ≠ 0 := by simpa [coreNineBottom] using hnz 1 (by omega)
      have hA1 : (coreNineBottom c).coeff 1 ≠ 0 := by simpa [coreNineBottom] using hnz 2 (by omega)
      have hdeg : (coreNineBottom c).natDegree = 3 := by
        dsimp [coreNineBottom]
        compute_degree <;> first | exact hnz 8 (by omega) | decide
      have hA := univariate_power_weight_three_all (coreNineBottom c) hA0 hA1 (by omega) hn
      have hD0 : U.symm (coreTenLinear c) ≠ 0 := by
        intro hz
        have h := congrArg (fun P => (U P).coeff 0) hz
        exact hnz 5 (by omega) (by simpa [coreTenLinear] using h)
      have hDdist := distance_pUnit_symm_two (coreTenLinear c)
        (by simpa [coreTenLinear] using hnz 5 (by omega))
        (by simpa [coreTenLinear] using hnz 10 (by omega))
      have hD : 2 ≤ weight ((U.symm (coreTenLinear c)) ^ n) := by
        have h := hDdist.trans (distance_le_weight_mul (U.symm (coreTenLinear c))
          ((U.symm (coreTenLinear c)) ^ (n - 1)) (pow_ne_zero _ hD0))
        rw [← pow_succ', Nat.sub_add_cancel hn] at h
        exact h
      have h := linearExtension_power_endpoints (U.symm (coreNineBottom c))
        (U.symm (coreTenLinear c)) hD0 hn
      dsimp only [U] at hD h ⊢
      omega
    | some j =>
      cases j
      let Q : Polynomial K := Polynomial.C (c 1) + Polynomial.C (c 3) * Polynomial.X +
        Polynomial.C (c 9) * Polynomial.X ^ 2
      let f : Option PUnit.{1} → Option (Option PUnit.{1})
        | none => none
        | some _ => some none
      have hf : Function.Injective f := by
        intro a b h
        cases a <;> cases b <;> simp_all [f]
      have heq : coordinateZero (some (some ())) (coreTenTemplate c) =
          rename f (linearExtension (U.symm Q) (C (c 5))) := by
        rw [coreTenTemplate_expansion]
        simp [linearExtension, Q, U, pUnitAlgEquiv_symm_apply, f]
      rw [heq, ← map_pow, weight_rename_of_injective f hf]
      have hQ0 : Q.coeff 0 ≠ 0 := by simpa [Q] using hnz 1 (by omega)
      have hQ1 : Q.coeff 1 ≠ 0 := by simpa [Q] using hnz 3 (by omega)
      have hdeg : Q.natDegree = 2 := by
        dsimp [Q]
        compute_degree <;> first | exact hnz 9 (by omega) | decide
      have hQ := univariate_power_weight_three_all Q hQ0 hQ1 (by omega) hn
      have hD : (C (c 5) : MvPolynomial PUnit.{1} K) ≠ 0 := C_ne_zero.mpr (hnz 5 (by omega))
      have hwD : weight ((C (c 5) : MvPolynomial PUnit.{1} K) ^ n) = 1 := by
        rw [← map_pow]
        change (monomial 0 (c 5 ^ n) : MvPolynomial PUnit.{1} K).support.card = 1
        rw [support_monomial, if_neg (pow_ne_zero n (hnz 5 (by omega))), Finset.card_singleton]
      have h := linearExtension_power_endpoints (U.symm Q) (C (c 5)) hD hn
      dsimp only [U] at h ⊢
      omega

theorem coreTenTemplate_power_binomial_eight (c : ℕ → K) (hc : NonzeroWeights 10 c)
    {n : ℕ} (hn : 0 < n) (B : MvPolynomial (Option (Option PUnit.{1})) K)
    (hB : weight B = 2) : 8 ≤ weight (coreTenTemplate c ^ n * B) := by
  exact weight_mul_binomial_of_all_coordinateZero _ 4
    (coreTenTemplate_coordinateZero_power c hc hn) B hB

theorem coreTenTemplate_power_nine (c : ℕ → K) (hc : NonzeroWeights 10 c)
    {n : ℕ} (hn : 0 < n) : 9 ≤ weight (coreTenTemplate c ^ n) := by
  let U := pUnitAlgEquiv.{_, 0} K
  let R := bivariateQuadratic (coreNineBottom c) (coreNineMiddle c) (Polynomial.C (c 9))
  let D := rename some (U.symm (coreTenLinear c))
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 10) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  have hc9 : NonzeroWeights 9 c := by
    intro a ha
    exact hnz a (by have h := Finset.mem_Icc.mp ha; omega)
  have hbase := intervalCore_nine_distance_four c hc9
  rw [intervalCore_nine_rename, distance_rename_of_injective coreNineVariables coreNineVariables_injective] at hbase
  have hDdist : 2 ≤ distance D := by
    rw [distance_rename_of_injective some (Option.some_injective _)]
    exact distance_pUnit_symm_two (coreTenLinear c)
      (by simpa [coreTenLinear] using hnz 5 (by omega))
      (by simpa [coreTenLinear] using hnz 10 (by omega))
  have hD : D ≠ 0 := by intro hz; simp [hz, distance_zero] at hDdist
  have hRpower (k : ℕ) (hk : 0 < k) : 6 ≤ weight (R ^ k) := by
    have h := intervalCore_nine_power_six c hc9 hk
    rw [intervalCore_nine_rename, ← map_pow,
      weight_rename_of_injective coreNineVariables coreNineVariables_injective] at h
    exact h
  rw [coreTenTemplate_eq_linearExtension]
  apply linearExtension_power_nine R D hD hbase hDdist hRpower _ hn
  rw [← coreTenTemplate_eq_linearExtension]
  exact le_of_eq (coreTenTemplate_weight c hc).symm

end WeightedPilz

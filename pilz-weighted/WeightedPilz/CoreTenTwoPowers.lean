import WeightedPilz.CoreTenPowers
import WeightedPilz.ShiftedLinearTwoPowers

/-! The final two-power exclusion for the actual weighted tenth core. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem coreTenTemplate_two_powers_eight (c : ℕ → K) (hc : NonzeroWeights 10 c)
    (M N : MvPolynomial (Option (Option PUnit.{1})) K) (hM : weight M = 1) (hN : weight N = 1)
    {i j : ℕ} (hi : 0 < i) (hij : i < j)
    (hG : M * coreTenTemplate c ^ i + N * coreTenTemplate c ^ j ≠ 0) :
    8 ≤ weight (M * coreTenTemplate c ^ i + N * coreTenTemplate c ^ j) := by
  classical
  let U := pUnitAlgEquiv.{_, 0} K
  let R := bivariateQuadratic (coreNineBottom c) (coreNineMiddle c) (Polynomial.C (c 9))
  let D := rename some (U.symm (coreTenLinear c))
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 10) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  have hc9 : NonzeroWeights 9 c := by
    intro a ha
    exact hnz a (by have h := Finset.mem_Icc.mp ha; omega)
  have hRd : 4 ≤ distance R := by
    have h := intervalCore_nine_distance_four c hc9
    rw [intervalCore_nine_rename, distance_rename_of_injective coreNineVariables coreNineVariables_injective] at h
    exact h
  have hR : R ≠ 0 := by intro hz; simp [hz, distance_zero] at hRd
  have hD0 : (coreTenLinear c).coeff 0 ≠ 0 := by simpa [coreTenLinear] using hnz 5 (by omega)
  have hD1 : (coreTenLinear c).coeff 1 ≠ 0 := by simpa [coreTenLinear] using hnz 10 (by omega)
  have hDd : 2 ≤ distance D := by
    rw [distance_rename_of_injective some (Option.some_injective _)]
    exact distance_pUnit_symm_two (coreTenLinear c) hD0 hD1
  have hD : D ≠ 0 := by intro hz; simp [hz, distance_zero] at hDd
  have hRpower (k : ℕ) (hk : 0 < k) : 6 ≤ weight (R ^ k) := by
    have h := intervalCore_nine_power_six c hc9 hk
    rw [intervalCore_nine_rename, ← map_pow,
      weight_rename_of_injective coreNineVariables coreNineVariables_injective] at h
    exact h
  have hDdeg : (coreTenLinear c).natDegree = 1 := by
    dsimp [coreTenLinear]
    compute_degree <;> first | exact hnz 10 (by omega) | decide
  have hDpower (k : ℕ) (hk : 0 < k) (hw : weight (D ^ k) ≤ 2) :
      ∃ e : ℕ, k = ringExpChar K ^ e := by
    change weight ((rename some (U.symm (coreTenLinear c))) ^ k) ≤ 2 at hw
    rw [← map_pow, weight_rename_some] at hw
    exact distinguished_of_univariate_linear_power_two (coreTenLinear c) hD0 hD1 hDdeg
      (ringExpChar K) hk hw
  have hA0 : (coreNineBottom c).coeff 0 ≠ 0 := by simpa [coreNineBottom] using hnz 1 (by omega)
  have hA1 : (coreNineBottom c).coeff 1 ≠ 0 := by simpa [coreNineBottom] using hnz 2 (by omega)
  have hB0 : (coreNineMiddle c).coeff 0 ≠ 0 := by simpa [coreNineMiddle] using hnz 3 (by omega)
  have hB1 : (coreNineMiddle c).coeff 1 ≠ 0 := by simpa [coreNineMiddle] using hnz 6 (by omega)
  have hAdeg : (coreNineBottom c).natDegree = 3 := by
    dsimp [coreNineBottom]
    compute_degree <;> first | exact hnz 8 (by omega) | decide
  have hrows (G : MvPolynomial (Option (Option PUnit.{1})) K) (hG : G ≠ 0)
      (hdiv : linearExtension R D ∣ G) (hw : weight G ≤ 7) :
      3 ≤ (optionEquivLeft K (Option PUnit.{1}) G).support.card := by
    have heq : coreTenTemplate c = linearExtension R D := coreTenTemplate_eq_linearExtension c
    rw [← heq] at hdiv
    exact initialTenBase_small_multiple_rows _ _ _ _ (hnz 9 (by omega)) hA0 hA1
      (by omega) hB0 hB1 hD0 hD1 hRd G hG hdiv hw
  rw [coreTenTemplate_eq_linearExtension] at hG ⊢
  exact linearExtension_two_monomial_powers_eight R D hR hD hRd hDd hRpower
    (ringExpChar K) hDpower hrows M N hM hN hi hij hG

end WeightedPilz

import WeightedPilz.InitialTwelve
import WeightedPilz.InitialTwoBinomials

/-! The fourteenth interval follows from two binomial extensions and completion. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

def coreFourteenSeven (c : ℕ → K) : Polynomial K :=
  Polynomial.C (c 7) + Polynomial.C (c 14) * Polynomial.X

def coreFourteenVariables : Option (Option (Option PUnit.{1})) → ℕ
  | none => 7
  | some a => coreTwelveVariables a

theorem coreFourteenVariables_injective : Function.Injective coreFourteenVariables := by
  intro a b hab
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases b with
      | none => simp [coreFourteenVariables, coreTwelveVariables] at hab
      | some b => cases b <;>
          simp [coreFourteenVariables, coreTwelveVariables, coreNineVariables] at hab
  | some a => cases b with
    | none => cases a with
      | none => simp [coreFourteenVariables, coreTwelveVariables] at hab
      | some a => cases a <;>
          simp [coreFourteenVariables, coreTwelveVariables, coreNineVariables] at hab
    | some b => exact congrArg some (coreTwelveVariables_injective hab)

theorem intervalCore_fourteen_rename (c : ℕ → K) :
    intervalCore 14 c = rename coreFourteenVariables
      (doubleBinomialBase (coreNineBottom c) (coreTwelveMiddle c)
        (coreTwelveFive c) (coreFourteenSeven c) (c 9)) := by
  rw [intervalCore_fourteen_decomposition,
    ← intervalCore_twelve_decomposition 12 (by decide) (by decide),
    doubleBinomialBase]
  simp only [linearExtension, map_add, map_mul, rename_X, rename_rename]
  change intervalCore 12 c + arithmeticBinomial 7 c * X 7 =
    rename coreTwelveVariables
      (initialTenBase (coreNineBottom c) (coreTwelveMiddle c) (coreTwelveFive c) (c 9)) +
    rename (coreFourteenVariables ∘ some ∘ (some ∘ some))
      ((pUnitAlgEquiv.{_, 0} K).symm (coreFourteenSeven c)) * X 7
  rw [← intervalCore_twelve_rename]
  congr 2
  simp [arithmeticBinomial, coreFourteenSeven, pUnitAlgEquiv_symm_apply,
    coreFourteenVariables, coreTwelveVariables, coreNineVariables]

theorem intervalCore_fourteen_distance_ten (c : ℕ → K) (hc : NonzeroWeights 14 c) :
    10 ≤ distance (intervalCore 14 c) := by
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 14) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  have hc12 : NonzeroWeights 12 c := by
    intro a ha
    exact hnz a (by have := Finset.mem_Icc.mp ha; omega)
  have hbase := baseTwelve_distance_four c hc12
  rw [baseTwelve, distance_rename_of_injective coreNineVariables coreNineVariables_injective] at hbase
  have hdegA : (coreNineBottom c).natDegree = 3 := by
    dsimp [coreNineBottom]
    compute_degree <;> first | exact hnz 8 (by omega) | decide
  have h := doubleBinomialBase_distance_ten (coreNineBottom c) (coreTwelveMiddle c)
    (coreTwelveFive c) (coreFourteenSeven c) (c 9) (hnz 9 (by omega))
    (by simpa [coreNineBottom] using hnz 1 (by omega))
    (by simpa [coreNineBottom] using hnz 2 (by omega)) (by omega)
    (by simpa [coreTwelveMiddle] using hnz 3 (by omega))
    (by simpa [coreTwelveMiddle] using hnz 6 (by omega))
    (by simpa [coreTwelveFive] using hnz 5 (by omega))
    (by simpa [coreTwelveFive] using hnz 10 (by omega))
    (by simpa [coreFourteenSeven] using hnz 7 (by omega))
    (by simpa [coreFourteenSeven] using hnz 14 (by omega)) hbase
  rw [intervalCore_fourteen_rename,
    distance_rename_of_injective coreFourteenVariables coreFourteenVariables_injective]
  exact h

theorem intervalBound_fourteen (c : ℕ → K) (hc : NonzeroWeights 14 c) : IntervalBound 14 c := by
  have h := intervalCore_fourteen_distance_ten c hc
  apply intervalBound_of_core_distance 14 c (by decide) hc (by decide)
  have hr : (intervalFreshPrimes 14).card = 2 := by decide
  rw [hr]
  omega

end WeightedPilz

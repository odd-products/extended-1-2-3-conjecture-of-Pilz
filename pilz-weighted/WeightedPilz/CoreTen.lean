import WeightedPilz.InitialTenBase

/-! Exact coefficient and variable identifications for the tenth core. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

def coreTenLinear (c : ℕ → K) : Polynomial K :=
  Polynomial.C (c 5) + Polynomial.C (c 10) * Polynomial.X

def coreTenTemplate (c : ℕ → K) : MvPolynomial (Option (Option PUnit.{1})) K :=
  initialTenBase (coreNineBottom c) (coreNineMiddle c) (coreTenLinear c) (c 9)

def coreTenVariables : Option (Option PUnit.{1}) → ℕ
  | none => 5
  | some none => 3
  | some (some _) => 2

theorem coreTenVariables_injective : Function.Injective coreTenVariables := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => cases b <;> simp_all [coreTenVariables]
  | some a =>
    cases b with
    | none => cases a <;> simp_all [coreTenVariables]
    | some b => cases a <;> cases b <;> simp_all [coreTenVariables]

theorem coreTenTemplate_expansion (c : ℕ → K) :
    coreTenTemplate c =
      C (c 1) + C (c 2) * X (some (some ())) +
      C (c 4) * X (some (some ())) ^ 2 + C (c 8) * X (some (some ())) ^ 3 +
      (C (c 3) + C (c 6) * X (some (some ()))) * X (some none) +
      C (c 9) * X (some none) ^ 2 +
      (C (c 5) + C (c 10) * X (some (some ()))) * X none := by
  apply (optionEquivLeft K (Option PUnit.{1})).injective
  simp [coreTenTemplate, optionEquiv_initialTenBase, bivariateQuadratic_coreNine,
    coreTenLinear, pUnitAlgEquiv_symm_apply, optionEquivLeft_C,
    optionEquivLeft_X_some, optionEquivLeft_X_none]

theorem intervalCore_ten_rename (c : ℕ → K) :
    intervalCore 10 c = rename coreTenVariables (coreTenTemplate c) := by
  have hset : Finset.Icc 1 10 \ intervalFreshPrimes 10 = {1, 2, 3, 4, 5, 6, 8, 9, 10} := by
    decide
  have h2 : (2 : ℕ).factorization = Finsupp.single 2 1 := Nat.prime_two.factorization
  have h3 : (3 : ℕ).factorization = Finsupp.single 3 1 :=
    (by decide : Nat.Prime 3).factorization
  have h5 : (5 : ℕ).factorization = Finsupp.single 5 1 :=
    (by decide : Nat.Prime 5).factorization
  have h4 : (4 : ℕ).factorization = Finsupp.single 2 2 := by
    simpa using Nat.prime_two.factorization_pow (k := 2)
  have h6 : (6 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 3 1 := by
    change (2 * 3 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h3]
  have h8 : (8 : ℕ).factorization = Finsupp.single 2 3 := by
    simpa using Nat.prime_two.factorization_pow (k := 3)
  have h9 : (9 : ℕ).factorization = Finsupp.single 3 2 := by
    simpa using (by decide : Nat.Prime 3).factorization_pow (k := 2)
  have h10 : (10 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 5 1 := by
    change (2 * 5 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h5]
  rw [coreTenTemplate_expansion]
  simp [intervalCore, polynomialOf, hset, h2, h3, h4, h5, h6, h8, h9, h10,
    ← C_apply, ← C_mul_X_pow_eq_monomial, monomial_add_single, coreTenVariables] <;> ring

theorem coreTenTemplate_weight (c : ℕ → K) (hc : NonzeroWeights 10 c) :
    weight (coreTenTemplate c) = 9 := by
  rw [← weight_rename_of_injective coreTenVariables coreTenVariables_injective,
    ← intervalCore_ten_rename, weight_intervalCore 10 c hc]
  decide

theorem coreTenTemplate_distance_seven (c : ℕ → K) (hc : NonzeroWeights 10 c) :
    7 ≤ distance (coreTenTemplate c) := by
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 10) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  have hc9 : NonzeroWeights 9 c := by
    intro a ha
    exact hnz a (by have h := Finset.mem_Icc.mp ha; omega)
  have hbase := intervalCore_nine_distance_four c hc9
  rw [intervalCore_nine_rename, distance_rename_of_injective coreNineVariables coreNineVariables_injective] at hbase
  have hdeg : (coreNineBottom c).natDegree = 3 := by
    dsimp [coreNineBottom]
    compute_degree <;> first | exact hnz 8 (by omega) | decide
  exact initialTenBase_distance_seven _ _ _ _ (hnz 9 (by omega))
    (by simpa [coreNineBottom] using hnz 1 (by omega))
    (by simpa [coreNineBottom] using hnz 2 (by omega)) (by omega)
    (by simpa [coreNineMiddle] using hnz 3 (by omega))
    (by simpa [coreNineMiddle] using hnz 6 (by omega))
    (by simpa [coreTenLinear] using hnz 5 (by omega))
    (by simpa [coreTenLinear] using hnz 10 (by omega)) hbase

theorem intervalCore_ten_distance_seven (c : ℕ → K) (hc : NonzeroWeights 10 c) :
    7 ≤ distance (intervalCore 10 c) := by
  rw [intervalCore_ten_rename, distance_rename_of_injective coreTenVariables coreTenVariables_injective]
  exact coreTenTemplate_distance_seven c hc

end WeightedPilz

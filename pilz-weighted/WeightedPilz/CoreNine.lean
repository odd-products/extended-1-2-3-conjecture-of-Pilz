import WeightedPilz.BivariateQuadratic
import WeightedPilz.InitialCore
import WeightedPilz.VariableSlices

/-! The first quadratic core in the initial interval argument. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

def coreNineBottom (c : ℕ → K) : Polynomial K :=
  Polynomial.C (c 1) + Polynomial.C (c 2) * Polynomial.X +
    Polynomial.C (c 4) * Polynomial.X ^ 2 + Polynomial.C (c 8) * Polynomial.X ^ 3

def coreNineMiddle (c : ℕ → K) : Polynomial K :=
  Polynomial.C (c 3) + Polynomial.C (c 6) * Polynomial.X

def coreNineVariables : Option PUnit → ℕ
  | none => 3
  | some _ => 2

theorem coreNineVariables_injective : Function.Injective coreNineVariables := by
  intro a b hab
  cases a <;> cases b <;> simp_all [coreNineVariables]

theorem bivariateQuadratic_coreNine (c : ℕ → K) :
    bivariateQuadratic (coreNineBottom c) (coreNineMiddle c) (Polynomial.C (c 9)) =
      C (c 1) + C (c 2) * X (some ()) + C (c 4) * X (some ()) ^ 2 +
      C (c 8) * X (some ()) ^ 3 +
      (C (c 3) + C (c 6) * X (some ())) * X none + C (c 9) * X none ^ 2 := by
  apply (optionEquivLeft K PUnit).injective
  simp [bivariateQuadratic, coreNineBottom, coreNineMiddle,
    pUnitAlgEquiv_symm_apply, optionEquivLeft_C, optionEquivLeft_X_some,
    optionEquivLeft_X_none]

theorem intervalCore_nine_expansion (c : ℕ → K) :
    intervalCore 9 c =
      C (c 1) + C (c 2) * X 2 + C (c 4) * X 2 ^ 2 + C (c 8) * X 2 ^ 3 +
      (C (c 3) + C (c 6) * X 2) * X 3 + C (c 9) * X 3 ^ 2 := by
  have hset : Finset.Icc 1 9 \ intervalFreshPrimes 9 = {1, 2, 3, 4, 6, 8, 9} := by
    decide
  have h2 : (2 : ℕ).factorization = Finsupp.single 2 1 := Nat.prime_two.factorization
  have h3 : (3 : ℕ).factorization = Finsupp.single 3 1 :=
    (by decide : Nat.Prime 3).factorization
  have h4 : (4 : ℕ).factorization = Finsupp.single 2 2 := by
    simpa using Nat.prime_two.factorization_pow (k := 2)
  have h6 : (6 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 3 1 := by
    change (2 * 3 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h2, h3]
  have h8 : (8 : ℕ).factorization = Finsupp.single 2 3 := by
    simpa using Nat.prime_two.factorization_pow (k := 3)
  have h9 : (9 : ℕ).factorization = Finsupp.single 3 2 := by
    simpa using (by decide : Nat.Prime 3).factorization_pow (k := 2)
  simp [intervalCore, polynomialOf, hset, h2, h3, h4, h6, h8, h9,
    ← C_apply, ← C_mul_X_pow_eq_monomial, monomial_add_single] <;> ring

theorem intervalCore_nine_rename (c : ℕ → K) :
    intervalCore 9 c = rename coreNineVariables
      (bivariateQuadratic (coreNineBottom c) (coreNineMiddle c) (Polynomial.C (c 9))) := by
  rw [bivariateQuadratic_coreNine, intervalCore_nine_expansion]
  simp [coreNineVariables]

theorem intervalCore_nine_distance_four (c : ℕ → K) (hc : NonzeroWeights 9 c) :
    4 ≤ distance (intervalCore 9 c) := by
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 9) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  have hA0 : (coreNineBottom c).coeff 0 ≠ 0 := by
    simpa [coreNineBottom] using hnz 1 (by omega)
  have hA1 : (coreNineBottom c).coeff 1 ≠ 0 := by
    simpa [coreNineBottom] using hnz 2 (by omega)
  have hB : coreNineMiddle c ≠ 0 := by
    intro hz
    have h0 := congrArg (fun P : Polynomial K => P.coeff 0) hz
    exact hnz 3 (by omega) (by simpa [coreNineMiddle] using h0)
  have hD : (Polynomial.C (c 9) : Polynomial K) ≠ 0 := Polynomial.C_ne_zero.mpr (hnz 9 (by omega))
  have hdegA : (coreNineBottom c).natDegree = 3 := by
    dsimp [coreNineBottom]
    compute_degree <;> first | exact hnz 8 (by omega) | decide
  have hdegB : (coreNineMiddle c).natDegree = 1 := by
    dsimp [coreNineMiddle]
    compute_degree <;> first | exact hnz 6 (by omega) | decide
  have h := bivariateQuadratic_distance_four (coreNineBottom c) (coreNineMiddle c)
    (Polynomial.C (c 9)) hA0 hA1 hB hD (by rw [hdegA, hdegB, Polynomial.natDegree_C]; decide)
  rw [intervalCore_nine_rename, distance_rename_of_injective coreNineVariables coreNineVariables_injective]
  exact h

end WeightedPilz

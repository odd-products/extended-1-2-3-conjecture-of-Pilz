import WeightedPilz.CoreNine
import WeightedPilz.BivariatePowerMultiplier

/-! The common quadratic base for the initial intervals twelve through fifteen. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

def coreTwelveMiddle (c : ℕ → K) : Polynomial K :=
  Polynomial.C (c 3) + Polynomial.C (c 6) * Polynomial.X +
    Polynomial.C (c 12) * Polynomial.X ^ 2

def baseTwelve (c : ℕ → K) : Poly K :=
  rename coreNineVariables
    (bivariateQuadratic (coreNineBottom c) (coreTwelveMiddle c) (Polynomial.C (c 9)))

theorem baseTwelve_expansion (c : ℕ → K) :
    baseTwelve c = C (c 1) + C (c 2) * X 2 + C (c 4) * X 2 ^ 2 +
      C (c 8) * X 2 ^ 3 +
      (C (c 3) + C (c 6) * X 2 + C (c 12) * X 2 ^ 2) * X 3 +
      C (c 9) * X 3 ^ 2 := by
  have h : bivariateQuadratic (coreNineBottom c) (coreTwelveMiddle c) (Polynomial.C (c 9)) =
      C (c 1) + C (c 2) * X (some ()) + C (c 4) * X (some ()) ^ 2 +
      C (c 8) * X (some ()) ^ 3 +
      (C (c 3) + C (c 6) * X (some ()) + C (c 12) * X (some ()) ^ 2) * X none +
      C (c 9) * X none ^ 2 := by
    apply (optionEquivLeft K PUnit).injective
    simp [bivariateQuadratic, coreNineBottom, coreTwelveMiddle,
      pUnitAlgEquiv_symm_apply, optionEquivLeft_C, optionEquivLeft_X_some,
      optionEquivLeft_X_none]
  rw [baseTwelve, h]
  simp [coreNineVariables]

theorem baseTwelve_eq_polynomialOf (c : ℕ → K) :
    baseTwelve c = polynomialOf {1, 2, 3, 4, 6, 8, 9, 12} c := by
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
  have h12 : (12 : ℕ).factorization = Finsupp.single 2 2 + Finsupp.single 3 1 := by
    change (4 * 3 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), h4, h3]
  rw [baseTwelve_expansion]
  simp [polynomialOf, h2, h3, h4, h6, h8, h9, h12,
    ← C_apply, ← C_mul_X_pow_eq_monomial, monomial_add_single] <;> ring

theorem baseTwelve_weight (c : ℕ → K) (hc : NonzeroWeights 12 c) :
    weight (baseTwelve c) = 8 := by
  rw [baseTwelve_eq_polynomialOf, weight_polynomialOf]
  · decide
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    omega
  · intro a ha
    apply hc a
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    exact Finset.mem_Icc.mpr (by omega)

theorem baseTwelve_distance_four (c : ℕ → K) (hc : NonzeroWeights 12 c) :
    4 ≤ distance (baseTwelve c) := by
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 12) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  have hA0 : (coreNineBottom c).coeff 0 ≠ 0 := by
    simpa [coreNineBottom] using hnz 1 (by omega)
  have hA1 : (coreNineBottom c).coeff 1 ≠ 0 := by
    simpa [coreNineBottom] using hnz 2 (by omega)
  have hB : coreTwelveMiddle c ≠ 0 := by
    intro hz
    have h0 := congrArg (fun P : Polynomial K => P.coeff 0) hz
    exact hnz 3 (by omega) (by simpa [coreTwelveMiddle] using h0)
  have hD : (Polynomial.C (c 9) : Polynomial K) ≠ 0 := Polynomial.C_ne_zero.mpr (hnz 9 (by omega))
  have hdegA : (coreNineBottom c).natDegree = 3 := by
    dsimp [coreNineBottom]
    compute_degree <;> first | exact hnz 8 (by omega) | decide
  have hdegB : (coreTwelveMiddle c).natDegree = 2 := by
    dsimp [coreTwelveMiddle]
    compute_degree <;> first | exact hnz 12 (by omega) | decide
  have h := bivariateQuadratic_distance_four (coreNineBottom c) (coreTwelveMiddle c)
    (Polynomial.C (c 9)) hA0 hA1 hB hD (by rw [hdegA, hdegB, Polynomial.natDegree_C]; decide)
  rw [baseTwelve, distance_rename_of_injective coreNineVariables coreNineVariables_injective]
  exact h

theorem coreTwelveMiddle_support_card (c : ℕ → K) (hc : NonzeroWeights 12 c) :
    (coreTwelveMiddle c).support.card = 3 := by
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 12) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  have hs : (coreTwelveMiddle c).support = {0, 1, 2} := by
    ext i
    simp only [Polynomial.mem_support_iff, Finset.mem_insert, Finset.mem_singleton]
    by_cases hi0 : i = 0
    · subst i; simp [coreTwelveMiddle, hnz 3 (by omega)]
    by_cases hi1 : i = 1
    · subst i; simp [coreTwelveMiddle, hnz 6 (by omega)]
    by_cases hi2 : i = 2
    · subst i; simp [coreTwelveMiddle, hnz 12 (by omega)]
    simp [coreTwelveMiddle, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_C_mul_X_pow,
      hi0, hi1, hi2, Ne.symm hi0, Ne.symm hi1, Ne.symm hi2]
  rw [hs]
  decide

theorem baseTwelve_power_seven (c : ℕ → K) (hc : NonzeroWeights 12 c)
    {n : ℕ} (hn : 0 < n) : 7 ≤ weight (baseTwelve c ^ n) := by
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 12) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  have hdegA : (coreNineBottom c).natDegree = 3 := by
    dsimp [coreNineBottom]
    compute_degree <;> first | exact hnz 8 (by omega) | decide
  have h := bivariateQuadratic_constant_power (coreNineBottom c) (coreTwelveMiddle c)
    (c 9) (hnz 9 (by omega))
    (by simpa [coreNineBottom] using hnz 1 (by omega))
    (by simpa [coreNineBottom] using hnz 2 (by omega)) (by omega) hn
  rw [coreTwelveMiddle_support_card c hc] at h
  rw [baseTwelve, ← map_pow,
    weight_rename_of_injective coreNineVariables coreNineVariables_injective]
  exact h

theorem baseTwelve_power_mul_six (c : ℕ → K) (hc : NonzeroWeights 12 c)
    (M : Poly K) (hM : M ≠ 0) (hvars : (M.vars : Set ℕ) ⊆ {2})
    {n : ℕ} (hn : 0 < n) : 6 ≤ weight (baseTwelve c ^ n * M) := by
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 12) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  let f : PUnit.{1} → ℕ := fun _ => 2
  have hf : Function.Injective f := fun _ _ _ => Subsingleton.elim _ _
  have hvars' : (M.vars : Set ℕ) ⊆ Set.range f := by
    intro z hz
    have hz2 : z = 2 := hvars hz
    exact ⟨(), hz2.symm⟩
  obtain ⟨M₀, hM₀⟩ := exists_rename_eq_of_vars_subset_range M f hf hvars'
  have hM₀ne : M₀ ≠ 0 := by
    intro hz
    apply hM
    rw [← hM₀, hz, map_zero]
  have hrename : rename f M₀ = rename coreNineVariables (rename some M₀) := by
    rw [rename_rename]
    rfl
  have hdegA : (coreNineBottom c).natDegree = 3 := by
    dsimp [coreNineBottom]
    compute_degree <;> first | exact hnz 8 (by omega) | decide
  have h := bivariateQuadratic_constant_power_mul (coreNineBottom c) (coreTwelveMiddle c)
    (c 9) (hnz 9 (by omega))
    (by simpa [coreNineBottom] using hnz 1 (by omega))
    (by simpa [coreNineBottom] using hnz 2 (by omega)) (by omega)
    (by simpa [coreTwelveMiddle] using hnz 3 (by omega))
    (by simpa [coreTwelveMiddle] using hnz 6 (by omega)) M₀ hM₀ne hn
  rw [baseTwelve, ← hM₀, hrename, ← map_pow, ← map_mul,
    weight_rename_of_injective coreNineVariables coreNineVariables_injective]
  exact h

end WeightedPilz

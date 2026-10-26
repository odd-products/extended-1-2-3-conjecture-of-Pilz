import WeightedPilz.CoreTwelve
import WeightedPilz.InitialSixteenBase
import WeightedPilz.InitialLateBases
import WeightedPilz.TwelveCoreDecomposition

/-! The exceptional quadratic base in the sixteenth interval. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

def baseSixteen (c : ℕ → K) : Poly K := baseTwelve c + C (c 16) * X 2 ^ 4

theorem baseSixteen_rename (c : ℕ → K) :
    baseSixteen c = rename coreNineVariables
      (bivariateQuadratic (lateBaseBottom c) (coreTwelveMiddle c) (Polynomial.C (c 9))) := by
  have h : bivariateQuadratic (lateBaseBottom c) (coreTwelveMiddle c) (Polynomial.C (c 9)) =
      bivariateQuadratic (coreNineBottom c) (coreTwelveMiddle c) (Polynomial.C (c 9)) +
        C (c 16) * X (some ()) ^ 4 := by
    apply (optionEquivLeft K PUnit).injective
    simp [bivariateQuadratic, lateBaseBottom, coreNineBottom, coreTwelveMiddle,
      pUnitAlgEquiv_symm_apply, optionEquivLeft_C, optionEquivLeft_X_some,
      optionEquivLeft_X_none] <;> ring
  rw [h]
  simp [baseSixteen, baseTwelve, coreNineVariables]

theorem baseSixteen_distance_four (c : ℕ → K) (hc : NonzeroWeights 16 c) :
    4 ≤ distance (baseSixteen c) := by
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 16) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  have hBdeg : (coreTwelveMiddle c).natDegree = 2 := by
    dsimp [coreTwelveMiddle]
    compute_degree <;> first | exact hnz 12 (by omega) | decide
  rw [baseSixteen_rename, distance_rename_of_injective coreNineVariables coreNineVariables_injective]
  apply initial_sixteen_base_distance
  · simpa [lateBaseBottom, coreNineBottom] using hnz 1 (by omega)
  · simpa [lateBaseBottom, coreNineBottom] using hnz 2 (by omega)
  · simpa [coreTwelveMiddle] using hnz 3 (by omega)
  · simpa [coreTwelveMiddle] using hnz 6 (by omega)
  · omega
  · exact hnz 9 (by omega)

theorem baseSixteen_power_seven (c : ℕ → K) (hc : NonzeroWeights 16 c)
    {n : ℕ} (hn : 0 < n) : 7 ≤ weight (baseSixteen c ^ n) := by
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 16) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  have hc12 : NonzeroWeights 12 c := by
    intro a ha
    exact hnz a (by have := Finset.mem_Icc.mp ha; omega)
  have h := bivariateQuadratic_constant_power (lateBaseBottom c) (coreTwelveMiddle c) (c 9)
    (hnz 9 (by omega))
    (by simpa [lateBaseBottom, coreNineBottom] using hnz 1 (by omega))
    (by simpa [lateBaseBottom, coreNineBottom] using hnz 2 (by omega))
    (by rw [lateBaseBottom_natDegree c (hnz 16 (by omega))]; decide) hn
  rw [coreTwelveMiddle_support_card c hc12] at h
  rw [baseSixteen_rename, ← map_pow,
    weight_rename_of_injective coreNineVariables coreNineVariables_injective]
  exact h

theorem baseSixteen_power_mul_six (c : ℕ → K) (hc : NonzeroWeights 16 c)
    (M : Poly K) (hM : M ≠ 0) (hvars : (M.vars : Set ℕ) ⊆ {2})
    {n : ℕ} (hn : 0 < n) : 6 ≤ weight (baseSixteen c ^ n * M) := by
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 16) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
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
  have h := bivariateQuadratic_constant_power_mul (lateBaseBottom c) (coreTwelveMiddle c)
    (c 9) (hnz 9 (by omega))
    (by simpa [lateBaseBottom, coreNineBottom] using hnz 1 (by omega))
    (by simpa [lateBaseBottom, coreNineBottom] using hnz 2 (by omega))
    (by rw [lateBaseBottom_natDegree c (hnz 16 (by omega))]; decide)
    (by simpa [coreTwelveMiddle] using hnz 3 (by omega))
    (by simpa [coreTwelveMiddle] using hnz 6 (by omega)) M₀ hM₀ne hn
  rw [baseSixteen_rename, ← hM₀, hrename, ← map_pow, ← map_mul,
    weight_rename_of_injective coreNineVariables coreNineVariables_injective]
  exact h

theorem intervalCore_sixteen_decomposition (c : ℕ → K) :
    intervalCore 16 c =
      (baseSixteen c + arithmeticFiveRow c * X 5) + arithmeticBinomial 7 c * X 7 := by
  have hset : Finset.Icc 1 16 \ intervalFreshPrimes 16 =
      insert 16 (Finset.Icc 1 15 \ intervalFreshPrimes 15) := by decide
  have hnot : 16 ∉ Finset.Icc 1 15 \ intervalFreshPrimes 15 := by decide
  have h16 : (16 : ℕ).factorization = Finsupp.single 2 4 := by
    simpa using Nat.prime_two.factorization_pow (k := 4)
  rw [intervalCore, polynomialOf, hset, Finset.sum_insert hnot]
  change monomial (16 : ℕ).factorization (c 16) + intervalCore 15 c = _
  rw [intervalCore_fifteen_decomposition, h16, baseSixteen]
  simp only [← C_mul_X_pow_eq_monomial]
  ring

end WeightedPilz

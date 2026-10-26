import WeightedPilz.TwelveCoreDecomposition
import WeightedPilz.InitialTenBase
import WeightedPilz.LinearExtensionOps
import WeightedPilz.CoreOverlap
import WeightedPilz.InitialCoreBinomial
import WeightedPilz.ShortFreshTest
import WeightedPilz.Initial

/-! The weighted twelfth interval and its prime successor. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

def coreTwelveFive (c : ℕ → K) : Polynomial K :=
  Polynomial.C (c 5) + Polynomial.C (c 10) * Polynomial.X

def coreTwelveVariables : Option (Option PUnit.{1}) → ℕ
  | none => 5
  | some a => coreNineVariables a

theorem coreTwelveVariables_injective : Function.Injective coreTwelveVariables := by
  intro a b hab
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases b <;> simp [coreTwelveVariables, coreNineVariables] at hab
  | some a => cases b with
    | none => cases a <;> simp [coreTwelveVariables, coreNineVariables] at hab
    | some b => exact congrArg some (coreNineVariables_injective hab)

theorem initialTenBase_eq_linearExtension (A B D : Polynomial K) (d : K) :
    initialTenBase A B D d = linearExtension (bivariateQuadratic A B (Polynomial.C d))
      (rename some ((pUnitAlgEquiv.{_, 0} K).symm D)) := by
  rw [linearExtension_eq_symm]
  rfl

theorem intervalCore_twelve_rename (c : ℕ → K) :
    intervalCore 12 c = rename coreTwelveVariables
      (initialTenBase (coreNineBottom c) (coreTwelveMiddle c) (coreTwelveFive c) (c 9)) := by
  rw [intervalCore_twelve_decomposition 12 (by decide) (by decide),
    initialTenBase_eq_linearExtension]
  simp only [linearExtension, map_add, map_mul, rename_X, rename_rename]
  change baseTwelve c + arithmeticBinomial 5 c * X 5 =
    baseTwelve c + rename (coreTwelveVariables ∘ some ∘ some)
      ((pUnitAlgEquiv.{_, 0} K).symm (coreTwelveFive c)) * X 5
  congr 2
  simp [arithmeticBinomial, coreTwelveFive, pUnitAlgEquiv_symm_apply,
    coreTwelveVariables, coreNineVariables]

theorem intervalCore_twelve_distance_seven (c : ℕ → K) (hc : NonzeroWeights 12 c) :
    7 ≤ distance (intervalCore 12 c) := by
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 12) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  have hbase := baseTwelve_distance_four c hc
  rw [baseTwelve, distance_rename_of_injective coreNineVariables coreNineVariables_injective] at hbase
  have hdegA : (coreNineBottom c).natDegree = 3 := by
    dsimp [coreNineBottom]
    compute_degree <;> first | exact hnz 8 (by omega) | decide
  have h := initialTenBase_distance_seven (coreNineBottom c) (coreTwelveMiddle c)
    (coreTwelveFive c) (c 9) (hnz 9 (by omega))
    (by simpa [coreNineBottom] using hnz 1 (by omega))
    (by simpa [coreNineBottom] using hnz 2 (by omega)) (by omega)
    (by simpa [coreTwelveMiddle] using hnz 3 (by omega))
    (by simpa [coreTwelveMiddle] using hnz 6 (by omega))
    (by simpa [coreTwelveFive] using hnz 5 (by omega))
    (by simpa [coreTwelveFive] using hnz 10 (by omega)) hbase
  rw [intervalCore_twelve_rename,
    distance_rename_of_injective coreTwelveVariables coreTwelveVariables_injective]
  exact h

theorem intervalCore_twelve_power_nine (c : ℕ → K) (hc : NonzeroWeights 12 c)
    {n : ℕ} (hn : 0 < n) : 9 ≤ weight (intervalCore 12 c ^ n) := by
  let A := bivariateQuadratic (coreNineBottom c) (coreTwelveMiddle c) (Polynomial.C (c 9))
  let D := rename some ((pUnitAlgEquiv.{_, 0} K).symm (coreTwelveFive c))
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 12) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  have hAd : 7 ≤ weight (A ^ n) := by
    have h := baseTwelve_power_seven c hc hn
    rwa [baseTwelve, ← map_pow,
      weight_rename_of_injective coreNineVariables coreNineVariables_injective] at h
  have hDd : 2 ≤ distance D := by
    rw [distance_rename_of_injective some (Option.some_injective _)]
    apply distance_pUnit_symm_two
    · simpa [coreTwelveFive] using hnz 5 (by omega)
    · simpa [coreTwelveFive] using hnz 10 (by omega)
  have hD : D ≠ 0 := by intro hz; simp [hz, distance_zero] at hDd
  have hDp : 2 ≤ weight (D ^ n) := by
    have h := hDd.trans (distance_le_weight_mul D (D ^ (n - 1)) (pow_ne_zero _ hD))
    rwa [← pow_succ', Nat.sub_add_cancel hn] at h
  have hsum := linearExtension_power_endpoints A D hD hn
  rw [intervalCore_twelve_rename, ← map_pow,
    weight_rename_of_injective coreTwelveVariables coreTwelveVariables_injective,
    initialTenBase_eq_linearExtension]
  change 9 ≤ weight (linearExtension A D ^ n)
  omega

theorem intervalBound_twelve (c : ℕ → K) (hc : NonzeroWeights 12 c) : IntervalBound 12 c := by
  have hr : (intervalFreshPrimes 12).Nonempty := by decide
  let S := intervalFreshData 12 c (by decide) hc hr
  have hvars : S.vars.card = 2 := by change (intervalFreshPrimes 12).card = 2; decide
  have hcore : S.C = intervalCore 12 c := rfl
  have hw : weight S.C = 10 := by rw [hcore, weight_intervalCore 12 c hc]; decide
  have hd : 7 ≤ distance S.C := by rw [hcore]; exact intervalCore_twelve_distance_seven c hc
  have h := S.short_fresh_test (ringExpChar K) 7 (by omega) hd (by omega) (by omega)
    (by
      intro j hj hnd hcost
      have hrow := S.fresh_nondistinguished_degree_cost (ringExpChar K) hj hnd
      rw [hvars] at hrow
      have hpow := intervalCore_twelve_power_nine c hc hj
      rw [hw, hvars, hcore]
      omega)
    (by
      intro e H hH
      have hbin := intervalCore_initial_distinguished_binomial_budget
        (ringExpChar K) e 12 (by omega) c hc H hH
      have hfc : Pilz.freshCount 12 = 2 := by decide
      rw [hfc] at hbin
      rw [hw, hvars, hcore]
      exact hbin)
    (by
      intro e f M L hef hM hL hne
      have htwo := intervalCore_unequal_distinguished_sum_bound 12 3 (ringExpChar K) e f c hc
        (by decide) M L hef hM hL
      have hweight : weight (intervalCore 12 c) = 10 := by rw [← hcore]; exact hw
      rw [hweight] at htwo
      rw [hw, hvars, hcore]
      omega)
  rw [hw, hvars] at h
  have heq := distance_interval_eq_freshData 12 c (by decide) hc hr
  change distance (interval 12 c) = distance S.F at heq
  rw [← heq] at h
  exact (le_distance_iff _ 12).mp h

theorem intervalBound_thirteen (c : ℕ → K) (hc : NonzeroWeights 13 c) : IntervalBound 13 c := by
  have hc12 : NonzeroWeights 12 c := by
    intro a ha
    exact hc a (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1, by
      have := (Finset.mem_Icc.mp ha).2
      omega⟩)
  exact intervalBound_prime_successor 12 c (by decide) hc (intervalBound_twelve c hc12)

end WeightedPilz

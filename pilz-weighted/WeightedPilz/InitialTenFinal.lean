import WeightedPilz.OneFreshShortTest
import WeightedPilz.CoreTenTwoPowers
import WeightedPilz.Initial

/-! The tenth and eleventh weighted intervals from the one-fresh-variable test. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

private def intervalTenVariables : Option (Option (Option PUnit.{1})) → ℕ
  | none => 7
  | some q => coreTenVariables q

private theorem intervalTenVariables_injective : Function.Injective intervalTenVariables := by
  have hn (q : Option (Option PUnit.{1})) : coreTenVariables q ≠ 7 := by
    cases q with
    | none => decide
    | some q => cases q <;> norm_num [coreTenVariables]
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => exact False.elim (hn b hab.symm)
  | some a =>
    cases b with
    | none => exact False.elim (hn a hab)
    | some b => exact congrArg some (coreTenVariables_injective hab)

private theorem intervalTen_completion_rename (c : ℕ → K) :
    rename intervalTenVariables (freshCompletion (coreTenTemplate c)) =
      intervalCore 10 c + X 7 := by
  simp only [freshCompletion, map_add, rename_rename, rename_X]
  change rename coreTenVariables (coreTenTemplate c) + X 7 = _
  rw [← intervalCore_ten_rename]

theorem intervalBound_ten (c : ℕ → K) (hc : NonzeroWeights 10 c) : IntervalBound 10 c := by
  have h := freshCompletion_distance_ten (coreTenTemplate c)
    (coreTenTemplate_distance_seven c hc)
    (fun j hj => coreTenTemplate_power_nine c hc hj)
    (fun j hj B hB => coreTenTemplate_power_binomial_eight c hc hj B hB)
    (by
      intro i j hi hij M N hM hN hne
      exact coreTenTemplate_two_powers_eight c hc M N hM hN hi hij hne)
  have hrename := distance_rename_of_injective intervalTenVariables
    intervalTenVariables_injective (freshCompletion (coreTenTemplate c))
  rw [intervalTen_completion_rename] at hrename
  have hinterval : distance (interval 10 c) = distance (intervalCore 10 c + X 7) := by
    rw [← distance_rescale (intervalFreshNormalization 10 c hc) (interval 10 c),
      rescale_interval_eq_core_add_fresh]
    simp only [show intervalFreshPrimes 10 = {7} by decide, Finset.sum_singleton]
  apply (le_distance_iff _ 10).mp
  rwa [hinterval, hrename]

theorem intervalBound_eleven (c : ℕ → K) (hc : NonzeroWeights 11 c) : IntervalBound 11 c := by
  have hc10 : NonzeroWeights 10 c := by
    intro a ha
    exact hc a (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1,
      (Finset.mem_Icc.mp ha).2.trans (by decide)⟩)
  exact intervalBound_prime_successor 10 c (by decide) hc (intervalBound_ten c hc10)

end WeightedPilz

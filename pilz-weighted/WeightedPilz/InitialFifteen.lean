import WeightedPilz.InitialFifteenCores
import WeightedPilz.InitialCoreBinomial
import WeightedPilz.CoreOverlap

/-! The weighted fifteenth interval. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem intervalBound_fifteen (c : ℕ → K) (hc : NonzeroWeights 15 c) : IntervalBound 15 c := by
  have hr : (intervalFreshPrimes 15).Nonempty := by decide
  let S := intervalFreshData 15 c (by decide) hc hr
  have hvars : S.vars.card = 2 := by change (intervalFreshPrimes 15).card = 2; decide
  have hcore : S.C = intervalCore 15 c := rfl
  have hw : weight S.C = 13 := by rw [hcore, weight_intervalCore 15 c hc]; decide
  have hd : 10 ≤ distance S.C := by rw [hcore]; exact intervalCore_fifteen_distance_ten c hc
  have h := S.short_fresh_test (ringExpChar K) 10 (by omega) hd (by omega) (by omega)
    (by
      intro j hj hnd hcost
      have hpow := intervalCore_fifteen_nondistinguished_power_sixteen c hc (ringExpChar K) hj hnd
      rw [hw, hvars, hcore]
      omega)
    (by
      intro e H hH
      have hbin := intervalCore_initial_distinguished_binomial_budget
        (ringExpChar K) e 15 (by omega) c hc H hH
      have hfc : Pilz.freshCount 15 = 2 := by decide
      rw [hfc] at hbin
      rw [hw, hvars, hcore]
      exact hbin)
    (by
      intro e f M L hef hM hL hne
      have htwo := intervalCore_unequal_distinguished_sum_bound 15 3 (ringExpChar K) e f c hc
        (by decide) M L hef hM hL
      have hweight : weight (intervalCore 15 c) = 13 := by rw [← hcore]; exact hw
      rw [hweight] at htwo
      rw [hw, hvars, hcore]
      omega)
  rw [hw, hvars] at h
  have heq := distance_interval_eq_freshData 15 c (by decide) hc hr
  change distance (interval 15 c) = distance S.F at heq
  rw [← heq] at h
  exact (le_distance_iff _ 15).mp h

end WeightedPilz
